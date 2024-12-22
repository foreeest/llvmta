////////////////////////////////////////////////////////////////////////////////
//
//   LLVMTA - Timing Analyser performing worst-case execution time analysis
//     using the LLVM backend intermediate representation
//
// Copyright (C) 2013-2022  Saarland University
// Copyright (C) 2014-2015  Claus Faymonville
//
// This file is distributed under the Saarland University Software Release
// License. See LICENSE.TXT for details.
//
// THIS SOFTWARE IS PROVIDED "AS IS", WITHOUT ANY EXPRESSED OR IMPLIED
// WARRANTIES, INCLUDING BUT NOT LIMITED TO, THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE SAARLAND UNIVERSITY, THE
// CONTRIBUTORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DIRECT,
// INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
// (INCLUDING BUT NOT LIMITED TO PROCUREMENT OF SUBSTITUTE GOODS OR
// SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
// HOWEVER CAUSED OR OTHER LIABILITY, WHETHER IN CONTRACT, STRICT
// LIABILITY, TORT OR OTHERWISE, ARISING IN ANY WAY FROM, OUT OF OR IN
// CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS WITH THE
// SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH A DAMAGE.
//
////////////////////////////////////////////////////////////////////////////////

#include "LLVMPasses/TimingAnalysisMain.h"
#include "AnalysisFramework/AnalysisDriver.h"
#include "AnalysisFramework/AnalysisResults.h"
#include "AnalysisFramework/CallGraph.h"
#include "LLVMPasses/DispatchFixedLatency.h"
#include "LLVMPasses/DispatchInOrderPipeline.h"
#include "LLVMPasses/DispatchMemory.h"
#include "LLVMPasses/DispatchOutOfOrderPipeline.h"
#include "LLVMPasses/DispatchPretPipeline.h"
#include "LLVMPasses/MachineFunctionCollector.h"
#include "Memory/PersistenceScopeInfo.h"
#include "PartitionUtil/DirectiveHeuristics.h"
#include "PathAnalysis/LoopBoundInfo.h"
#include "PreprocessingAnalysis/AddressInformation.h"
#include "PreprocessingAnalysis/ConstantValueDomain.h"
#include "Util/GlobalVars.h"
#include "Util/Options.h"
#include "Util/Statistics.h"
#include "Util/Util.h"
#include "Util/muticoreinfo.h"

#include "llvm/ADT/Optional.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/Passes.h"
#include "llvm/DebugInfo/Symbolize/SymbolizableModule.h"
#include "llvm/Support/Format.h"

#include "llvm/Support/JSON.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"

#include <Util/StatisticOutput.h>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <fstream>
#include <limits>
#include <list>
#include <map>
#include <queue>
#include <sstream>
#include <string>
#include <system_error>
#include <type_traits>
#include <utility>

using namespace llvm;
using namespace std;

namespace TimingAnalysisPass {

TimingAnalysisMain **MultiCorePasses = nullptr;

unsigned getInitialStackPointer() { return InitialStackPointer; }

unsigned getInitialLinkRegister() { return InitialLinkRegister; }

MachineFunction *getAnalysisEntryPoint() {
  auto *Res = machineFunctionCollector->getFunctionByName(AnalysisEntryPoint);
  assert(Res && "Invalid entry point specified");
  return Res;
}

char TimingAnalysisMain::ID = 0;
TargetMachine *TimingAnalysisMain::TargetMachineInstance = nullptr;

TimingAnalysisMain::TimingAnalysisMain(TargetMachine &TM)
    : MachineFunctionPass(ID) {
  TargetMachineInstance = &TM;
}

TargetMachine &TimingAnalysisMain::getTargetMachine() {
  return *TargetMachineInstance;
}

bool TimingAnalysisMain::runOnMachineFunction(MachineFunction &MF) {
  bool Changed = false;
  return Changed;
}

void TimingAnalysisMain::parseCoreInfo(const std::string &fileName) {
  // TODO
  mcif.setSize(CoreNums.getValue());
  auto jsonfile = MemoryBuffer::getFile(fileName, true);
  if (!jsonfile) {
    fprintf(stderr, "Unable to open file %s, exit.", fileName.c_str());
    exit(1);
  }
  auto jsondata = json::parse(jsonfile.get()->getBuffer());
  if (!jsondata) {
    fprintf(stderr, "Unable to parse json file %s, exit.", fileName.c_str());
    exit(1);
  }

  json::Array *cores = jsondata->getAsArray();
  if (!cores) {
    fprintf(stderr, "File(%s) should be an array of cores, exit.",
            fileName.c_str());
    exit(1);
  }
  for (json::Value &e : *cores) {
    json::Object *obj = e.getAsObject();
    if (!obj) {
      fprintf(stderr, "Core info(%s) shoule be an object, exit.",
              fileName.c_str());
      exit(1);
    }
    int64_t core = obj->getInteger("core").getValue(); // core号，从0开始计算

    json::Array *functions = obj->getArray("tasks");
    if (!functions) {
      fprintf(stderr, "Unable to get tasks for core %lu, exit.", core);
      exit(1);
    }

    for (json::Value &task : *functions) {
      bool has_deadline = false, has_period = false;
      auto taskName = task.getAsObject()->get("function")->getAsString();
      if (task.getAsObject()->get("deadline")) { // 这两啥意思？
        has_deadline = true;
      }
      if (task.getAsObject()->get("period")) {
        has_period = true;
      }
      llvm::Optional<int64_t> deadline(-1), period(-1);
      if (has_deadline)
        deadline = task.getAsObject()->get("deadline")->getAsInteger();
      if (has_period)
        period = task.getAsObject()->get("period")->getAsInteger();
      if (!taskName) {
        fprintf(stderr, "Unable to get task name for core %lu, exit.", core);
        exit(1);
      }
      // if (!deadline) {
      //   fprintf(stderr, "Unable to get deadline for core %lu, exit.", core);
      //   exit(1);
      // }
      // if (!period) {
      //   fprintf(stderr, "Unable to get period for core %lu, exit.", core);
      //   exit(1);
      // }
      mp[core].push(taskName.getValue().str());
      this->deadFunctionMap[taskName.getValue().str()] = deadline.getValue();
      this->periodFunctionMap[taskName.getValue().str()] = period.getValue();
      // NOTICE: blabla
      mcif.addTask(core, taskName.getValue().str());
    }
  }
}

boost::optional<std::string>
TimingAnalysisMain::getNextFunction(unsigned int core) {
  auto it = mp.find(core);

  if (it == mp.end()) {
    return boost::none;
  }

  if (it->second.empty())
    return boost::none;

  std::string functionName = it->second.front();
  it->second.pop();

  return functionName;
}

/* main函数 */
bool TimingAnalysisMain::doFinalization(Module &M) {
  // do File parsing
  parseCoreInfo(coreInfo);
  ::ModulePtr = &M;

  ofstream Myfile;

  // Default analysis type: timing
  if (AnaType.getBits() == 0) {
    AnaType.addValue(AnalysisType::TIMING);
  }

  // 这两行应该就是个代码运行计时的
  Statistics &Stats = Statistics::getInstance();
  Stats.startMeasurement("Complete Analysis");

  if (CoRunnerSensitive) { // 这也是命令行参数
    for (int I = 0; I <= UntilIterationMeasurement; ++I) {
      std::string MeasurementId = "Until Iteration ";
      MeasurementId += std::to_string(I);
      Stats.startMeasurement(MeasurementId); // 也是个计时
    }
  }

  if (OutputExtFuncAnnotationFile) { // 外部调用
    Myfile.open("ExtFuncAnnotations.csv", ios_base::trunc);
    CallGraph::getGraph().dumpUnknownExternalFunctions(Myfile);
    // dump的含义就是输出结果？
    Myfile.close();
    return false;
  }

  if (!QuietMode) {
    Myfile.open("AnnotatedHeuristics.txt", ios_base::trunc);
    DirectiveHeuristicsPassInstance->dump(Myfile);
    Myfile.close();

    // jjy: I put this back, after we know the function name that we ananysis
    // Myfile.open("PersistenceScopes.txt", ios_base::trunc);
    // PersistenceScopeInfo::getInfo().dump(Myfile);
    // Myfile.close();

    Myfile.open("CallGraph.txt", ios_base::trunc);
    CallGraph::getGraph().dump(Myfile);
    Myfile.close();
  }

  VERBOSE_PRINT(" -> Finished Preprocessing Phase\n"); // 这在哪完成运算的？在Pass，这应该已经算完了
  // Init the output infos
  int64_t task_id = 0;
  // llvm::json::Array arr;
  llvm::json::Object result{
      {{"system", llvm::json::Object{{"core_count", CoreNums.getValue()}}},
       {"tasks", llvm::json::Array()}}};

  std::map<std::string, size_t> vec;

  auto &manager = StatisticOutputManager::getInstance();
  // auto &output_data = manager.insert(
  //     "Summary", StatisticOutput("Summary", "Function Name", COL_LEN));

  // 进行UR和CEOP的获取
  for (unsigned i = 0; i < CoreNums; ++i) {
    outs() << "UR Analysis for core: " << i; 
    Core = i;
    for (std::string &functionName : mcif.coreinfo[i]) {
      outs() << " entry point: " << functionName << '\n';
      mcif.URCalculation(i, functionName);
    }
  }

  // 各单核分别分析
  StatisticOutput output_data =
    StatisticOutput("Summary", "Function Name", COL_LEN);
    
  outs() << "WCET Intra Analysis start";
  for (unsigned i = 0; i < CoreNums; ++i) {
    outs() << "Timing Analysis for core: " << i; // 输出到终端
    Core = i; // 全局变量，控制当前分析的哪个单核
    for (std::string &functionName : mcif.coreinfo[i]) { // multicore-info
      outs() << " entry point: " << functionName << '\n';
      AnalysisEntryPoint = functionName;
      if (!QuietMode) {
        // 持久域收集
        Myfile.open("PersistenceScopes.txt", ios_base::trunc);
        PersistenceScopeInfo::getInfo().dump(Myfile);
        Myfile.close();
      }
      // Dispatch the value analysis
      auto Arch = getTargetMachine().getTargetTriple().getArch();
      if (Arch == Triple::ArchType::arm) {
        dispatchValueAnalysis<Triple::ArchType::arm>(); // 这里就完成单核分析
        // pair of 2 u
        // ETchage = 
        //     ETchage || mcif.updateTaskTime(Core, AnalysisEntryPoint,
        //                                     this->BCETtime, this->WCETtime); // B\W是全局
            // 所以说目前一轮n核，每个核算完一次，冲突集都可能变化，而非轮内冲突集不变
      } else if (Arch == Triple::ArchType::riscv32) {
        dispatchValueAnalysis<Triple::ArchType::riscv32>();
        // ETchage =
        //     ETchage || mcif.updateTaskTime(Core, AnalysisEntryPoint,
        //                                     this->BCETtime, this->WCETtime);
      } else {
        assert(0 && "Unsupported ISA for LLVMTA");
      }
      mcif.intraBWtime[Core][AnalysisEntryPoint] = std::make_pair(this->BCETtime,
        this->WCETtime); // 单核分析结果

      // jjy:收集各个Task的WCET信息
      // if (vec.count(functionName) == 0) {
      //   llvm::json::Object obj{
      //       //  {"BCET", this->BCETtime}
      //       {"id", task_id++},
      //       {"partition", i},
      //       {"WCET", this->WCETtime},
      //       {"deadline", this->deadFunctionMap[functionName]},
      //       {"period", this->periodFunctionMap[functionName]},
      //       {"function", functionName},
      //   };
      //   auto *arr = result["tasks"].getAsArray();
      //   arr->push_back(std::move(obj));
      //   vec[functionName] = arr->size() - 1;
      // } else {
      //   auto *arr = result["tasks"].getAsArray();
      //   auto *ptr = (*arr)[vec[functionName]].getAsObject();
      //   (*ptr)["WCET"] = this->WCETtime;
      //   // (*ptr)["BCET"] = this->BCETtime;
      // }

      // output_data.update(functionName, "BCET", this->BCETtime);
      // output_data.update(functionName, "WCET", this->WCETtime);
      // output_data.update(functionName, "I-MISS", IMISS);
      // output_data.update(functionName, "D-MISS", DMISS);
      // output_data.update(functionName, "L2-MISS", L2MISS);
      // IMISS = 0, DMISS = 0, L2MISS = 0; // 全局变量
    }
    outs() << " No next analyse point for this core.\n";
  }

  // 现在先无脑全部Task都冲突，即不实现生命周期迭代
  outs() << "WCET Inter Analysis start";
  for (unsigned local = 0; local < CoreNums; ++local) {
    for (std::string &localFunc : mcif.coreinfo[local]){
      // 选出本地task
      unsigned wceetOfTSum = 0;
      for (unsigned inter = 0; inter < CoreNums; ++inter) { // interference
        if (local==inter) continue;
        for (std::string &interFunc : mcif.getInitConflictFunction(local, localFunc)){
          // 要考虑函数可能执行多次，这里默认getInitConflictFunction会多次返回
          // 选出冲突task
          unsigned wceetOf2T = 0; // 两个Task之间的WCEET
          for (const CEOP &localP : mcif.CEOPs[local][localFunc]){
            for (const CEOP &interP : mcif.CEOPs[inter][interFunc]){
              // 选出两条Path, 开始dp，横干扰、竖本地
              unsigned localPLen = localP.URs.size();
              unsigned interPLen = interP.URs.size();
              unsigned ArvVal[localPLen][interPLen] = {0};

              for(unsigned i=1;i<localPLen;i++){
                ArvVal[i][0] = mcif.getFValue(local, localP, i, inter, interP, 0) 
                  + ArvVal[i-1][0]; // 感觉paper公式有问题，改成累加
              }
              for(unsigned i=1;i<interPLen;i++){
                ArvVal[0][i] = mcif.getFValue(local, localP, 0, inter, interP, i)
                  + ArvVal[0][i-1];
              }
              for(unsigned i=1;i<localPLen;i++){
                for(unsigned j=1;j<interPLen;j++){
                  ArvVal[i][j] = max(ArvVal[i-1][j], ArvVal[i][j-1]) 
                    + mcif.getFValue(local, localP, i, inter, interP, j);
                }
              }
              wceetOf2T = max(wceetOf2T, ArvVal[localPLen-1][interPLen]);
            }
          }
          wceetOf2T *= Latency; // BG Mem的延迟值 from Command Line, 但感觉很容易重名
          wceetOfTSum += wceetOf2T; // 不同核所有冲突的函数都加上
        }
      }
      mcif.currWcetInter[local][localFunc] = wceetOfTSum;
    }
  }

  // std::ofstream myfile;
  // std::string fileName = "MISSC.txt";
  // myfile.open(fileName, std::ios_base::trunc);
  // myfile << "IMISS : " << ::IMISS << '\n'
  //        << "DMISS : " << ::DMISS << '\n'
  //        << "L2MISS : " << ::L2MISS << '\n';
  // myfile.close();
  // IMISS = DMISS = L2MISS = 0; // RESET

  // output_data.dump("output_information.txt", "a");
  // Release the call graph instance
  CallGraph::getGraph().releaseInstance();
  // Dump the json array to file
  std::error_code EC;
  llvm::raw_fd_ostream OS("WCET.json", EC);
  llvm::json::Value val(std::move(result));
  OS << llvm::formatv("{0:4}", val) << '\n';
  OS.flush();
  OS.close();

  manager.insert("Summary", std::move(output_data));

  return false;
}

// 每轮生命周期迭代都要ValueAnalysis吗？
// 这里包含了一次WCET和一次BCET，感觉这里包含了整个大流程
template <Triple::ArchType ISA>
void TimingAnalysisMain::dispatchValueAnalysis() {
  ofstream Myfile;

  std::tuple<> NoDep;
  AnalysisDriverInstr<ConstantValueDomain<ISA>> ConstValAna(NoDep);
  // step1: CV分析
  auto CvAnaInfo = ConstValAna.runAnalysis(); //MicroArch和ConstantValue的共同接口？
  // No，MuArch的类是CV的那个类的子类
  // step2: 循环计算
  LoopBoundInfo->computeLoopBoundFromCVDomain(*CvAnaInfo); // LoopBoundInfoPass *LoopBoundInfo;

  if (UseMetaDataAsAnnotation) {
    // Use the metadata as loop annotation
    assert(::ModulePtr && "Module not set");
    LoopBoundInfo->extractLoopAnnotationsFromMetaData(::ModulePtr);
  }

  if (OutputLoopAnnotationFile) {
    ofstream Myfile2;
    Myfile.open("CtxSensLoopAnnotations.csv", ios_base::app);
    Myfile2.open("LoopAnnotations.csv", ios_base::app);
    LoopBoundInfo->dumpNonUpperBoundLoops(Myfile, Myfile2);
    Myfile2.close();
    Myfile.close();
    return;
  }

  for (auto BoundsFile : ManuallowerLoopBounds) {
    LoopBoundInfo->parseManualLowerLoopBounds(BoundsFile.c_str());
  }
  for (auto BoundsFile : ManualLoopBounds) {
    LoopBoundInfo->parseManualUpperLoopBounds(BoundsFile.c_str());
  }

  if (!QuietMode) {
    //持久分析改动标记
    // Myfile.open("PersistenceScopes.txt", ios_base::trunc);
    // PersistenceScopeInfo::getInfo().dump(Myfile);
    // Myfile.close();

    Myfile.open("LoopBounds.txt", ios_base::trunc);
    LoopBoundInfo->dump(Myfile);
    Myfile.close();

    Myfile.open("ConstantValueAnalysis.txt", ios_base::app);
    CvAnaInfo->dump(Myfile);
    Myfile.close();
  }
  
  AddressInformationImpl<ConstantValueDomain<ISA>> AddrInfo(*CvAnaInfo);// step3： Cv用来获取地址信息
  ::glAddrInfo = &AddrInfo;

  if (!QuietMode) {
    Myfile.open("AddressInformation.txt", ios_base::trunc);
    AddrInfo.dump(Myfile);
    Myfile.close();
  }

  VERBOSE_PRINT(" -> Finished Value & Address Analysis\n");

  // Set and check the parameters of the instruction and data cache
  icacheConf.LINE_SIZE = Ilinesize; // 从命令行赋值到DispatchMemory
  icacheConf.ASSOCIATIVITY = Iassoc;
  icacheConf.N_SETS = Insets;
  icacheConf.LEVEL = 1;
  icacheConf.LATENCY = ILatency;
  icacheConf.checkParams(); // 就检查写策略组合是否合法

  dcacheConf.LINE_SIZE = Dlinesize;
  dcacheConf.ASSOCIATIVITY = Dassoc;
  dcacheConf.N_SETS = Dnsets;
  // data cache才会有这样的策略
  dcacheConf.WRITEBACK = DataCacheWriteBack;
  dcacheConf.WRITEALLOCATE = DataCacheWriteAllocate;
  icacheConf.LATENCY = DLatency;
  dcacheConf.LEVEL = 1;
  dcacheConf.checkParams();

  dcacheConf.LINE_SIZE = L2linesize;
  l2cacheConf.LINE_SIZE = Dlinesize;
  l2cacheConf.N_SETS = NN_SET;
  l2cacheConf.ASSOCIATIVITY = L2assoc;
  l2cacheConf.LATENCY = L2Latency;
  l2cacheConf.LEVEL = 2;
  l2cacheConf.checkParams();
  // 分别完成一次WCET 和 BCET计算
  // WCET
  // Select the analysis to execute
  dispatchAnalysisType(AddrInfo); // 这里根据几种分析TYPE分别完成计算
  // Release the call graph instance
  // CallGraph::getGraph().releaseInstance();

  // Write results and statistics
  Statistics &Stats = Statistics::getInstance();
  AnalysisResults &Ar = AnalysisResults::getInstance();

  // Stats.stopMeasurement("Complete Analysis");

  Myfile.open(std::to_string(this->coreNum) + "_" + AnalysisEntryPoint +
                  "_Statistics.txt",
              ios_base::app);
  Stats.dump(Myfile);
  Myfile.close();

  Myfile.open(std::to_string(this->coreNum) + "_" + AnalysisEntryPoint +
                  "_TotalBound.xml",
              ios_base::app);
  Ar.dump(Myfile);
  Myfile.close();
  // BCET
  ::isBCET = true;
  dispatchAnalysisType(AddrInfo);
  // Write results and statistics
  Statistics &Stats1 = Statistics::getInstance();
  AnalysisResults &Ar1 = AnalysisResults::getInstance();
  Myfile.open(std::to_string(this->coreNum) + "_" + AnalysisEntryPoint +
                  "_TotalBound.xml",
              ios_base::app);
  Ar1.dump(Myfile);
  Myfile.close();
  ::isBCET = false;
  // No need for constant value information
  delete CvAnaInfo;
  PersistenceScopeInfo::deletper();
}

// 不同分析类型，不同输出，有TIMING CRPD CACHE等类型
void TimingAnalysisMain::dispatchAnalysisType(AddressInformation &AddressInfo) {
  AnalysisResults &Ar = AnalysisResults::getInstance();
  // Timing & CRPD calculation need normal muarch analysis first
  if (AnaType.isSet(AnalysisType::TIMING) ||
      AnaType.isSet(AnalysisType::CRPD)) {
    auto Bound = dispatchTimingAnalysis(AddressInfo); // 这里应该是主要计算
    // 包括microArch + PathAnalysis
    Ar.registerResult("total", Bound);
    if (Bound) { // 这后面基本上是每个iteration每个函数的W/B的分析完的输出
      if (!isBCET) {
        outs() << std::to_string(Core)
               << "-Core:   " + AnalysisEntryPoint +
                      "_Calculated WCET Timing Bound: "
               << llvm::format("%-20.0f", Bound.get().ub) << "\n";
        this->WCETtime = Bound.get().ub;
      } else {
        outs() << std::to_string(Core)
               << "-Core:   " + AnalysisEntryPoint +
                      "_Calculated BCET Timing Bound: "
               << llvm::format("%-20.0f", Bound.get().lb) << "\n";
        this->BCETtime = Bound.get().lb;
      }
    } else {
      outs() << std::to_string(Core)
             << "-Core:   " + AnalysisEntryPoint +
                    "_Calculated Timing Bound: infinite\n";
      // set wcet and bcet to 0
      this->WCETtime = 0;
      this->BCETtime = 0;
    }
  }
  if (AnaType.isSet(AnalysisType::L1ICACHE)) {
    auto Bound = dispatchCacheAnalysis(AnalysisType::L1ICACHE, AddressInfo);
    Ar.registerResult("icache", Bound);
    if (Bound) {
      outs() << "Calculated "
             << "Instruction Cache Miss Bound: "
             << llvm::format("%-20.0f", Bound.get().ub) << "\n";
    } else {
      outs() << "Calculated "
             << "Instruction Cache Miss Bound: infinite\n";
    }
  }
  if (AnaType.isSet(AnalysisType::L1DCACHE)) {
    auto Bound = dispatchCacheAnalysis(AnalysisType::L1DCACHE, AddressInfo);
    Ar.registerResult("dcache", Bound);
    if (Bound) {
      outs() << "Calculated "
             << "Data Cache Miss Bound: "
             << llvm::format("%-20.0f", Bound.get().ub) << "\n";
    } else {
      outs() << "Calculated "
             << "Data Cache Miss Bound: infinite\n";
    }
  }
}

///////////////////////////////////////////////////////////////////////////////
/// Timing Analysis
/// ///////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

boost::optional<BoundItv>
TimingAnalysisMain::dispatchTimingAnalysis(AddressInformation &AddressInfo) {
  // Note, we no longer need this, this functionName will get check before
  // enter if (!functionName) {
  //   fprintf(stderr, "You should not come here");
  //   exit(10);
  // }
  switch (MuArchType) { // CPU类型，乱序、顺序、PERT等;这几个case的函数都在LLVMPass里实现的
  case MicroArchitecturalType::FIXEDLATENCY:
    assert(MemTopType == MemoryTopologyType::NONE &&
           "Fixed latency has no external memory");
    return dispatchFixedLatencyTimingAnalysis(Core);
  case MicroArchitecturalType::PRET:
    return dispatchPretTimingAnalysis(AddressInfo, Core);
  case MicroArchitecturalType::INORDER:
  case MicroArchitecturalType::STRICTINORDER:
    return dispatchInOrderTimingAnalysis(AddressInfo, Core); // 先关注这个
  case MicroArchitecturalType::OUTOFORDER: // 我们在此
    return dispatchOutOfOrderTimingAnalysis(AddressInfo, Core);
  default:
    errs() << "No known microarchitecture chosen.\n";
    return boost::none;
  }
}

boost::optional<BoundItv>
TimingAnalysisMain::dispatchCacheAnalysis(AnalysisType Anatype,
                                          AddressInformation &AddressInfo) {
  switch (MuArchType) {
  case MicroArchitecturalType::INORDER:
  case MicroArchitecturalType::STRICTINORDER:
    return dispatchInOrderCacheAnalysis(Anatype, AddressInfo);
  default:
    errs() << "Unsupported microarchitecture for standalone cache analysis.\n";
    return boost::none;
  }
}

} // namespace TimingAnalysisPass

FunctionPass *llvm::createTimingAnalysisMain(TargetMachine &TM) {
  return new TimingAnalysisPass::TimingAnalysisMain(TM);
}
