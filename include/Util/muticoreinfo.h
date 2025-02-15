#ifndef MUTICORE_INFORMATION
#define MUTICORE_INFORMATION

#include "Util/AbstractAddress.h"
#include "Util/Options.h"
#include <cstddef>
#include <map>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "llvm/CodeGen/MachineBasicBlock.h"
#include "llvm/CodeGen/MachineInstr.h"
#include "llvm/CodeGen/MachineLoopInfo.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/Analysis/LoopInfo.h"

#include "LLVMPasses/MachineFunctionCollector.h" // 由函数名找函数
#include "LLVMPasses/StaticAddressProvider.h" // mi -> addr
#include "LLVMPasses/DispatchMemory.h" // cacheconfig

#include "Memory/Classification.h" // CL_MISS/UNKONWN/HIT
#include "Memory/CacheTraits.h" // addr -> cache index
#include "PathAnalysis/LoopBoundInfo.h"

#include "llvm/Support/FileSystem.h" // 输出ur-cfg图片
#include "llvm/Support/raw_ostream.h"

// using namespace TimingAnalysisPass;

struct X_Class {
  unsigned x;
  TimingAnalysisPass::dom::cache::Classification classification;
};

/// 提供 ZW paper f函数运算所需的信息的查找方式
class UnorderedRegion{
public:
  std::map<const llvm::MachineInstr *, X_Class> mi2xclass;
};

class CEOP{
public:
  std::vector<UnorderedRegion> URs; // 路径上的UR(按顺序)
  // 这里已经包含了排序信息，即UR编号
};

/*
  MI + 完整的函数调用栈，可以在UR-CFG上唯一标识一个MI
*/
class CtxMI{
public:
  const llvm::MachineInstr* MI;
  std::vector<const llvm::MachineInstr *> CallSites;
};

/* 这个类就是维护MSG的 */
class Multicoreinfo {
private:
  // CoreNum -> <Earlest Start, Latest Stop>list
  std::vector<std::vector<std::pair<unsigned, unsigned>>> schedule;
  // CoreNum -> <BCET, WCET>list
  std::vector<std::vector<std::pair<unsigned, unsigned>>> BWtime;

  // CoreNum -> map<function, index>
  // BTW, this is actually core order (orz) // 6
  std::vector<std::map<std::string, unsigned>> coreOrz;

public:
  // // function->address of Instruction->地址的执行次数   //不用地址，用block
  std::map<std::string, std::map<unsigned, unsigned>> addressinfowithtime;
  std::map<std::string, std::set<unsigned>> addressinfo;
  // CoreNum -> vector of function
  std::vector<std::vector<std::string>> coreinfo;

  // 张伟复现
  // (Core, Function) -> [CEOP]
  std::map<unsigned, std::map<std::string, std::vector<CEOP>>> CEOPs; // 各个task的CEOP集合(别set了，比较函数不好写)
  std::map<unsigned, std::map<std::string, unsigned>> currWcetIntra;
  std::map<unsigned, std::map<std::string, unsigned>> currWcetInter; // 目前各Task的WCEET，迭代更新
  // TODO: 需要初始化
  std::vector<std::map<std::string, std::pair<unsigned, unsigned>>> intraBWtime; // 单核BW
  // 拿到MachineLoop的信息，这样我就可以通过MBB直接得到其外层循环，然后得到执行次数；
  // 需要先从LoopBoundInfoPass偷到这个信息
  // std::map<std::string, MachineLoopInfo> f2MLI; // 算了目前这个设计上有点麻烦，暂时不采用

  // 注意从0还是1开始计数,目前0,见main; FIXME这里参数有点冗余
  unsigned getFValue(unsigned localCore, CEOP localPath, unsigned localUR,
      unsigned interCore, CEOP interPath, unsigned interUR){
    // TODO 这里参数是不是还漏了Core上的哪个函数？有CEOP问题不大，甚至Core号也是多余的
    UnorderedRegion local_ur = localPath.URs[localUR];
    UnorderedRegion inter_ur = interPath.URs[interUR];
    std::map<unsigned, unsigned> index2ExeTimes;
    std::map<unsigned, bool> indexIsDisturbed;
    unsigned ret_val = 0;

    // debug
    std::ofstream myfile;
    std::string fileName = "addr_in_ur.txt";
    if(ZWDebug){
      myfile.open(fileName, std::ios_base::app);
      myfile<<"Core:"<<localCore<<" LocalUR:"<<localUR<<
        " Core"<<interCore<<" InterUR:"<<interUR<<"\n";
    }
    for(const auto &local_pair:local_ur.mi2xclass){
      const llvm::MachineInstr* local_mi = local_pair.first;
      unsigned tmp_exe_times = local_pair.second.x;
      if(local_pair.second.classification!=
        TimingAnalysisPass::dom::cache::CL_HIT){ 
        continue;
      }
      index2ExeTimes[mi2cacheIndex(local_mi)] += tmp_exe_times;
      if(ZWDebug){
        myfile<<"  "<<"LocalMI"<<local_mi<<
          " Iaddr:"<<TimingAnalysisPass::StaticAddrProvider->getAddr(local_mi)<<
          " Cindex"<<mi2cacheIndex(local_mi)<<"\n";
      }
    }
    for(const auto &inter_pair:inter_ur.mi2xclass){
      const llvm::MachineInstr* inter_mi = inter_pair.first;
      if((inter_pair.second.classification!=
        TimingAnalysisPass::dom::cache::CL_HIT)&&
        (inter_pair.second.classification!=
        TimingAnalysisPass::dom::cache::CL_UNKNOWN)){ 
        continue;
      }
      indexIsDisturbed[mi2cacheIndex(inter_mi)] = true;
      if(ZWDebug){
        myfile<<"  "<<"InterMI"<<inter_mi<<
          " Iaddr:"<<TimingAnalysisPass::StaticAddrProvider->getAddr(inter_mi)<<
          " Cindex"<<mi2cacheIndex(inter_mi)<<"\n";
      }
    }
    for(auto &pair:index2ExeTimes){
      if(indexIsDisturbed[pair.first]){
        ret_val += pair.second;
      }
    }
    return ret_val;
  }

  // helper function
  unsigned mi2cacheIndex(const llvm::MachineInstr* mi){
    unsigned tmp_addr = TimingAnalysisPass::StaticAddrProvider->getAddr(mi);
    return (tmp_addr / TimingAnalysisPass::l2cacheConf.LINE_SIZE) 
      % TimingAnalysisPass::l2cacheConf.N_SETS;
    // line_size为64byte的话，低6位地址是offset；1024set的话，再过10位是index
  }

  // helper function

  unsigned getbound(const MachineBasicBlock *MBB,
                    const TimingAnalysisPass::Context &ctx) {
    for (const MachineLoop *loop :
        TimingAnalysisPass::LoopBoundInfo->getAllLoops()) {
      if (MBB->getParent() == loop->getHeader()->getParent() &&
          loop->contains(MBB)) {
        if (TimingAnalysisPass::LoopBoundInfo->hasUpperLoopBound(
                loop, TimingAnalysisPass::Context())) {
          return TimingAnalysisPass::LoopBoundInfo->getUpperLoopBound(
              loop, TimingAnalysisPass::Context());
        }
      }
    }
    return 1; // 没bound默认1次了
  }
  /*
    搞不了自底向上，搞自顶向下也是ok，在一个函数的所有loop里搜，搜到此BB在此loop里即可取
    优先取更深层的loop；一个函数多个循环是可以的，一个Basic Block足以定位哪个循环
  */
  unsigned getbound_plus(){
    return 1;
  }

  // helper function:TODO有待优化；需要假设循环次数是已知的
  unsigned getExeTimes(const llvm::MachineInstr* mi){ // TODO改为CtxMI
    const llvm::MachineBasicBlock* mbb = mi->getParent();
    // const llvm::MachineLoop* ml = llvm::MachineLoopInfo::getLoopFor(mbb);
    unsigned tmpBound = getbound(mbb, TimingAnalysisPass::Context());
    return tmpBound;
  }

  // 收集XClass信息(假设没有不同核的重名函数)
  void addXClass(unsigned core, std::string function, const llvm::MachineInstr* mi, 
    TimingAnalysisPass::dom::cache::Classification classification,
    unsigned x
  ){
    X_Class obj;
    // 使用mi计算x
    // obj.x = x; // 直接忽略这个参数
    obj.x = getExeTimes(mi);
    obj.classification = classification;
    mi_xclass[core][function][mi] = obj;
    return;
  }

  Multicoreinfo();
  // Make all constructor and destructor to be default
  Multicoreinfo(unsigned coreNum)
      : schedule(coreNum), BWtime(coreNum), coreinfo(coreNum),
        coreOrz(coreNum){};
  ~Multicoreinfo() = default;
  Multicoreinfo(const Multicoreinfo &) = default;

  void setSize(unsigned core) {
    schedule.resize(core);
    BWtime.resize(core);
    coreinfo.resize(core);
    // addressinfo.resize(core);
    coreOrz.resize(core);
    intraBWtime.resize(core);
  }

  void addaddress(std::string function, unsigned addressLINE) {
    addressinfo.at(function).insert(addressLINE);
  }

  void addaddress(std::string function, std::vector<unsigned> &addrlist,
                  int time) {
    for (auto &addressLINE : addrlist) {
      addressinfowithtime.at(function)[addressLINE] += time;
      addressinfo.at(function).insert(addressLINE);
    }
  }
  // void addaddress(std::string function,
  //                 TimingAnalysisPass::AbstractAddress &addr, int time) {
  //   //未知的地址不管
  //   if (addr.isSameInterval(
  //           TimingAnalysisPass::AbstractAddress::getUnknownAddress())) {
  //     return;
  //   }
  //   //数组的地址会转换为地址范围
  //   unsigned lowAligned = addr.getAsInterval().lower() & ~(Dlinesize - 1);
  //   unsigned upAligned = addr.getAsInterval().upper() & ~(Dlinesize - 1);
  //   while (lowAligned <= upAligned) {
  //     addaddress(function, lowAligned, time);
  //     lowAligned += Dlinesize;
  //   }
  // }

  void addTask(unsigned num, const std::string &function) {
    coreinfo[num].emplace_back(function);
    //对没有分析过的函数进行访存信息收集，这是个初始化
    if (addressinfo.find(function) == addressinfo.end()) {
      addressinfowithtime.insert(
          std::make_pair(function, std::map<unsigned, unsigned>{}));
      addressinfo.insert(std::make_pair(function, std::set<unsigned>{}));
    }
    coreOrz[num].insert(std::make_pair(function, coreinfo[num].size() - 1));
    schedule[num].emplace_back(std::make_pair(0, 0)); // 这个00初值没问题吗？
    BWtime[num].emplace_back(std::make_pair(0, 0));
  }

  void setTaskTime(unsigned core, const std::string &function,
                   unsigned early = 0, unsigned latest = 0) {
    // CHECK_CORE_VALIE(core)

    if (coreOrz[core].count(function) == 0) {
      fprintf(stderr, "Function %s can not found on core %u\n",
              function.c_str(), core);
      return;
    }
    schedule[core][coreOrz[core][function]].first = early;
    schedule[core][coreOrz[core][function]].second = latest;
  }

  bool updateTaskTime(unsigned core, const std::string &function,
                      unsigned early = 0, unsigned latest = 0) { // 这两参数是BCET和WCET
    if (coreOrz[core].count(function) == 0) {
      fprintf(stderr, "Function %s can not found on core %u\n",
              function.c_str(), core);
      return false;
    }
    bool changed = false;
    unsigned taskNum = coreOrz[core][function]; // CoreNum -> map<function, index>核上第几个函数
    if (BWtime[core][taskNum].first != early || // map里存的是生命周期
        BWtime[core][taskNum].second != latest) {
      changed = true;
      //更新 执行时间
      BWtime[core][taskNum].first = early;
      BWtime[core][taskNum].second = latest;
    }
    //更新生命周期
    if (taskNum == 0) {
      schedule[core][taskNum].second = 0u + latest;
    } else {
      schedule[core][taskNum].second =
          schedule[core][taskNum - 1].second + latest; // 原来前置就只考虑1个
    }
    if (taskNum != schedule[core].size() - 1) {
      schedule[core][taskNum + 1].first = schedule[core][taskNum].first + early;
    }
    return changed;
  }

  std::vector<std::string> getConflictFunction(unsigned core,
                                               const std::string &function) {
    std::vector<std::string> list;
    auto liftime = schedule[core][coreOrz[core][function]]; // (core, index) -> (ES, LF)
    // if (liftime.first == 0 || liftime.second == 0) {
    //   list.emplace_back("ALL");
    //   return list;
    // }
    for (int i = 0; i < schedule.size(); i++) { //各个其它核心
      if (i == core) {
        continue;
      }
      for (int j = 0; j < schedule[i].size(); j++) { //的各个task
        auto &tlifetime = schedule[i][j];
        if (tlifetime.second > liftime.first &&
                tlifetime.second < liftime.second ||
            tlifetime.first >= liftime.first &&
                tlifetime.first < liftime.second ||
            liftime.first >= tlifetime.first &&
                liftime.second <= tlifetime.second) {
          list.emplace_back(coreinfo[i][j]);
        }
      }
    }
    return list;
  }

  // 第一轮迭代，直接返回所有能冲突的函数，而与上述基于生命周期的getConflictFunction区分开来
  std::vector<std::string> getInitConflictFunction(unsigned core,
                                               const std::string &function) {
                                                // 目前没有考虑跨核依赖
    std::vector<std::string> list;
    for(int i = 0;i < coreinfo.size(); i++){
      if(i == core){
        continue;
      }
      for(int j = 0;j < coreinfo[i].size(); j++){
        list.emplace_back(coreinfo[i][j]);
      } 
    }
    return list;
  }

  std::pair<unsigned, unsigned> getlifetime(unsigned core,
                                            const std::string &function) {
    return schedule[core][coreOrz[core][function]];
  }

  std::pair<unsigned, unsigned> getPreTask(unsigned core,
                                           const std::string &function) {
    // CHECK_CORE_VALIE(core)

    int pre = coreOrz[core][function] - 1;
    if (pre >= 0) {
      return schedule[core][pre];
    }
    return std::make_pair(0u, 0u);
  }

private:
  // module1: 暂存对一个task的UR分析数据，对应oi-wiki tarjan算法
  std::map<const llvm::MachineInstr*, unsigned> dfn;
  std::map<const llvm::MachineInstr*, unsigned> low;
  unsigned dfncnt;
  std::map<unsigned, const llvm::MachineInstr*> ur_stack;
  std::map<const llvm::MachineInstr*, unsigned> in_stack;
  unsigned stack_pt;
  std::map<const llvm::MachineInstr*, unsigned> mi_ur; // MI所在ur_id
  std::map<unsigned, unsigned> ur_size; // 指含有多少条MI
  unsigned ur_id; // 强连通分量号，这个序号应该没有什么含义
  std::map<const llvm::MachineInstr*, const llvm::MachineBasicBlock*> mi_mbb; // MI所在MBB

  // module2: 新图，UR的出入边包含原来属于UR的MI的所有出入边
  std::map<unsigned, std::vector<unsigned>> ur_graph;
  std::map<unsigned, std::vector<const llvm::MachineInstr*>> ur_mi; // 没有顺序

  // module3： 除了这个module其它3个module都是暂存的
  std::map<unsigned, std::map<std::string, // core, function, mi -> xclass
    std::map<const llvm::MachineInstr*, X_Class>>> mi_xclass; // TODO 先存着class
    // 后面需要扩展为 CtxMI->xclass
  unsigned cur_core;
  std::string cur_func;

  // module: CEOP
  std::vector<UnorderedRegion> tmpPath; // 暂存UR图DFS的PATH
  std::vector<CEOP> tmpCEOPs; // 暂存本task上所有路径

  // 显式收集MI-CFG，用于debug
  std::map<const llvm::MachineInstr*, 
    std::vector<const llvm::MachineInstr*>> mi_cfg;

public:
  /// UR于CEOP的计算函数
  void URCalculation(unsigned core, const std::string &function){
    // 参照analysisDriver.h
    auto MF = TimingAnalysisPass::machineFunctionCollector->
      getFunctionByName(function);
    const MachineBasicBlock *analysisStart = &*(MF->begin());
    // 每次需要清空上述用于暂存的数据结构
    dfncnt = stack_pt = ur_id = 0;
    // 新的task清空全部暂存的数据结构；map用迭代器清空会把实例都清了，这里就只清指针
    dfn.clear();
    low.clear();
    ur_stack.clear();
    in_stack.clear();
    mi_ur.clear();
    ur_size.clear();
    mi_mbb.clear();
    ur_graph.clear();
    ur_mi.clear();
    tmpCEOPs.clear();
    mi_cfg.clear();

    cur_core = core;
    cur_func = function;

    const llvm::MachineInstr* firstMI = &(analysisStart->front());
    tarjan(analysisStart, firstMI); // module1: 在CFG上获取UR
    if(ZWDebug){
      print_mi_cfg(function); // debug
    }
    collectUrInfo(); // module2: 建立UR图和ur为键的信息映射
    // module3: 需要先收集x_class信息，这样下一步得到的信息才完整
    // DAG的DFS标记CEOP
    collectCEOPInfo(firstMI); // module4: dfs遍历图，并同时建立起CEOP的数据结构
    CEOPs[core][function] = tmpCEOPs;    

    if(ZWDebug){
      std::ofstream myfile;
      std::string fileName = function + "_CEOP_info.txt";
      myfile.open(fileName, std::ios_base::trunc);
      myfile<<"Function: "<<function<<"with "<<tmpCEOPs.size()<<"CEOPs"<<std::endl;
      for (int i=0;i<tmpCEOPs.size();i++) {
        CEOP tmp_ceop = tmpCEOPs[i];
        myfile<<"  CEOP-"<<i<<" have "<<tmp_ceop.URs.size()<<" UR(s)"<<std::endl;
      }
    }
  }

  // helper, 在此将所有CEOP所需数据存入tmpCEOPs
  void ceopDfs(unsigned u){
    UnorderedRegion curUR{};
    std::vector<const llvm::MachineInstr*> curMIs = ur_mi[u];
    for(int i=0;i<curMIs.size();i++){
      X_Class obj = mi_xclass[cur_core][cur_func][curMIs[i]];
      // if(curMIs[i]->isTransient()) continue; // 这里包括伪指令等
      curUR.mi2xclass.insert(std::make_pair(curMIs[i], obj));
    }
    assert(curUR.mi2xclass.size()!=0 && "UR must have at least 1 instr");
    tmpPath.push_back(curUR);

    std::vector<unsigned> vs = ur_graph[u];
    if(vs.size()==0){ // 出口
      CEOP curCeop{};
      curCeop.URs = tmpPath;
      tmpCEOPs.push_back(curCeop); // recorded
      tmpPath.pop_back();
      return;
    }

    for(int i=0;i<vs.size();i++){
      unsigned v = vs[i];
      ceopDfs(v);
    }
    tmpPath.pop_back();
    return;
  }

  // 构造之前定义的CEOP和UR对象，UR中的X_Class内容先设置为空
  void collectCEOPInfo(const llvm::MachineInstr* firstMI){
    unsigned s = mi_ur[firstMI];
    ceopDfs(s);
  }

  // 反过来获取UR -> (出边、 MI);也即包含了建立UR图
  void collectUrInfo(){
    for(auto m_u:mi_ur){
      const llvm::MachineInstr* mi_ptr = m_u.first;
      unsigned ur_id_num = m_u.second;
      auto it = ur_graph.find(ur_id_num);
      if (it == ur_graph.end()){ // 首次记录某个UR
        std::vector<unsigned> ur_out_edge_vec;
        ur_graph[ur_id_num] = ur_out_edge_vec;
        std::vector<const llvm::MachineInstr*> ur_mi_vec;
        ur_mi[ur_id_num] = ur_mi_vec;
      }
      // 在ur中添加mi
      ur_mi[ur_id_num].push_back(mi_ptr);
      // 在ur中添加后继ur
      const llvm::MachineBasicBlock* mbb_ptr = mi_mbb[mi_ptr];
      std::vector<std::pair<const llvm::MachineBasicBlock*, 
        const llvm::MachineInstr*>> succ_mis = getMiCFGSucc(mbb_ptr, mi_ptr);
      for (auto succ_mi:succ_mis){
        const llvm::MachineInstr* target_mi_ptr = succ_mi.second;
        unsigned target_ur_id_num = mi_ur[target_mi_ptr];
        if(ur_id_num!=target_ur_id_num){
          ur_graph[ur_id_num].push_back(target_ur_id_num);
        }
      }
    }
  }

  void print_mi_cfg(const std::string &function){
    const std::vector<std::string> colors = {
        "turquoise", "lightblue", "lightgreen",  "lightyellow", "white"
    };
    std::unordered_map<std::string, std::string> func_color_map;
    int color_index = 0;
    std::error_code EC;
    raw_fd_ostream File(function + "machine_cfg.dot", EC, sys::fs::OpenFlags::OF_Text);
    if (EC) {
        errs() << "Error opening file: " << EC.message() << "\n";
    }
    File << "digraph \"MachineCFG of " + function + "\" {\n";
    for(auto tmp_pair:mi_cfg){
      // 函数获取或分配颜色
      const llvm::MachineInstr *MI = tmp_pair.first;
      const std::string func_name = 
        MI->getParent()->getParent()->getFunction().getName().str();
      if (func_color_map.find(func_name) == func_color_map.end()) {
          func_color_map[func_name] = colors[color_index % colors.size()];
          color_index++;
      }
      const std::string color = func_color_map[func_name];
      // 节点
      File << "  " << "Node" << MI << " [label=\"MI" << MI << "\\l  ";  
      MI->print(File, false, false, true);
      File << "\\l  ";
      std::string tmp_flag = (MI->isTransient())?"True":"False";
      File << "isTransient:" << tmp_flag << "\\l  ";
      File << "ExeCnt:" << mi_xclass[cur_core][function][MI].x << " "
        << "CHMC:" << mi_xclass[cur_core][function][MI].classification
        << "\\l  ";
      File << "in BB" << MI->getParent()->getNumber() << "\\l  ";
      File << "in UR" << mi_ur[MI] << "\\l  ";
      File << "in Func: " << 
        MI->getParent()->getParent()->getFunction().getName() << "\\l";   
      File << "\" fillcolor=\"" << color << "\" style=\"filled\"];\n"; 
      // 边
      std::vector<const llvm::MachineInstr *> tmp_MIs = tmp_pair.second;
      for(auto tmp_MI:tmp_MIs){
        File << "  " << "Node" << MI << " -> " << "Node" << tmp_MI << ";\n";
      }
    }
    File << "}\n";
  }

  // 要带着MBB来遍历MI-CFG
  void tarjan(const llvm::MachineBasicBlock* MBB, 
    const llvm::MachineInstr* MI){
    mi_mbb[MI] = MBB; // 先收集一手MI属于哪个MBB，后面UR建图所用

    low[MI] = dfn[MI] = ++dfncnt;
    ur_stack[++stack_pt] = MI; 
    in_stack[MI] = 1;

    std::vector<std::pair<const llvm::MachineBasicBlock*, 
      const llvm::MachineInstr*>> SUCCs = getMiCFGSucc(MBB, MI);

    // 收集mi_cfg，用来输出debug // 改为ctxmi
    if(mi_cfg.find(MI)==mi_cfg.end()){
      std::vector<const llvm::MachineInstr*> tmp_mi_succ;
      for(auto tmp_pair:SUCCs){
        const llvm::MachineInstr* tmp_mi = tmp_pair.second;
        tmp_mi_succ.push_back(tmp_mi);
      }
      mi_cfg[MI] = tmp_mi_succ;
    }

    for(auto SUCC:SUCCs){
      const llvm::MachineBasicBlock* SUCC_MBB = SUCC.first;
      const llvm::MachineInstr* SUCC_MI = SUCC.second;
      if(dfn.find(SUCC_MI)==dfn.end()){ // 从未访问
        tarjan(SUCC_MBB, SUCC_MI);
        low[MI] = std::min(low[MI], low[SUCC_MI]); // 回溯，可能子树somehow返祖
      }else if(in_stack[SUCC_MI]){
        low[MI] = std::min(low[MI], dfn[SUCC_MI]);
      }
    }
    if (dfn[MI] == low[MI]) { // 回溯的时候再消，eg无子直接自成1个分量
      // 所以最后回访到子树的根时，别的都pop掉了
      ++ur_id;
      do {
        mi_ur[ur_stack[stack_pt]] = ur_id;
        ur_size[ur_id] += 1;
        in_stack[ur_stack[stack_pt]] = 0;
      } while (ur_stack[stack_pt--] != MI); 
    }
  }
  
  // 返回一条指令的后继者(一个MBB里的MI数应该不会太多， 所以这里不会太耗时)
  std::vector<std::pair<const llvm::MachineBasicBlock*, 
    const llvm::MachineInstr*>> getMiCFGSucc(
      const llvm::MachineBasicBlock* MBB, 
      const llvm::MachineInstr* MI){
    std::vector<std::pair<const llvm::MachineBasicBlock*, 
      const llvm::MachineInstr*>> retSucc;  
    
    // 我们已经消除了伪指令，不会有遍历伪指令后继者的情况
    assert((!MI->isTransient()) && "We should not see transient instr here");

    // call 和 return(嵌入处理)
    auto &cg = TimingAnalysisPass::CallGraph::getGraph();
    if(MI->isCall() && !cg.callsExternal(MI)){
      for (const auto *callee : cg.getPotentialCallees(MI)) {
        const MachineBasicBlock *calleeBeginBB = &*callee->begin();
        const llvm::MachineInstr* calleeBeginMI = &(calleeBeginBB->front());
        assert((!calleeBeginMI->isTransient())
          && "First Instr of func shouldn't be transient");
        retSucc.push_back(std::make_pair(calleeBeginBB, calleeBeginMI));
      }
      return retSucc;
    }
    if(MI->isReturn()){
      const auto *currentFunc = MI->getParent()->getParent();
      for (auto &callsite : cg.getCallSites(currentFunc)) { 
        // 如果将函数理解为内嵌在调用方的语句，那么被多次调用的函数会被共享
        const auto *callsiteMBB = callsite->getParent(); // 这里回到了call语句
        // 但我们需要call的下一条指令(call不会是Basic Block里最后一条指令)
        auto it = std::find_if(callsiteMBB->begin(), callsiteMBB->end(),
                       [callsite](const MachineInstr &Instr) 
                        { return &Instr == callsite; });
        if (it != callsiteMBB->end() && 
          std::next(it) != callsiteMBB->end()) { // 包含了下一条是最后一条
          const llvm::MachineInstr* targetMI = &*(std::next(it));
          // 从源头消除伪指令
          // 我假设transient不会出现在BB头尾
          if(targetMI->isTransient()){
            auto tmp_pair = transientHelper(callsiteMBB, targetMI);
            retSucc.push_back(tmp_pair);
          }else{
            retSucc.push_back(std::make_pair(callsiteMBB, targetMI));
          }
        }
      }
      return retSucc;
    }

    // 可能两种情况，MBB内下一条MI，或者MBB最后一条MI到后继MBB的第一条MI
    if(MI == &(MBB->back())){
      for (auto succit = MBB->succ_begin(); succit != MBB->succ_end(); ++succit){
        const llvm::MachineBasicBlock *targetMBB = *succit;
        const llvm::MachineInstr* targetMI = &(targetMBB->front());
        retSucc.push_back(std::make_pair(targetMBB, targetMI));
      }
    }else{
      auto it = std::find_if(MBB->begin(), MBB->end(),
                       [MI](const MachineInstr &Instr) { return &Instr == MI; });
      if (it != MBB->end() && std::next(it) != MBB->end()) {
        const llvm::MachineInstr* targetMI = &*(std::next(it));
        // 从源头消除伪指令
        // 我假设transient不会出现在BB头尾
        if(targetMI->isTransient()){
          auto tmp_pair = transientHelper(MBB, targetMI);
          retSucc.push_back(tmp_pair);
        }else{
          retSucc.push_back(std::make_pair(MBB, targetMI));
        }
      }
    }
    return retSucc;
  }

  // 跳过transient的办法就是拿到它的第一个非transient后继(可能递归执行)
  // 目前只考虑单个transient唯一后继的情况
  std::pair<const llvm::MachineBasicBlock*, 
    const llvm::MachineInstr*> transientHelper(
    const llvm::MachineBasicBlock* MBB, 
    const llvm::MachineInstr* MI){
    if(!MI->isTransient()){
      return std::make_pair(MBB, MI);
    }
    assert((MI != &(MBB->back()))
      && "I assume transient instr isn't last instr of bb, but this indicates I am wrong");
    auto it = std::find_if(MBB->begin(), MBB->end(),
                       [MI](const MachineInstr &Instr) { return &Instr == MI; });
    if (it != MBB->end() && std::next(it) != MBB->end()) {
      const llvm::MachineInstr* targetMI = &*(std::next(it));
      return transientHelper(MBB, targetMI);
    }
  }
};

#endif