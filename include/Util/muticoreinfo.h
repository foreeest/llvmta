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

// 由函数名找函数
#include "LLVMPasses/MachineFunctionCollector.h"

#include "Memory/Classification.h"

/// 提供 ZW paper f函数运算所需的信息的查找方式
class UnorderedRegion{
public:
  struct X_Class {
    unsigned x;
    TimingAnalysisPass::dom::cache::Classification classification;
  };

  std::map<const llvm::MachineInstr *, X_Class> mi2xclass;
};

class CEOP{
public:
  std::vector<UnorderedRegion> URs; // 路径上的UR(按顺序)
  // 这里已经包含了排序信息，即UR编号
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
  std::map<unsigned, std::map<std::string, std::vector<CEOP>>> CEOPs; // 各个task的CEOP集合(别set了，比较函数不好写)
  std::vector<std::map<std::string, unsigned>> currWcetInter; // 目前各Task的WCEET，迭代更新
  // TODO: 需要初始化
  std::vector<std::map<std::string, std::pair<unsigned, unsigned>>> intraBWtime; // 单核BW

  // 计算f值，想想怎么设计能索引; 注意从0还是1开始计数,目前0,见main
  unsigned getFValue(unsigned localCore, CEOP localPath, unsigned localUR,
      unsigned interCore, CEOP interPath, unsigned interUR){
    // TODO 这里参数是不是还漏了Core上的哪个函数
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
                      unsigned early = 0, unsigned latest = 0) {
    if (coreOrz[core].count(function) == 0) {
      fprintf(stderr, "Function %s can not found on core %u\n",
              function.c_str(), core);
      return false;
    }
    bool changed = false;
    unsigned taskNum = coreOrz[core][function]; // CoreNum -> map<function, index>核上第几个函数
    if (BWtime[core][taskNum].first != early ||
        BWtime[core][taskNum].second != latest) {
      changed = true;
      //更新 执行时间
      BWtime[core][taskNum].first = early;
      BWtime[core][taskNum].second =latest;
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
      for(int j = 0;j < coreinfo[i].size(); i++){
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
  // 暂存UR分析数据，对应oi-wiki tarjan算法
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

  // 新图，UR的出入边包含原来属于UR的MI的所有出入边
  std::map<unsigned, std::vector<unsigned>> ur_graph;
  std::map<unsigned, std::vector<const llvm::MachineInstr*>> ur_mi; // 没有顺序

  // CEOP
  std::vector<UnorderedRegion> tmpPath; // 暂存UR图DFS的PATH
  std::vector<CEOP> tmpCEOPs; // 暂存本task上所有路径

public:
  /// UR于CEOP的计算函数
  void URCalculation(unsigned core, const std::string &function){
    // 参照analysisDriver.h
    auto MF = TimingAnalysisPass::machineFunctionCollector->getFunctionByName(AnalysisEntryPoint);
    const MachineBasicBlock *analysisStart = &*(MF->begin());
    // 每次需要清空上述用于暂存的数据结构
    dfncnt = stack_pt = 0;
    // 迭代器清空会把实例都清了，这里就只清指针
    dfn.clear();
    low.clear();
    ur_stack.clear();
    in_stack.clear();
    // TODO 没清空完
    const llvm::MachineInstr* firstMI = &(analysisStart->front());
    tarjan(analysisStart, firstMI);
    collectUrInfo();
    // DAG的DFS标记CEOP
    collectCEOPInfo(firstMI);
    CEOPs[core][function] = tmpCEOPs;    
  }

  // helper
  void ceopDfs(unsigned u){
    UnorderedRegion curUR{};
    std::vector<const llvm::MachineInstr*> curMIs = ur_mi[u];
    for(int i=0;i<curMIs.size();i++){
      curUR.mi2xclass.insert(std::make_pair(curMIs[i], UnorderedRegion::X_Class{}));
    }
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

  // 反过来获取UR -> (出边、 MI)
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

  // 要带着MBB来遍历MI-CFG
  void tarjan(const llvm::MachineBasicBlock* MBB, const llvm::MachineInstr* MI){
    mi_mbb[MI] = MBB; // 先收集一手MI属于哪个MBB，后面UR建图所用

    low[MI] = dfn[MI] = ++dfncnt;
    ur_stack[++stack_pt] = MI; 
    in_stack[MI] = 1;

    std::vector<std::pair<const llvm::MachineBasicBlock*, 
      const llvm::MachineInstr*>> SUCCs = getMiCFGSucc(MBB, MI);

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
  
  // 返回一条指令的后继者(一个MBB里的MI数应该不会太多吧？)
  std::vector<std::pair<const llvm::MachineBasicBlock*, 
    const llvm::MachineInstr*>> getMiCFGSucc(
      const llvm::MachineBasicBlock* MBB, 
      const llvm::MachineInstr* MI){
    std::vector<std::pair<const llvm::MachineBasicBlock*, 
      const llvm::MachineInstr*>> retSucc;  
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
        retSucc.push_back(std::make_pair(MBB, targetMI));
      }
    }
    return retSucc;
  }
};

#endif