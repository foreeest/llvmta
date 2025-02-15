////////////////////////////////////////////////////////////////////////////////
//
//   LLVMTA - Timing Analyser performing worst-case execution time analysis
//     using the LLVM backend intermediate representation
//
// Copyright (C) 2013-2022  Saarland University
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

#ifndef LRUMAXAGEANALYSIS_H_
#define LRUMAXAGEANALYSIS_H_

#include <algorithm>
#include <ostream>

#include "AbstractCache.h"
#include "Memory/CacheTraits.h"
#include "Memory/Classification.h"
#include "Memory/progana/Lattice.h"
#include "Memory/util/CacheUtils.h"
#include "Memory/util/ImplicitSet.h"
#include "Util/GlobalVars.h"
#include "Util/PersistenceScope.h"
#include <boost/tuple/tuple.hpp>
#include <string>
namespace TimingAnalysisPass {

namespace dom {
namespace cache {

/**
 * \tparam T Cache traits
 *
 * \brief   Implements a must analysis for an LRU cache set.
 * \todo Reimplement with SmallerOf magic as used in FifoMust.
 */

// 感觉这里就是Must分析的实现了
template <CacheTraits *T> // T应该是CacheTraits.h吧，封装有cache相连度等信息
class LruMaxAgeAbstractCache : public progana::JoinSemiLattice {
  typedef LruMaxAgeAbstractCache<T> Self;

protected:
  typedef typename CacheTraits::WayType WayType;
  typedef typename CacheTraits::TagType TagType; // 32位无符号整数
  typedef typename CacheTraits::PosType PosType;

  /**
   * tags[i] has a maximal age of ages[i].
   * for i<j: (ages[i] < ages[j]) || (ages[i] == ages[j] && tags[i] < tags[j])
   * 年龄相同，按tag排序，就随便找个顺序反正。所以这个就是实现16年cache survey里的Abstract Cache了
   */
  std::vector<TagType> tags;
  std::vector<WayType> ages; // 如果8bits用满256相连度就能0-255岁，值表示年龄
  PosType size; // what is pos？同一个集合有多少个Line(Block)
  // bool isl2;

public:
  using AnaDeps = std::tuple<>;

  explicit LruMaxAgeAbstractCache(bool assumeAnEmptyCache = false);
  Classification classify(const AbstractAddress addr) const; // 读了
  LruMaxAgeUpdateReport<TagType> *
  update(AbstractAddress addr, AccessType load_store, AnaDeps *,
         bool wantReport = false, const Classification assumption = CL_UNKNOWN);

  LruMaxAgeUpdateReport<TagType> *potentialUpdate(AbstractAddress addr,
                                                  AccessType load_store,
                                                  bool wantReport = false);
  void join(const Self &y); // 读了
  bool lessequal(const Self &y) const;
  void enterScope(const PersistenceScope &) {} // persistence相关的do nothing
  void leaveScope(const PersistenceScope &) {}
  std::set<PersistenceScope> getPersistentScopes(const TagType tag) const {
    return std::set<PersistenceScope>();
  }
  std::set<PersistenceScope>
  getPersistentScopes(const GlobalVariable *var) const {
    return std::set<PersistenceScope>();
  }
  bool operator==(const Self &y) const;
  bool operator<(const Self &y) const;
  std::ostream &dump(std::ostream &os) const;

  unsigned getMaxAge(const TagType tag) const;
  unsigned getNumberOfTagsWithMaxAge(int maxAge) const;
  ImplicitSet<TagType> getTagsWithMaxMaxAge(int maxAge) const;
  unsigned getMaxConcreteSubStackSize(int maxAge) const;
};

///\see dom::cache::CacheSetAnalysis<T>::CacheSetAnalysis(bool
/// assumeAnEmptyCache)
template <CacheTraits *T>
inline LruMaxAgeAbstractCache<T>::LruMaxAgeAbstractCache(
    bool assumeAnEmptyCache __attribute__((unused)))
    : tags(T->ASSOCIATIVITY), ages(T->ASSOCIATIVITY), size(0) {}

///\see dom::cache::CacheSetAnalysis<T>::classify(const TagType tag) const
// template <CacheTraits *T>
// Classification
// LruMaxAgeAbstractCache<T>::classify(const AbstractAddress addr) const {
//   unsigned CNN = 0;
//   TagType tag = getTag<T>(addr);
//   unsigned index = getindex<T>(addr);
//   if (T->LEVEL > 1) { // 假设>层1的皆共享
//     for (std::string &funtion : conflicFunctions) {
//       for (unsigned address : mcif.addressinfo[funtion]) {
//         if (getindex<T>(address) == index && getTag<T>(address) != tag) {
//           CNN++;
//         }
//       }
//     }
//   }

//   for (unsigned i = 0; i < size; ++i)
//     if (tags[i] == tag) {
//       if (ages[i] + CNN >= T->ASSOCIATIVITY) {
//         return CL_MISS; // 严谨一点应该是NC
//       }
//       return CL_HIT;
//     }
//   if (size == T->ASSOCIATIVITY)
//     return CL_MISS;
//   return CL_UNKNOWN;
// }
// 原版
template <CacheTraits *T>
Classification
LruMaxAgeAbstractCache<T>::classify(const AbstractAddress addr) const {
  TagType tag = getTag<T>(addr);
  for (unsigned i = 0; i < size; ++i)
    if (tags[i] == tag)
      return CL_HIT;
  if (size == T->ASSOCIATIVITY)
    return CL_MISS;
  return CL_UNKNOWN; // 因为没有在分析的时候进入，但cache又没满，这个块可能初始在里面
      // 也可能不在，所以是NC，非常严谨
}

/**
 * \brief Simulates an update to an unknown cache element, increase the age of
 * all elements
 */
template <CacheTraits *T>
LruMaxAgeUpdateReport<typename CacheTraits::TagType> *
LruMaxAgeAbstractCache<T>::potentialUpdate(AbstractAddress addr,
                                           AccessType load_store,
                                           bool wantReport) {
  unsigned pos = size;
  LruMaxAgeUpdateReport<TagType> *report = nullptr;
  if (wantReport) {
    report = new LruMaxAgeUpdateReport<TagType>;
  }

  // Evict all elements with age A-1
  while (pos > 0 && ages[pos - 1] == T->ASSOCIATIVITY - 1) {
    if (wantReport) {
      report->evictedElements.insert(tags[pos - 1]);
    }
    --size;
    --pos;
  }

  // Go backwards and age every element by one
  for (; pos > 0; --pos) {
    ages[pos - 1] = ages[pos - 1] + 1;
  }
  return report;
}

///\see dom::cache::CacheSetAnalysis<T>::update(const TagType tag, const
/// Classification assumption)
// 模拟LRU更新或者驱逐
template <CacheTraits *T>
LruMaxAgeUpdateReport<typename CacheTraits::TagType> *
LruMaxAgeAbstractCache<T>::update(AbstractAddress addr, AccessType load_store,
                                  AnaDeps *, bool wantReport,
                                  const Classification assumption) { // 为什么可以假设？
  WayType accessedAge = T->ASSOCIATIVITY;
  TagType tag = getTag<T>(addr);

  LruMaxAgeUpdateReport<TagType> *report = nullptr;
  if (wantReport) {
    report = new LruMaxAgeUpdateReport<TagType>;
  }

  // Search for tag
  unsigned pos;
  for (pos = 0; pos < size; ++pos)
    if (tags[pos] == tag) {
      accessedAge = ages[pos];
      break;
    }

  // In case of a cache miss
  if (accessedAge == T->ASSOCIATIVITY) {
    // an element will be added
    ++size;
    // But we actually assumed a hit
    if (assumption == CL_HIT || (T->LEVEL > 1 && assumption == CL2_HIT)) {
      // No evictions, age at most k-1
      assert(size <= T->ASSOCIATIVITY &&
             "Full cache and addr not in there, cannot assume a hit (illegal "
             "classification)");
      accessedAge = T->ASSOCIATIVITY - 1;
    } else {
      // elements with age A-1 get evicted
      while (pos > 0 && ages[pos - 1] == T->ASSOCIATIVITY - 1) {
        if (wantReport) {
          report->evictedElements.insert(tags[pos - 1]);
        }
        --size;
        --pos;
      }
    }
  }

  // Only if not direct-mapped
  if (T->ASSOCIATIVITY > 1) {
    // Go backwards and shift all entries to the right and update ages
    for (; pos > 0; --pos) {
      tags[pos] = tags[pos - 1];
      ages[pos] = ages[pos - 1] + (ages[pos - 1] < accessedAge ? 1 : 0);

      // Elements that were exacly one access younger than accessedAge
      // merge into set of elements with age accessedAge.
      // Hence, the merged set of tags could be unsorted.
      // Keep sorted.
      if (ages[pos] == accessedAge) {
        TagType currentTag = tags[pos];
        int i = pos;
        while (i < size - 1 && ages[i + 1] == accessedAge &&
               tags[i + 1] < currentTag) {
          tags[i] = tags[i + 1];
          ++i;
        }
        tags[i] = currentTag;
      }
    }
  }

  // Finally, insert the accessed tag at the front
  tags[0] = tag;
  ages[0] = 0;

  assert(size >= 0 && size <= T->ASSOCIATIVITY &&
         "Illegal must cache set size");
  return report;
}

///\see dom::cache::CacheSetAnalysis<T>::join(const Self& y)
// 就是经典的取上界
template <CacheTraits *T> void LruMaxAgeAbstractCache<T>::join(const Self &y) {
  std::vector<TagType> outTags(T->ASSOCIATIVITY);
  std::vector<WayType> outAges(T->ASSOCIATIVITY);
  int out = T->ASSOCIATIVITY - 1;
  int xIn = size - 1;
  int yIn = y.size - 1;// 从右往左扫

  while (xIn >= 0 || yIn >= 0) {
    // Select "greater" element
    bool xElemIsGreater =
        xIn >= 0 && (yIn == -1 || ages[xIn] > y.ages[yIn] ||
                     (ages[xIn] == y.ages[yIn] && tags[xIn] >= y.tags[yIn]));

    // Determine what and where to search
    std::vector<TagType>::const_iterator first;
    std::vector<TagType>::const_iterator last;
    TagType tag;
    WayType joinedAge;

    if (xElemIsGreater) {
      joinedAge = ages[xIn];
      tag = tags[xIn];
      first = y.tags.begin();
      last = y.tags.begin() + yIn + 1; // 从y里找同一个tag，其实对应到paper里的block了
      --xIn;
    } else {
      joinedAge = y.ages[yIn];
      tag = y.tags[yIn];
      first = tags.begin();
      last = tags.begin() + xIn + 1;
      --yIn;
    }

    // Search
    while (first != last)
      if (*first++ == tag) {
        outTags[out] = tag;
        outAges[out] = joinedAge;
        --out;
        break;
      }
      // 假设是x grater，这里的细节在于，如果y里无对应，x也是不能出现在join后缓存的
  }

  // Move elements to member variables.
  ++out;
  size = T->ASSOCIATIVITY - out;
  for (unsigned i = 0; i < size; ++i) { // 挪到前面的位置
    tags[i] = outTags[out + i];
    ages[i] = outAges[out + i];
  }
}

template <CacheTraits *T>
inline bool LruMaxAgeAbstractCache<T>::lessequal(const Self &y) const {
  Self copy(*this);
  copy.join(y);
  return copy == y;
}

///\see dom::cache::CacheSetAnalysis<T>::operator==(const Self& y) const
template <CacheTraits *T>
inline bool LruMaxAgeAbstractCache<T>::operator==(const Self &y) const {
  return size == y.size &&
         std::equal(tags.begin(), tags.begin() + size, y.tags.begin()) &&
         std::equal(ages.begin(), ages.begin() + size, y.ages.begin());
}

///\see dom::cache::CacheSetAnalysis<T>::operator<(const Self& y) const
template <CacheTraits *T>
inline bool LruMaxAgeAbstractCache<T>::operator<(const Self &y) const {
  if (size != y.size)
    return size < y.size;

  for (unsigned i = 0; i < size; ++i)
    if (ages[i] != y.ages[i])
      return ages[i] < y.ages[i];

  for (unsigned i = 0; i < size; ++i)
    if (tags[i] != y.tags[i])
      return tags[i] < y.tags[i];

  return false;
}

/////\see dom::cache::CacheSetAnalysis<T>::hash() const
// template <CacheTraits* T>
// std::size_t LruMaxAgeAbstractCache<T>::hash() const
//{
//	std::size_t res = static_cast<std::size_t>(2166136261UL);
//	for (unsigned i = 0; i < size; ++i) {
//		res ^= ((tags[i] << T::WAY_BITS) | ages[i]);
//		res *= static_cast<std::size_t>(16777619UL);
//	}
//	return res;
// }

///\see dom::cache::CacheSetAnalysis<T>::dump(std::ostream& os) const
template <CacheTraits *T>
std::ostream &LruMaxAgeAbstractCache<T>::dump(std::ostream &os) const {
  WayType pos = 0;

  os << "[";
  for (unsigned age = 0; age < T->ASSOCIATIVITY; ++age) {
    if (age != 0)
      os << ", ";

    os << "{";
    bool emitComma = false;
    while (pos < size && ages[pos] == age) {
      if (emitComma)
        os << ", ";
      printHex(os, (int)tags[pos]);
      ++pos;
      emitComma = true;
    }
    os << "}";
  }
  os << "]";

  return os;
}

///\see std::ostream& operator<<(std::ostream& os, const CacheSetAnalysis<T>& x)
template <CacheTraits *T>
inline std::ostream &operator<<(std::ostream &os,
                                const LruMaxAgeAbstractCache<T> &x) {
  return x.dump(os);
}

/**
 * Returns an upper bound on the age of \c tag
 */
template <CacheTraits *T>
unsigned LruMaxAgeAbstractCache<T>::getMaxAge(const TagType tag) const {
  for (unsigned i = 0; i < size; ++i)
    if (tags[i] == tag)
      return ages[i]; // 一旦找到直接返回
  return T->ASSOCIATIVITY; // TODO Should this return \infty?
}

template <CacheTraits *T>
unsigned
LruMaxAgeAbstractCache<T>::getNumberOfTagsWithMaxAge(int maxAge) const {
  unsigned res = 0;
  for (unsigned i = 0; i < size; ++i) {
    if (ages[i] == maxAge)
      ++res;
    if (ages[i] > maxAge)
      break;
  }
  return res;
}

template <CacheTraits *T>
ImplicitSet<typename CacheTraits::TagType>
LruMaxAgeAbstractCache<T>::getTagsWithMaxMaxAge(int maxAge) const {
  ImplicitSet<TagType> res;
  for (unsigned i = 0; i < size; ++i) {
    if (ages[i] > maxAge)
      break;
    res.insert(tags[i]);
  }
  return res;
}

/**
 * Compute the maximal size n of a stack S such that
 * - n <= maxStackSize (S is a sub-stack)
 * - |S| = n (S is concrete, it contains n elements)
 */
template <CacheTraits *T>
unsigned
LruMaxAgeAbstractCache<T>::getMaxConcreteSubStackSize(int maxStackSize) const {
  unsigned res = 0;
  for (unsigned i = 0; i < size; ++i) {
    if (ages[i] >= maxStackSize)
      break;
    // ages[] is sorted increasingly. If ages[i] == i, there are i-1 other tags
    // with age <= i.
    if (ages[i] == i)
      res = i + 1;
  }
  return res;
}

} // namespace cache
} // namespace dom

} // namespace TimingAnalysisPass

#endif /*LRUMAXAGEANALYSIS_H_*/
