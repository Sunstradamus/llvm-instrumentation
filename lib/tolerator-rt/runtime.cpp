//#include <vector>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <map>

extern "C" {


// This macro allows us to prefix strings so that they are less likely to
// conflict with existing symbol names in the examined programs.
// e.g. TOLERATE(entry) yields ToLeRaToR_entry
#define TOLERATE(X) ToLeRaToR_##X

std::map<char*, std::pair<uint64_t, bool>>* validMem;

void TOLERATE(helloworld)() {
  validMem = new std::map<char*, std::pair<uint64_t, bool>>();
  /*printf("==============================\n"
         "\tHello, World!\n"
         "==============================\n");*/
}

void TOLERATE(goodbyeworld)() {
  delete validMem;
  /*printf("==============================\n"
         "\tGoodbye, World!\n"
         "==============================\n");*/
}

void TOLERATE(logread)() {
  printf("FOUND: Invalid read from memory\n");
}

void TOLERATE(logwrite)() {
  printf("FOUND: Invalid write to memory\n");
}

void TOLERATE(logfree)() {
  printf("FOUND: Invalid free of memory\n");
}

void TOLERATE(logzero)() {
  printf("FOUND: Division by zero\n");
}

// ==========================================

void TOLERATE(PushGlobal)(char* addr, uint64_t size) {
  //printf("CALLED: addr %p, value %s, size %lu\n", (void*)addr, addr, size);
  (*validMem)[addr] = { size, false };
}

void TOLERATE(PushPtr)(char* addr, uint32_t count, uint64_t size) {
  //printf("CALLED: addr %p, value %X, width %lu, range %u\n", (void*)addr, *addr, size, count);
  (*validMem)[addr] = { size * count, false };
}

void TOLERATE(PopPtr)(char* addr, uint32_t count, uint64_t size) {
  //printf("CALLED: addr %p, value %X, width %lu, range %u\n", (void*)addr, *addr, size, count);
  validMem->erase(addr);
}

void TOLERATE(PostMalloc)(char* addr, uint64_t size) {
  //printf("MALLOC: addr %p, range %lu\n", (void*)addr, size);
  (*validMem)[addr] = { size, true };
}

bool TOLERATE(IsValidPtr)(char* addr, uint64_t size) {
  auto res = validMem->lower_bound(addr);
  char* validAddr = res->first;
  //uint64_t range = res->second;
  std::pair<uint64_t, bool> range = res->second;
  bool ret = false;
  // If starts match, and read size <= alloc'd ptr size
  if (validAddr == addr && size <= range.first) {
    ret = true;
  }
  // Overshot, check previous entry
  if (validAddr > addr || (res == validMem->end())) {
    validAddr = (--res)->first;
    range = res->second;
    if ((validAddr <= addr) && (addr <= validAddr+range.first) && (addr+size <= validAddr+range.first)) {
      ret = true;
    }
  }
  //printf("FETCH: addr %p, range %lu\n", (void*)addr, size);
  //printf("FOUND: addr %p, range %lu\n", (void*)validAddr, range);
  //printf("RESULT: %d\n", ret);
  return ret;
}

bool TOLERATE(IsValidFree)(char* addr) {
  //printf("FREE: addr %p\n", (void*)addr);
  auto search = validMem->find(addr);
  return (search != validMem->end() && search->second.second);
}

void TOLERATE(MyFree)(char* addr) {
  //printf("MYFREE: addr %p\n", (void*)addr);
  if (TOLERATE(IsValidFree)(addr)) {
    // probably also poison malloc'd memory
    validMem->erase(addr);
    free(addr);
  }
}

}
