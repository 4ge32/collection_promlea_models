#include "lfq.h"
#include <algorithm>
#include <atomic>
#include <iostream>
#include <mutex>
#include <thread>
#include <unistd.h>
#include <vector>

#define all(x) begin(x), end(x)

using namespace std;
using ll = long long;

const static unsigned int producer = 50;
const static unsigned int consumer = 10;
vector<long> result;

const long mmax = 4000000;
long MEM[mmax];
static std::atomic<long> val(0);

void producer_func(int arg) {
  const unsigned long num = mmax / producer;
  for (unsigned long i = 0; i < num; ++i) {
  again:
    int32_t ret = enqueue(i + (num * arg));
    if (ret == -1) {
      goto again;
    }
  }
}

std::mutex mtx;
void consumer_func(void) {
start:
  long int old = val.fetch_add(1);
  long res = -1;
  if (old < mmax) {
    while (res < 0) {
      res = dequeue();
      if (res == -1) {
        usleep(10);
      }
    }

    MEM[old] = res;
    goto start;
  }
}

int main() {
  vector<thread> pro;
  vector<thread> con;

  lfq_init();
  int res = 0;

  cout << "\nPOP" << endl;
  res = dequeue();
  cout << res << endl;
  con_();

  cout << "\nPOP" << endl;
  res = dequeue();
  cout << res << endl;
  con_();

  cout << "\nPUSH" << endl;
  res = enqueue(1);
  cout << res << endl;
  con_();

  cout << "\nPUSH" << endl;
  res = enqueue(2);
  cout << res << endl;
  con_();

  cout << "\nPOP" << endl;
  res = dequeue();
  cout << res << endl;
  con_();

  cout << "\nPOP" << endl;
  res = dequeue();
  cout << res << endl;
  con_();

  cout << "\nPOP" << endl;
  res = dequeue();
  cout << res << endl;
  con_();

  cout << endl;

  // return 0;
  std::chrono::system_clock::time_point start, end;

  start = std::chrono::system_clock::now();

  cout << producer << ": producers start" << endl;
  cout << consumer << ": consumers start" << endl;

  for (auto i = 0U; i < producer; ++i) {
    pro.push_back(thread(producer_func, i));
  }
  for (auto i = 0U; i < consumer; ++i) {
    con.push_back(thread(consumer_func));
  }

  for (auto &p : pro) {
    p.join();
  }
  for (auto &c : con) {
    c.join();
  }
  for (int i = 0; i < mmax; ++i) {
    result.push_back(MEM[i]);
  }

  end = std::chrono::system_clock::now();
  double elapsed =
      std::chrono::duration_cast<std::chrono::milliseconds>(end - start)
          .count();

  cout << producer << ": producers finish" << endl;
  cout << consumer << ": consumers finish" << endl;
  cout << "Elapsed: " << elapsed << endl;

  sort(result.begin(), result.end());
  long old = -1;
  for (auto r : result) {
    if (r == old) {
      cout << "ERROR" << endl;
      cout << r << ":" << old << endl;
      break;
    }
    old = r;
  }
  con_();
  cout << "Last: " << old << endl;
  cout << "DONE" << endl;
}
