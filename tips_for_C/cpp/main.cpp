#include "lfstack.hpp"
#include <thread>
#include <vector>
#include <algorithm>
#include <iostream>

int main() {
  const int tnum = 1000;
  std::vector<std::thread> producer;
  std::vector<std::thread> consumer;
  std::vector<int> res(tnum * tnum);
  lfstack<int> lfs;

  for (int i = 0; i < tnum; ++i) {
    consumer.push_back(std::thread([&lfs, &res, i] {
      const int id = i * tnum;
      for (int j = 0; j < tnum; ++j) {
        std::shared_ptr<int> data;
        do {
          data = lfs.pop();
          if (data != nullptr) {
            break;
          }
        } while (1);
        res[*data] = id + j;
      }
    }));
  }

  for (int i = 0; i < tnum; ++i) {
    producer.push_back(std::thread([&lfs, i] {
      const int id = i * tnum;
      for (int j = 0; j < tnum; ++j) {
        lfs.push(id + j);
      }
    }));
  }

  for (auto &p : producer) {
    p.join();
  }

  for (auto &c : consumer) {
    c.join();
  }

  std::sort(res.begin(), res.end());
  std::unique(res.begin(), res.end());
  for (int i = 0; i < tnum * tnum; ++i) {
      if (i != res[i]) {
          std::cout << "broken!" << std::endl;
          break;
      }
  }
}
