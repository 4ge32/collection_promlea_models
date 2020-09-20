#include <atomic>
#include <memory>

template <typename T> class lfstack {
private:
  struct node {
    std::shared_ptr<T> data;
    std::shared_ptr<node> next;
    node(T const &data_) : data(std::make_shared<T>(data_)) {}
  };
  std::shared_ptr<node> head;

public:
  void push(T const &data) {
    std::shared_ptr<node> const new_node = std::make_shared<node>(data);
    std::shared_ptr<node> old_head = std::atomic_load(&head);
    do {
      new_node->next = old_head;
    } while (!std::atomic_compare_exchange_weak(&head, &old_head, new_node));
  }
  std::shared_ptr<T> pop() {
    std::shared_ptr<node> old_head = std::atomic_load(&head);
    std::shared_ptr<node> new_head;
    do {
        if (old_head == nullptr) {
          return std::shared_ptr<T>();
        }
        new_head = old_head->next;
    } while (!std::atomic_compare_exchange_weak(&head, &old_head, new_head));
    return old_head->data;
  }
  ~lfstack() {
    while (pop())
      ;
  }
};
