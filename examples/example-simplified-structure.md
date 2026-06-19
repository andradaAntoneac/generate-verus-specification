# Example Simplified Structure

## The structure's code from the implementation
```rust
use super::DoubleLinkedList;
use tests_api::TheAlloc;

struct Element<T> {
    next: u32,
    prec: u32,
    value: T,
}
pub struct Implementation<'x, T> {
    data: Vec<Option<Element<T>>, &'x TheAlloc>,
    free_list: Vec<u32>,
    first: u32,
    last: u32,
}
```

## The structure used for the Verus specification
```rust
pub struct Element<T> {
    pub next: u32,
    pub prec: u32,
    pub value: T,
}

pub struct DoublyLinkedList<T> {
    pub data: Vec<Option<Element<T>>>,
    pub free_list: Vec<u32>,
    pub first: u32,
    pub last: u32,
}
```