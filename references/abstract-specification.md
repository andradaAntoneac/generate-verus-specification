# Abstract Specification (DLL)

Specifying a DLL as an abstract data type (ADT) is challenging because, in
practice, DLLs are typically used to implement other ADTs rather than being
defined as one themselves.

## Operations in the ADT
- **Insertion**: Add a new element (front, back, or a specific position).
- **Deletion**: Remove an element (front, back, or a specific position).
- **Traversal**: Iterate forward or backward through elements.
- **Search**: Find a specific element and return its position.
- **Accessing**: Refer to individual elements.
- **Size**: Return the current number of elements.
- **Emptiness**: Indicate whether the list is empty.

This specification is an intermediate level of abstraction.

## Semi-formal abstract description
A standard DLL `L` is either the empty list (`L.emptylist() = true`) or a
collection of nodes with these properties:
- Each node `N` is uniquely referred to by an identifier `id`, written
  `id -> N`.
- There is a first node `L.first()`.
- There is a last node `L.last()`.
- Each node `id -> N`, different from the first one, has a unique immediate
  predecessor `L.pred(id)`.
- Each node `id -> N`, different from the last one, has a unique immediate
  successor `L.suc(id)`.
- Each node `id -> N` stores a value `L.val(id)`.

Let `NodeId` denote the type of identifiers, and `T` the type of values stored
in nodes.

We specify the operations as a trait, using a semi-formal specification
language where each method lists:
- Input parameters
- Output parameters (if any)
- Return value (if any)

We use `p'` for the output value of parameter `p`. The trait-based approach
aligns with idiomatic Rust: behavior is defined independently of the underlying
memory representation.

Because the operation specifications are mutually recursive, they depend on
each other. Correctness cannot be established for any single operation in
isolation. The entire list implementation must be verified as a whole.

Below are the core operations used in our experiments.

### Next
Returns the node immediately after a given node in forward traversal. If the
list is empty or the given node is the last one, it returns `None`.

```
next(NodeId id_t): NodeId
Input
  self: the current list
  id_t: the target node in self
Output
  unchanged
Return
  if self.is_empty() or id_t = self.last()
  then None
  else id s.t. self.prec(id) = id_t
```

### Prec
Returns the node immediately before a given node. If the list is empty or the
given node is the first one, it returns `None`.

```
prec(NodeId id_t): NodeId
Input
  self: the current list
  id_t: the target node in self
Output
  unchanged
Return
  if self.is_empty() or id_t = self.first()
  then None
  else id s.t. self.next(id) = id_t
```

### Push_back
Adds a new node as the last one and stores a given value in it. If the list is
empty, the new node is also the first one.

```
push_back(T value): NodeId
Input
  self: the current list
  value: a T object
Output
  self' = self ⊎ {id_new -> N}
  self'.last() = id_new
  self'.next(id_new) = None
  self'.value(id_new) = value
  if self.is_empty() then
    self'.first() = id_new
    self'.prec(id_new) = None
  else self'.prec(id_new) = self.last()
Return
  id_new
```

### Push_front
Adds a new node as the first one and stores a given value in it. If the list is
empty, the new node is also the last one.

```
push_front(T value): NodeId
Input
  self: the current list
  value: a T object
Output
  self' = self ⊎ {id_new -> N}
  self'.value(id_new) = value
  self'.prec(id_new) = None
  self'.first() = id_new
  if self.is_empty() then
    self'.last() = id_new
    self'.next(id_new) = None
  else self'.next(id_new) = self.first()
Return
  id_new
```

### Insert_before
Adds a new node as the predecessor of a given node and stores a given value in
it. The given node becomes the next one for the new node. If the given node is
the first one, the new node takes its place.

```
insert_before(T value, NodeId id_t): NodeId
Input
  self: the current list
  value: a T object
  id_t: the target node in self
Output
  self' = self ⊎ {id_new -> N}
  self'.value(id_new) = value
  self'.next(id_new) = id_t
  self'.prec(id_t) = id_new
  if self.first() = id_t then
    self'.first() = id_new
    self'.prec(id_new) = None
  else self'.prec(id_new) = self.prec(id_t)
    self'.next(self.prec(id_t)) = id_new
Return
  id_new
```

### Insert_after
Adds a new node as the successor of a given node and stores a given value in it.
The given node becomes the predecessor for the new node. If the given node is
the last one, the new node takes its place.

```
insert_after(T value, NodeId id_t): NodeId
Input
  self: the current list
  value: the value to be inserted
  id_t: id of the target node after which the new value is inserted
Output
  self' = self ⊎ {id_new -> N}
  self'.value(id_new) = value
  self'.prec(id_new) = id_t
  self'.next(id_t) = id_new
  if self.last() = id_t then
    self'.last() = id_new
    self'.next(id_new) = None
  else self'.next(id_new) = self.next(id_t)
    self'.prec(self.next(id_t)) = id_new
Return
  id_new
```

### Deletion
Deletes a given node from the list. The predecessor (if any) becomes the
predecessor of the next node. The successor (if any) becomes the successor of
the predecessor. If the given node is the first/last one, the corresponding
reference is updated.

```
delete(NodeId id): void
Input
  self: the current list
  id: a node in self
Output
  self' = self \ {id -> N}
  if self.first() = id and self.last() = id then
      self'.first() = None
      self'.last() = None
      self'.is_empty() = true
  else if self.first() = id then
      self'.first() = self.next(id)
  else if self.last() = id then
      self'.last() = self.prec(id)
  else
      self'.next(self.prec(id)) = self.next(id)
      self'.prec(self.next(id)) = self.prec(id)
Return
  nothing
```

### Search
Given a value, search the list for a node that stores that value. If such a node
exists, return its position; otherwise return `None`.

```
search(T value): NodeId
Input
  self: the current list
  value: a T object to be searched for
Output
  self' = self
Return
  if exists id in self such that self.value(id) = value
      then id
  else None
```
