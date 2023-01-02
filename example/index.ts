import { malloc, List } from "./stdlib";

function map<T, U>(f: (x: T) => U, list: List<T>): List<U> {
  if (list.tail == null) {
    return { head: f(list.head), tail: null };
  }
  let head = f(list.head);
  let tail = malloc(sizeof List<U>);
  *tail = map(f, *list.tail);
  return { head: head, tail: null };
}

function makeList<T>(head: T, tail: Ref<List<T>>): Ref<List<T>> {
  let list: Ref<List<T>> = malloc(sizeof List<T>);
  *list = { head: head, tail: tail };
  return list;
}

function main(): number {
  let x = makeList(8, makeList(9, makeList(10, null)));
  let add = (x, y) => x + y;
  let sub = (x) => (y) => x - y;
  map((x) => printf("%d ", add(x, sub(x)(1))), *x);
  printf("%d\n", sub(5)(add(1, 2)));
  return 0;
}