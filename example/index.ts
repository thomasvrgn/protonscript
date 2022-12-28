import { malloc } from "./stdlib";
interface List<T> {
  head: T;
  tail: Ref<List<T>>;
}

interface Closure<E, F> {
  env: E;
  func: F;
}

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

function test(x) {
  return printf("%s ", x);
}

function main(): number {
  let x = makeList("test", makeList("bruh", makeList("hello", null)));
  map(test, *x);
  return 0;
}