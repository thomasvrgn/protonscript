declare function malloc<T>(size: number): Ref<T>;
interface List<T> {
  head: T;
  tail: Ref<List<T>>;
}

function map<T, U>(f: (x: T) => U, list: List<T>): List<U> {
  if (list.tail == null) {
    return { head: f(list.head), tail: null };
  }
  let head: U = f(list.head);
  let tail = malloc(sizeof List<U>);
  *tail = map(f, *list.tail);
  return { head: head, tail: null };
}

function callback(x: string) {
  printf(x)
  return printf("\n")
}

function makeList<T>(head: T, tail: Ref<List<T>>): Ref<List<T>> {
  let list: Ref<List<T>> = malloc(sizeof List<T>);
  *list = { head: head, tail: tail };
  return list;
}

function main(): number {

  printf(lst[0])
  let x = makeList("test", makeList("bruh", makeList("hello", null)));
  map(callback, *x);
  printf(lst[0])
  return 0;
}