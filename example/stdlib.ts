export declare function malloc<T>(size: number): Ref<T>;
export interface List<T> {
  head: T;
  tail: Ref<List<T>>;
}
export interface Closure<E, F> {
  env: E;
  fun: F;
}

function makeList(test: number): Ref<List<number>> {
  let list: Ref<List<number>> = malloc(sizeof List<number>);
  *list = { head: test, tail: null };
  return list;
}