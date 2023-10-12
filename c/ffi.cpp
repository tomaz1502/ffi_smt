#include <lean/lean.h>

extern "C" uint32_t my_add(uint32_t a, uint32_t b) {
    return a + b;
}

extern "C" lean_obj_res my_lean_fun() {
    return lean_io_result_mk_ok(lean_box(0));
}

extern "C" lean_obj_res my_foo(uint8_t ctor) {
  switch (ctor) {
    case 0: return lean_mk_string("foo"); break;
    case 1: return lean_mk_string("bar"); break;
    case 2: return lean_mk_string("baz"); break;
  }
  return lean_mk_string("bam");
}

extern "C" uint8_t my_bar(lean_obj_arg s) {
  if (lean_string_dec_eq(s, lean_mk_string("T.A")))
    return 0;
  if (lean_string_dec_eq(s, lean_mk_string("T.B")))
    return 1;
  if (lean_string_dec_eq(s, lean_mk_string("T.C")))
    return 2;
  return 0;
}
