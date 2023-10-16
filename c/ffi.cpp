#include <lean/lean.h>
#include <string.h>

extern "C" lean_obj_res mk_tac(lean_object* str)
{
  return str;
}

extern "C" lean_obj_res mk_step_tac(lean_object* name, lean_object* type, lean_object* tac)
{
  lean_obj_res obj =  lean_alloc_ctor(0, 3, 0);
  lean_ctor_set(obj, 0, name);
  lean_ctor_set(obj, 1, type);
  lean_ctor_set(obj, 2, tac);
  return obj;
}

extern "C" lean_obj_res mk_step_thm(lean_object* name, lean_object* type, lean_object* args)
{
  lean_obj_res obj = lean_alloc_ctor(1, 3, 1);
  lean_ctor_set(obj, 0, name);
  lean_ctor_set(obj, 1, type);
  lean_ctor_set(obj, 2, args);
  return obj;
}

extern "C" lean_obj_res mk_step_scope(lean_object* name, lean_object* type, lean_object* steps)
{
  lean_obj_res obj = lean_alloc_ctor(2, 3, 2);
  lean_ctor_set(obj, 0, name);
  lean_ctor_set(obj, 1, type);
  lean_ctor_set(obj, 2, steps);
  return obj;
}

extern "C" lean_obj_res mk_cvc5_proof(lean_object* steps)
{
  return steps;
}
