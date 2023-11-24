#include <cvc5/cvc5.h>
#include <cvc5/cvc5_parser.h>
#include <lean/lean.h>

#include <iostream>

using namespace cvc5;

lean_obj_res mk_option_none() { return lean_box(0); }

lean_obj_res mk_option_some(lean_obj_arg val)
{
  lean_obj_res obj = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(obj, 0, val);
  return obj;
}

lean_obj_res mk_list_nil() { return lean_box(0); }

lean_obj_res mk_list_cons(lean_obj_arg head, lean_obj_arg tail)
{
  lean_obj_res obj = lean_alloc_ctor(1, 2, 0);
  lean_ctor_set(obj, 0, head);
  lean_ctor_set(obj, 1, tail);
  return obj;
}

lean_obj_res mk_name_anonymous() { return lean_box(0); }

lean_obj_res mk_name_str(lean_obj_arg pre, const char* name)
{
  lean_object* lname = lean_mk_string(name);
  lean_obj_res obj = lean_alloc_ctor(1, 2, 0);
  lean_ctor_set(obj, 0, pre);
  lean_ctor_set(obj, 1, lname);
  return obj;
}

lean_obj_res mk_name_string(const char* name)
{
  lean_object* anonymous = mk_name_anonymous();
  lean_object* lname = lean_mk_string(name);
  lean_obj_res obj = lean_alloc_ctor(1, 2, 0);
  lean_ctor_set(obj, 0, anonymous);
  lean_ctor_set(obj, 1, lname);
  return obj;
}

lean_obj_res mk_fvarId(lean_obj_arg name) { return name; }

lean_obj_res mk_level_zero() { return lean_box(0); }

lean_obj_res mk_level_succ(lean_obj_arg lvl)
{
  lean_obj_res obj = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(obj, 0, lvl);
  return obj;
}

lean_obj_res mk_level_one() { return (mk_level_succ(mk_level_zero())); }

lean_obj_res mk_binderInfo_default() { return lean_box(0); }

lean_obj_res mk_expr_fvar(lean_obj_arg name)
{
  lean_obj_res obj = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(obj, 0, mk_fvarId(name));
  return obj;
}

lean_obj_res mk_expr_const(lean_obj_arg name, lean_obj_arg us)
{
  lean_obj_res obj = lean_alloc_ctor(4, 2, 0);
  lean_ctor_set(obj, 0, name);
  lean_ctor_set(obj, 1, us);
  return obj;
}

lean_obj_res mk_expr_app(lean_obj_arg fn, lean_obj_arg arg)
{
  lean_obj_res obj = lean_alloc_ctor(5, 2, 0);
  lean_ctor_set(obj, 0, fn);
  lean_ctor_set(obj, 1, arg);
  return obj;
}

lean_obj_res mk_expr_forallE(lean_obj_arg name,
                             lean_obj_arg type,
                             lean_obj_arg body,
                             lean_obj_arg info)
{
  lean_obj_res obj = lean_alloc_ctor(7, 4, 0);
  lean_ctor_set(obj, 0, name);
  lean_ctor_set(obj, 1, type);
  lean_ctor_set(obj, 2, body);
  lean_ctor_set(obj, 3, info);
  return obj;
}

lean_obj_res mk_expr_app_n(lean_obj_arg f,
                           const std::vector<lean_obj_arg>& args)
{
  lean_object* e = f;
  for (const lean_obj_arg& arg : args)
  {
    e = mk_expr_app(e, arg);
  }
  return e;
}

lean_obj_res mk_tac_eval() { return lean_box(0); }

lean_obj_res mk_tac_rewrite(lean_obj_arg assoc,
                            lean_obj_arg null,
                            lean_obj_arg rule,
                            lean_obj_arg args)
{
  lean_obj_res obj = lean_alloc_ctor(1, 4, 0);
  lean_ctor_set(obj, 0, assoc);
  lean_ctor_set(obj, 1, null);
  lean_ctor_set(obj, 2, rule);
  lean_ctor_set(obj, 3, args);
  return obj;
}

lean_obj_res mk_tac_andElim(lean_obj_arg a, lean_obj_arg i)
{
  lean_obj_res obj = lean_alloc_ctor(2, 2, 0);
  lean_ctor_set(obj, 0, a);
  lean_ctor_set(obj, 1, i);
  return obj;
}

lean_obj_res mk_tac_r0(lean_obj_arg h1,
                       lean_obj_arg h2,
                       lean_obj_arg pivot,
                       lean_obj_arg i1,
                       lean_obj_arg i2)
{
  lean_obj_res obj = lean_alloc_ctor(3, 5, 0);
  lean_ctor_set(obj, 0, h1);
  lean_ctor_set(obj, 1, h2);
  lean_ctor_set(obj, 2, pivot);
  lean_ctor_set(obj, 3, i1);
  lean_ctor_set(obj, 4, i2);
  return obj;
}

lean_obj_res mk_tac_r1(lean_obj_arg h1,
                       lean_obj_arg h2,
                       lean_obj_arg pivot,
                       lean_obj_arg i1,
                       lean_obj_arg i2)
{
  lean_obj_res obj = lean_alloc_ctor(4, 5, 0);
  lean_ctor_set(obj, 0, h1);
  lean_ctor_set(obj, 1, h2);
  lean_ctor_set(obj, 2, pivot);
  lean_ctor_set(obj, 3, i1);
  lean_ctor_set(obj, 4, i2);
  return obj;
}

lean_obj_res mk_tac_cong(lean_obj_arg as)
{
  lean_obj_res obj = lean_alloc_ctor(5, 1, 0);
  lean_ctor_set(obj, 0, as);
  return obj;
}

lean_obj_res mk_step_thm(const char* name, lean_obj_arg type, lean_obj_arg val)
{
  lean_object* lname = mk_name_string(name);
  lean_obj_res obj = lean_alloc_ctor(0, 3, 0);
  lean_ctor_set(obj, 0, lname);
  lean_ctor_set(obj, 1, type);
  lean_ctor_set(obj, 2, val);
  return obj;
}

lean_obj_res mk_step_tac(const char* name, lean_obj_arg type, lean_obj_arg tac)
{
  lean_object* lname = mk_name_string(name);
  lean_obj_res obj = lean_alloc_ctor(1, 3, 0);
  lean_ctor_set(obj, 0, lname);
  lean_ctor_set(obj, 1, type);
  lean_ctor_set(obj, 2, tac);
  return obj;
}

lean_obj_res mk_step_scope(const char* name,
                           lean_obj_arg type,
                           lean_obj_arg assums,
                           lean_obj_arg steps,
                           const char* main)
{
  lean_object* lname = mk_name_string(name);
  lean_object* lmain = mk_name_string(main);
  lean_obj_res obj = lean_alloc_ctor(2, 5, 0);
  lean_ctor_set(obj, 0, lname);
  lean_ctor_set(obj, 1, type);
  lean_ctor_set(obj, 2, assums);
  lean_ctor_set(obj, 3, steps);
  lean_ctor_set(obj, 4, lmain);
  return obj;
}

lean_obj_res mk_step_trust(const char* name, lean_obj_arg type)
{
  lean_object* lname = mk_name_string(name);
  lean_obj_res obj = lean_alloc_ctor(3, 2, 0);
  lean_ctor_set(obj, 0, lname);
  lean_ctor_set(obj, 1, type);
  return obj;
}

lean_obj_res mk_proof(lean_obj_arg steps) { return steps; }

lean_obj_res process_term(const Term& t);

lean_obj_res left_assoc_op(lean_obj_arg op,
                           cvc5::Term::const_iterator begin,
                           cvc5::Term::const_iterator end)
{
  lean_object* curr = process_term(*begin);
  auto it = ++begin;
  while (it != end)
  {
    curr = mk_expr_app(mk_expr_app(op, curr), process_term(*it));
    ++it;
  }
  return curr;
}

lean_obj_res left_assoc_op_proof(lean_obj_arg op,
                                 cvc5::Term::const_iterator begin,
                                 cvc5::Term::const_iterator end)
{
  lean_object* curr = process_term(*begin);
  auto it = ++begin;
  while (it != end)
  {
    curr = mk_expr_app(mk_expr_app(op, curr), process_term(*it));
    ++it;
  }
  return curr;
}

lean_obj_res process_sort(const Sort& s)
{
  switch (s.getKind())
  {
    case SortKind::BOOLEAN_SORT:
    {
      return mk_expr_const(mk_name_string("Prop"), mk_list_nil());
    }
    case SortKind::INTERNAL_SORT_KIND:
    case SortKind::UNINTERPRETED_SORT:
    {
      return mk_expr_const(mk_name_string(s.toString().c_str()), mk_list_nil());
    }
    case SortKind::INTEGER_SORT:
    {
      return mk_expr_const(mk_name_string("Int"), mk_list_nil());
    }
    case SortKind::REAL_SORT:
    {
      return mk_expr_const(mk_name_string("Rat"), mk_list_nil());
    }
    default:
    {
      return mk_expr_const(mk_name_string("sorry"), mk_list_nil());
    }
  }
}

lean_obj_res process_term(const Term& t)
{
  switch (t.getKind())
  {
    case Kind::CONSTANT:
    {
      return mk_expr_fvar(mk_name_string(t.toString().c_str()));
    }
    case Kind::CONST_BOOLEAN:
    {
      return mk_expr_const(
          mk_name_string(t.getBooleanValue() ? "True" : "False"),
          mk_list_nil());
    }
    case Kind::NOT:
    {
      return mk_expr_app(mk_expr_const(mk_name_string("Not"), mk_list_nil()),
                         process_term(t[0]));
    }
    case Kind::AND:
    {
      lean_object* op = mk_expr_const(mk_name_string("And"), mk_list_nil());
      lean_inc_n(op, t.getNumChildren() - 1);
      return left_assoc_op(op, t.begin(), t.end());
    }
    case Kind::OR:
    {
      lean_object* op = mk_expr_const(mk_name_string("Or"), mk_list_nil());
      lean_inc_n(op, t.getNumChildren() - 1);
      return left_assoc_op(op, t.begin(), t.end());
    }
    case Kind::IMPLIES:
    {
      lean_object* curr = process_term(*t.end());
      for (size_t i = t.getNumChildren() - 2; i >= 0; --i)
      {
        curr = mk_expr_forallE(mk_name_anonymous(),
                               process_term(t[i]),
                               curr,
                               mk_binderInfo_default());
      }
      return curr;
    }
    case Kind::EQUAL:
    {
      return mk_expr_app(
          mk_expr_app(mk_expr_app(mk_expr_const(mk_name_string("Eq"),
                                                mk_list_cons(mk_level_one(),
                                                             mk_list_nil())),
                                  process_sort(t[0].getSort())),
                      process_term(t[0])),
          process_term(t[1]));
    }
    case Kind::DISTINCT:
    {
      return mk_expr_app(
          mk_expr_app(mk_expr_app(mk_expr_const(mk_name_string("Ne"),
                                                mk_list_cons(mk_level_one(),
                                                             mk_list_nil())),
                                  process_sort(t[0].getSort())),
                      process_term(t[0])),
          process_term(t[1]));
    }
    case Kind::APPLY_UF:
    {
      lean_object* curr = process_term(*t.begin());
      auto it = ++t.begin();
      while (it != t.end())
      {
        curr = mk_expr_app(curr, process_term(*it));
        ++it;
      }
      return curr;
    }
    default:
    {
      std::cout << t.getKind() << ": " << t << std::endl;
      return mk_expr_const(mk_name_string("sorry"), mk_list_nil());
    }
  }
}

Term getLastDiff(Term clause, Term pivot)
{
  for (size_t size = clause.getNumChildren(), i = size; i > 0; --i)
  {
    if (clause[i - 1] != pivot)
    {
      return clause[i - 1];
    }
  }
  return Term();
}

Term getLastDiffs(Term clause, Term pivot1, Term pivot2)
{
  for (size_t size = clause.getNumChildren(), i = size; i > 0; --i)
  {
    if (clause[i - 1] != pivot1 && clause[i - 1] != pivot2)
    {
      return clause[i - 1];
    }
  }
  return Term();
}

Term getSingletonPosition(Solver& slv,
                          Term clause,
                          size_t pos,
                          const std::vector<Term>& pivots)
{
  if (clause.getKind() != Kind::OR
      || (pivots[2 * (pos - 1)] == slv.mkBoolean(false)
          && pivots[2 * (pos - 1) + 1] == clause))
  {
    return slv.mkInteger(0);
  }
  if (clause[clause.getNumChildren() - 1].getKind() == Kind::OR)
  {
    return slv.mkInteger(clause.getNumChildren() - 1);
  }
  return slv.mkInteger(-1);
}

void process_rewrite(Solver& slv,
                     const cvc5::Proof& p,
                     std::unordered_map<Term, std::string>& tMap,
                     std::unordered_map<Proof, std::string>& pMap,
                     lean_obj_arg& steps)
{
  if (pMap.find(p) != pMap.cend())
  {
    return;
  }
  switch (p.getArguments()[0].getUInt32Value())
  {
    case 36U:
    {
      pMap[p] = "s" + std::to_string(tMap.size() + pMap.size());
      lean_object* val = mk_expr_app(
          mk_expr_const(mk_name_string("bool_eq_true"), mk_list_nil()),
          process_term(p.getArguments()[1]));
      steps = lean_array_push(
          steps,
          mk_step_thm(pMap[p].c_str(), process_term(p.getResult()), val));
      break;
    }
    case 48U:
    {
      pMap[p] = "s" + std::to_string(tMap.size() + pMap.size());
      lean_object* assoc =
          mk_expr_const(mk_name_string("and_assoc_eq"), mk_list_nil());
      lean_object* null =
          mk_expr_const(mk_name_string("and_true"), mk_list_nil());
      lean_object* rule =
          mk_expr_const(mk_name_string("bool_and_true"), mk_list_nil());
      lean_object* args = lean_mk_empty_array();
      const std::vector<Term> pargs = p.getArguments();
      for (size_t i = 1; i < pargs.size(); ++i)
      {
        lean_object* arg = lean_mk_empty_array();
        for (const Term& t : pargs[i])
        {
          arg = lean_array_push(arg, process_term(t));
        }
        args = lean_array_push(args, arg);
      }
      lean_object* tac = mk_tac_rewrite(assoc, null, rule, args);
      steps = lean_array_push(
          steps,
          mk_step_tac(pMap[p].c_str(), process_term(p.getResult()), tac));
      break;
    }
    case 305U:
    {
      pMap[p] = "s" + std::to_string(tMap.size() + pMap.size());
      lean_object* levels = mk_list_cons(mk_level_one(), mk_list_nil());
      lean_object* val = mk_expr_app(
          mk_expr_app(mk_expr_const(mk_name_string("eq_refl"), levels),
                      process_sort(p.getResult()[0].getSort())),
          process_term(p.getArguments()[1]));
      steps = lean_array_push(
          steps,
          mk_step_thm(pMap[p].c_str(), process_term(p.getResult()), val));
      break;
    }
    case 307U:
    {
      pMap[p] = "s" + std::to_string(tMap.size() + pMap.size());
      lean_object* levels = mk_list_cons(mk_level_one(), mk_list_nil());
      lean_object* val = mk_expr_app(
          mk_expr_app(
              mk_expr_app(
                  mk_expr_const(mk_name_string("distinct_binary_elim"), levels),
                  process_sort(p.getResult()[0].getSort())),
              process_term(p.getArguments()[1])),
          process_term(p.getArguments()[2]));
      steps = lean_array_push(
          steps,
          mk_step_thm(pMap[p].c_str(), process_term(p.getResult()), val));
      break;
    }
    default:
    {
      std::cout << slv.proofToString(p) << std::endl;
      pMap[p] = "s" + std::to_string(tMap.size() + pMap.size());
      steps = lean_array_push(
          steps, mk_step_trust(pMap[p].c_str(), process_term(p.getResult())));
      break;
    }
  }
}

void process_step(Solver& slv,
                  const cvc5::Proof& p,
                  std::unordered_map<Term, std::string>& tMap,
                  std::unordered_map<Proof, std::string>& pMap,
                  lean_obj_arg& steps)
{
  if (pMap.find(p) != pMap.cend())
  {
    return;
  }
  switch (p.getRule())
  {
    case ProofRule::SCOPE:
    {
      std::unordered_map<Term, std::string> ctMap;
      ctMap.insert(tMap.cbegin(), tMap.cend());
      std::unordered_map<Proof, std::string> cpMap;
      cpMap.insert(pMap.cbegin(), pMap.cend());
      lean_object* cAssums = lean_mk_empty_array();
      lean_object* cSteps = lean_mk_empty_array();
      std::vector<cvc5::Term> args = p.getArguments();
      for (const cvc5::Term& arg : args)
      {
        ctMap[arg] = "a" + std::to_string(ctMap.size() + cpMap.size());
        cAssums = lean_array_push(cAssums, mk_name_string(ctMap[arg].c_str()));
      }
      process_step(slv, p.getChildren()[0], ctMap, cpMap, cSteps);
      pMap[p] = "s" + std::to_string(tMap.size() + pMap.size());
      steps = lean_array_push(steps,
                              mk_step_scope(pMap[p].c_str(),
                                            process_term(p.getResult()),
                                            cAssums,
                                            cSteps,
                                            cpMap[p.getChildren()[0]].c_str()));
      break;
    }
    case ProofRule::ASSUME:
    {
      pMap[p] = tMap[p.getArguments()[0]];
      break;
    }
    case ProofRule::AND_ELIM:
    {
      process_step(slv, p.getChildren()[0], tMap, pMap, steps);
      pMap[p] = "s" + std::to_string(tMap.size() + pMap.size());
      steps = lean_array_push(
          steps,
          mk_step_tac(pMap[p].c_str(),
                      process_term(p.getResult()),
                      mk_tac_andElim(
                          mk_name_string(pMap[p.getChildren()[0]].c_str()),
                          lean_cstr_to_nat(
                              p.getArguments()[0].getIntegerValue().c_str()))));
      break;
    }
    case ProofRule::AND_INTRO:
    {
      const std::vector<Proof> children = p.getChildren();
      for (const Proof& cp : children)
      {
        process_step(slv, cp, tMap, pMap, steps);
      }
      size_t c = tMap.size() + pMap.size();
      std::string currName = pMap[children[0]];
      Term curr = children[0].getResult();
      lean_object* thm = mk_expr_const(
          mk_name_str(mk_name_string("And"), "intro"), mk_list_nil());
      lean_inc_n(thm, children.size() - 2);
      for (size_t i = 1; i < children.size(); ++i)
      {
        std::string newName = "s" + std::to_string(c) + "s" + std::to_string(i);
        lean_object* val = mk_expr_app(
            mk_expr_app(mk_expr_app(mk_expr_app(thm, process_term(curr)),
                                    process_term(children[i].getResult())),
                        mk_expr_fvar(mk_name_string(currName.c_str()))),
            mk_expr_fvar(mk_name_string(pMap[children[i]].c_str())));
        curr = curr.andTerm(children[i].getResult());
        steps = lean_array_push(
            steps, mk_step_thm(newName.c_str(), process_term(curr), val));
        currName = newName;
      }
      pMap[p] = currName;
      break;
    }
    case ProofRule::RESOLUTION:
    case ProofRule::CHAIN_RESOLUTION:
    {
      std::vector<Term> children;
      const std::vector<Term> args = p.getArguments();
      const Term res = p.getResult();
      for (const Proof& cp : p.getChildren())
      {
        process_step(slv, cp, tMap, pMap, steps);
        children.push_back(cp.getResult());
      }
      std::string currName = pMap[p.getChildren()[0]];
      size_t c = tMap.size() + pMap.size();
      Term cur = children[0], curLastLit;
      Term minusOne = slv.mkInteger(-1), zero = slv.mkInteger(0);
      size_t numCurLits = 0;
      std::vector<Term> singletons{minusOne, minusOne};
      std::vector<bool> ithPremiseSingleton(children.size());
      // Whether child 0 is a singleton list. The first child is used as an OR
      // non-singleton clause if it is not equal to its pivot L_1. Since it's
      // the first clause in the resolution it can only be equal to the pivot in
      // the case the polarity is true.
      if (children[0].getKind() != Kind::OR
          || (args[0] == slv.mkBoolean(true) && children[0] == args[1]))
      {
        singletons[0] = zero;
        curLastLit = children[0];
        numCurLits = 1;
        ithPremiseSingleton[0] = true;
      }
      else
      {
        ithPremiseSingleton[0] = false;
        numCurLits = children[0].getNumChildren();
        curLastLit = children[0][numCurLits - 1];
        if (curLastLit.getKind() == Kind::OR)
        {
          singletons[0] = slv.mkInteger(numCurLits - 1);
        }
      }
      // For all other children C_i the procedure is simliar. There is however a
      // key difference in the choice of the pivot element which is now the
      // L_{i-1}, i.e. the pivot of the child with the result of the i-1
      // resolution steps between the children before it. Therefore, if the
      // policy id_{i-1} is true, the pivot has to appear negated in the child
      // in which case it should not be a [(or F1 ... Fn)] node. The same is
      // true if it isn't the pivot element.
      for (size_t i = 1, size = children.size(); i < size; ++i)
      {
        singletons[1] = getSingletonPosition(slv, children[i], i, args);
        ithPremiseSingleton[i] = singletons[1] == zero;
        if (i < size - 1)
        {
          // create a (unique) placeholder for the resulting binary
          // resolution. The placeholder is [res, i, pol, pivot], where pol and
          // pivot are relative to this part of the chain resolution
          Term pol = args[(i - 1) * 2];
          // std::vector<Term> curArgs{d_lnc.convert(args[(i - 1) * 2 + 1]),
          //                           d_lnc.mkList(singletons)};
          std::vector<Term> curChildren{
              res, slv.mkInteger(i), pol, args[(i - 1) * 2 + 1]};
          Term newCur = slv.mkTerm(Kind::SEXPR, curChildren);  // ?????????????
          // addLeanStep(newCur,
          //             pol.getConst<bool>() ? LeanRule::R0_PARTIAL
          //                                  : LeanRule::R1_PARTIAL,
          //             d_empty,
          //             {cur, children[i]},
          //             curArgs,
          //             *cdp);
          ///
          std::string newName =
              "s" + std::to_string(c) + "s" + std::to_string(i);
          auto f = pol.getBooleanValue() ? mk_tac_r0 : mk_tac_r1;
          lean_object* i1 = singletons[0] == minusOne
                                ? mk_option_none()
                                : mk_option_some(lean_cstr_to_nat(
                                    singletons[0].getIntegerValue().c_str()));
          lean_object* i2 = singletons[1] == minusOne
                                ? mk_option_none()
                                : mk_option_some(lean_cstr_to_nat(
                                    singletons[1].getIntegerValue().c_str()));
          steps = lean_array_push(
              steps,
              mk_step_tac(newName.c_str(),
                          process_term(res),
                          f(mk_name_string(currName.c_str()),
                            mk_name_string(pMap[p.getChildren()[i]].c_str()),
                            process_term(args[(i - 1) * 2 + 1]),
                            i1,
                            i2)));
          currName = newName;
          ///
          cur = newCur;
          size_t pivotIndex = 2 * (i - 1);
          // if the second premise is singleton, the new last current literal
          // will be:
          // - if the current last lit is not the pivot, it'll be the new last
          // - otherwise it'll be the first non-pivot literal in a previous
          // premise
          if (ithPremiseSingleton[i])
          {
            // Note that since this is an internal resolution we cannot have
            // that both premises are singletons
            // Assert(numCurLits > 1);
            // we only update if curLastLit cannot remain the same
            if (curLastLit
                == (args[pivotIndex] == slv.mkBoolean(true)
                        ? args[pivotIndex + 1]
                        : args[pivotIndex + 1].notTerm()))
            {
              // search in a previous premise for the last current literal. For
              // each j-th previous premise, we look, from last to first, at the
              // literals that are different from the polarity (j-1)-th pivot
              // and the !polarity (j-2)-th pivot. We ignore singleton premises
              size_t j;
              for (j = i; j > 0; --j)
              {
                if (ithPremiseSingleton[j - 1])
                {
                  continue;
                }
                uint64_t curPivotIndex, prevPivotIndex;
                Term curPivot, prevPivot, diffLit;
                curPivotIndex = 2 * (j - 1);
                curPivot = args[curPivotIndex] == slv.mkBoolean(true)
                               ? args[curPivotIndex]
                               : args[curPivotIndex].notTerm();
                // we also exclude the previous res pivot if there was one,
                // which is always the case except for the first premise
                if (j > 1)
                {
                  prevPivotIndex = 2 * (j - 2);
                  prevPivot = args[prevPivotIndex] == slv.mkBoolean(true)
                                  ? args[prevPivotIndex].notTerm()
                                  : args[prevPivotIndex];
                  diffLit = getLastDiffs(children[j - 1], curPivot, prevPivot);
                }
                else
                {
                  diffLit = getLastDiff(children[j - 1], curPivot);
                }
                if (!diffLit.isNull())
                {
                  curLastLit = diffLit;
                  break;
                }
              }
            }
          }
          else
          {
            curLastLit = getLastDiff(children[i],
                                     args[pivotIndex] == slv.mkBoolean(true)
                                         ? args[pivotIndex + 1].notTerm()
                                         : args[pivotIndex + 1]);
          }
          // The number of literals in working clause is what we had before,
          // plus the literals in the new premise, minus the two literals
          // removed from it and the new premise.
          numCurLits =
              numCurLits
              + (ithPremiseSingleton[i] ? 1 : children[i].getNumChildren()) - 2;
          // if the number of current literals is one, then singletons[0] == 0,
          // otherwise it's != -1 if its last current literal is an OR,
          // otherwise it's -1
          singletons[0] = numCurLits == 1 ? zero
                                          : (curLastLit.getKind() == Kind::OR
                                                 ? slv.mkInteger(numCurLits - 1)
                                                 : minusOne);
          // reset next child to be computed whether singleton
          singletons[1] = minusOne;
        }
      }
      size_t i = children.size() - 1;
      // std::vector<Term> curArgs{d_lnc.convert(args[(i - 1) * 2 + 1]),
      //                           d_lnc.mkList(singletons)};
      // addLeanStep(
      //     res,
      //     args[(i - 1) * 2].getConst<bool>() ? LeanRule::R0 : LeanRule::R1,
      //     d_lnc.convert(res),
      //     {cur, children.back()},
      //     curArgs,
      //     *cdp);
      ///
      std::string newName = "s" + std::to_string(c);
      auto f = args[(i - 1) * 2].getBooleanValue() ? mk_tac_r0 : mk_tac_r1;
      lean_object* i1 = singletons[0] == minusOne
                            ? mk_option_none()
                            : mk_option_some(lean_cstr_to_nat(
                                singletons[0].getIntegerValue().c_str()));
      lean_object* i2 = singletons[1] == minusOne
                            ? mk_option_none()
                            : mk_option_some(lean_cstr_to_nat(
                                singletons[1].getIntegerValue().c_str()));
      steps = lean_array_push(
          steps,
          mk_step_tac(newName.c_str(),
                      process_term(res),
                      f(mk_name_string(currName.c_str()),
                        mk_name_string(pMap[p.getChildren().back()].c_str()),
                        process_term(args[(i - 1) * 2 + 1]),
                        i1,
                        i2)));
      pMap[p] = currName;
      break;
    }
    case ProofRule::REFL:
    {
      pMap[p] = "s" + std::to_string(tMap.size() + pMap.size());
      lean_object* levels = mk_list_cons(mk_level_one(), mk_list_nil());
      lean_object* val = mk_expr_app(
          mk_expr_app(
              mk_expr_const(mk_name_str(mk_name_string("Eq"), "refl"), levels),
              process_sort(p.getArguments()[0].getSort())),
          process_term(p.getArguments()[0]));
      steps = lean_array_push(
          steps,
          mk_step_thm(pMap[p].c_str(), process_term(p.getResult()), val));
      break;
    }
    case ProofRule::SYMM:
    {
      process_step(slv, p.getChildren()[0], tMap, pMap, steps);
      pMap[p] = "s" + std::to_string(tMap.size() + pMap.size());
      lean_object* levels = mk_list_cons(mk_level_one(), mk_list_nil());
      const char* op = p.getResult().getKind() == Kind::EQUAL ? "Eq" : "Ne";
      lean_object* val = mk_expr_app(
          mk_expr_app(
              mk_expr_const(mk_name_str(mk_name_string(op), "symm"), levels),
              process_sort(p.getResult()[0].getSort())),
          mk_expr_fvar(mk_name_string(pMap[p.getChildren()[0]].c_str())));
      steps = lean_array_push(
          steps,
          mk_step_thm(pMap[p].c_str(), process_term(p.getResult()), val));
      break;
    }
    case ProofRule::TRANS:
    {
      const std::vector<Proof> children = p.getChildren();
      for (const Proof& cp : children)
      {
        process_step(slv, cp, tMap, pMap, steps);
      }
      size_t c = tMap.size() + pMap.size();
      std::string currName = pMap[children[0]];
      Term lhs = children[0].getResult()[0];
      lean_object* levels = mk_list_cons(mk_level_one(), mk_list_nil());
      lean_object* thm = mk_expr_app(
          mk_expr_const(mk_name_str(mk_name_string("Eq"), "trans"), levels),
          process_sort(lhs.getSort()));
      lean_inc_n(thm, children.size() - 2);
      for (size_t i = 1; i < children.size(); ++i)
      {
        std::string newName = "s" + std::to_string(c) + "s" + std::to_string(i);
        lean_object* val = mk_expr_app(
            mk_expr_app(thm, mk_expr_fvar(mk_name_string(currName.c_str()))),
            mk_expr_fvar(mk_name_string(pMap[children[i]].c_str())));
        steps = lean_array_push(
            steps,
            mk_step_thm(newName.c_str(),
                        process_term(lhs.eqTerm(children[i].getResult()[1])),
                        val));
        currName = newName;
      }
      pMap[p] = currName;
      break;
    }
    case ProofRule::CONG:
    {
      const std::vector<Proof> children = p.getChildren();
      lean_object* assums = lean_mk_empty_array();
      for (const Proof& cp : children)
      {
        process_step(slv, cp, tMap, pMap, steps);
        assums = lean_array_push(assums, mk_name_string(pMap[cp].c_str()));
      }
      pMap[p] = "s" + std::to_string(tMap.size() + pMap.size());
      steps = lean_array_push(steps,
                              mk_step_tac(pMap[p].c_str(),
                                          process_term(p.getResult()),
                                          mk_tac_cong(assums)));
      break;
    }
    case ProofRule::EQ_RESOLVE:
    {
      process_step(slv, p.getChildren()[0], tMap, pMap, steps);
      process_step(slv, p.getChildren()[1], tMap, pMap, steps);
      pMap[p] = "s" + std::to_string(tMap.size() + pMap.size());
      lean_object* val = mk_expr_app(
          mk_expr_app(
              mk_expr_app(
                  mk_expr_app(
                      mk_expr_const(mk_name_string("eqResolve"), mk_list_nil()),
                      process_term(p.getChildren()[0].getResult())),
                  process_term(p.getResult())),
              mk_expr_fvar(mk_name_string(pMap[p.getChildren()[0]].c_str()))),
          mk_expr_fvar(mk_name_string(pMap[p.getChildren()[1]].c_str())));
      steps = lean_array_push(
          steps,
          mk_step_thm(pMap[p].c_str(), process_term(p.getResult()), val));
      break;
    }
    case ProofRule::EVALUATE:
    {
      pMap[p] = "s" + std::to_string(tMap.size() + pMap.size());
      steps = lean_array_push(
          steps,
          mk_step_tac(
              pMap[p].c_str(), process_term(p.getResult()), mk_tac_eval()));
      break;
    }
    case ProofRule::DSL_REWRITE:
    {
      process_rewrite(slv, p, tMap, pMap, steps);
      break;
    }
    default:
    {
      std::cout << slv.proofToString(p) << std::endl;
      pMap[p] = "s" + std::to_string(tMap.size() + pMap.size());
      steps = lean_array_push(
          steps, mk_step_trust(pMap[p].c_str(), process_term(p.getResult())));
      break;
    }
  }
}

lean_obj_res process(Solver& slv, const cvc5::Proof& p)
{
  std::unordered_map<Term, std::string> tMap;
  std::unordered_map<Proof, std::string> pMap;
  lean_object* steps = lean_mk_empty_array();
  // first two nodes are scopes for definitions and other assumptions. We
  // process only the internal proof node. And we merge these two scopes.
  process_step(slv, p, tMap, pMap, steps);
  return mk_proof(steps);
}

extern "C" lean_obj_res solve_and_get_proof(lean_obj_arg query)
{
  Solver slv;
  slv.setOption("dag-thresh", "0");
  slv.setOption("produce-proofs", "true");
  slv.setOption("proof-granularity", "dsl-rewrite");
  parser::SymbolManager sm(&slv);
  // construct an input parser associated the solver above
  parser::InputParser parser(&slv, &sm);
  parser.setIncrementalStringInput(modes::InputLanguage::SMT_LIB_2_6,
                                   "lean-smt");
  parser.appendIncrementalStringInput(lean_string_cstr(query));
  // parse commands until finished
  std::stringstream out;
  parser::Command cmd;
  while (true)
  {
    cmd = parser.nextCommand();
    if (cmd.isNull())
    {
      break;
    }
    // invoke the command on the solver and the symbol manager, print the result
    // to out
    cmd.invoke(&slv, &sm, out);
  }
  Result r = slv.checkSat();
  return process(slv, slv.getProof()[0]);
}
