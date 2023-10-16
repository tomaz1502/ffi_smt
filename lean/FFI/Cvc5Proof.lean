import Lean

open Lean

structure Tac where
  stx : String
  deriving Inhabited

inductive Step where
  | tac (name : Name) (type : String) : Tac → Step
  | thm (name : Name) (type : String) (args : List Name) : Step
  | scope (name : Name) (type : String) (steps : List Step) : Step
  deriving Inhabited

-- we will define a function that takes a step and introduces the Name
-- with the given type in the context, using pf
abbrev Cvc5Proof := List Step

@[extern "mk_tac"]
opaque mkTac : String → Tac

@[extern "mk_step_tac"]
opaque mkStepTac : Name → String → Tac → Step

@[extern "mk_step_thm"]
opaque mkStepThm : Name → String → List Name → Step

@[extern "mk_step_scope"]
opaque mkStepScope : Name → String → List Step → Step

@[extern "mk_cvc5_proof"]
opaque mkCvc5Proof : List Step → Cvc5Proof
