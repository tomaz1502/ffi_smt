import Lean

open Lean Elab Meta Tactic Parser

instance : Repr Expr := ⟨fun e _ => f!"({e})"⟩

inductive Tac where
  | eval : Tac -- rfl or decide
  | rewrite : Expr → Expr → Expr → Array (Array Expr) → Tac
  | andElim : Name → Nat → Tac
  | r0 : Name → Name → Expr → Option Nat → Option Nat → Tac
  | r1 : Name → Name → Expr → Option Nat → Option Nat → Tac
  | cong : Array Name → Tac
deriving Repr

inductive Step where
  -- have $name : $type := $val
  | thm (name : Name) (type : Expr) (val : Expr) : Step
  -- have $name : $type := by $tac
  | tac (name : Name) (type : Expr) (tac : Tac) : Step
  -- have $name : ¬ $paramType ∨ $retType := scope (fun $scopedName => ...)
  | scope (name : Name) (type : Expr) (assums : Array Name) (steps : Array Step) (main : Name) : Step
  -- have $name : $type := sorry
  | trust (name : Name) (type : Expr) : Step
deriving Inhabited, Repr

-- an array containing a single scope for now...
abbrev Proof := Array Step

@[extern "solve_and_get_proof"]
opaque solveAndGetProof (query : String) : Proof
