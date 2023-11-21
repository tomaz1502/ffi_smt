import FFI

def main : IO Unit := do
  let p := solveAndGetProof "(set-logic UF)\n(assert false)\n(check-sat)"
  IO.println (repr p)

-- #eval Solver.getVersion (Solver.new ())

#eval solveAndGetProof "
(set-logic UF)
(assert false)
"

#eval solveAndGetProof "
(set-logic UF)
(declare-sort U 0)
(declare-const a U)
(declare-const b U)
(declare-const c U)
(declare-const d U)
(declare-fun f (U U) U)
(declare-const p1 Bool)
(declare-const p2 Bool)
(declare-const p3 Bool)
(assert (= a b))
(assert (= c d))
(assert (and p1 true))
(assert (or (not p1) (and p2 p3)))
(assert (or (not p3) (distinct (f a c) (f b d))))
(check-sat)
"
