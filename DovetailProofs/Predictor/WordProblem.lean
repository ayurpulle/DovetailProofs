import DovetailProofs.Predictor.Syntactic

/-!
# States and the word problem: the algebraic part

The monoid-level content of Remark `rem:word-problem` (`Lattice/main.tex` l.782) and of
Proposition `prop:pred-word`(i) (l.910).  The circuit-complexity statements built on them
(Proposition `prop:pred-word`(ii), Theorem `thm:pred-complexity`, Corollary `cor:transformers`)
are **not formalised**: Mathlib has no circuit classes (`AC⁰`, `ACC⁰`, `TC⁰`, `NC¹`), no
reductions between them, and none of the cited theorems (Barrington, Barrington–Thérien,
Smolensky, Merrill–Sabharwal).
-/

namespace Dovetail.Predictor

namespace StochLang

variable {O : Type*} [Fintype O] (P : StochLang O)

/-- **Remark `rem:word-problem`, second half** (main.tex l.787): if `u_x` is a history with
`ν(u_x) = x` for each live `x`, then `τ_w` is determined by the tuple `(ν(u_x w))_{x ∈ X_p}`. -/
theorem tau_eq_iff_forall_rep (rep : P.X → List O) (hrep : ∀ x, P.nu (rep x) = some x)
    (w w' : List O) :
    run P.tau w = run P.tau w' ↔ ∀ x, P.nu (rep x ++ w) = P.nu (rep x ++ w') := by
  constructor
  · intro h x
    rw [← P.run_tau_nu, ← P.run_tau_nu, h]
  · intro h
    refine P.ext_nu (by simp) fun u hu => ?_
    have hx := hrep (P.qState u hu)
    rw [P.nu_of_pos hu, ← hx, P.run_tau_nu, P.run_tau_nu, h]

/-- **Proposition `prop:pred-word`(i)** (main.tex l.914): the next-symbol law
`n_p(u) = (q_u(o))_{o ∈ O}` of a possible history is a function of `τ_u`, namely the next-symbol
law of the state `τ_u(q_ε)`. -/
theorem nextSymbol_eq_of_tau_eq {u u' : List O} (hu : 0 < P.p u) (hu' : 0 < P.p u')
    (h : run P.tau u = run P.tau u') (o : O) : P.q u [o] = P.q u' [o] := by
  have hν : P.nu u = P.nu u' := by rw [P.nu_eq_run u, P.nu_eq_run u', h]
  rw [P.nu_of_pos hu, P.nu_of_pos hu', Option.some.injEq] at hν
  have hq : P.q u = P.q u' := congrArg Subtype.val hν
  rw [hq]

end StochLang

end Dovetail.Predictor

#print axioms Dovetail.Predictor.StochLang.tau_eq_iff_forall_rep
#print axioms Dovetail.Predictor.StochLang.nextSymbol_eq_of_tau_eq
