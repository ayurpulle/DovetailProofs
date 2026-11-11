import DovetailProofs.Predictor.MarkovReset

/-!
# The three-symbol reset chain

The concrete Markov chain of Section 9.2 of `Lattice/main.tex` (l.1685): uniform initial
distribution and the doubly stochastic transition matrix `M` of l.1689.  It satisfies the
hypotheses of Proposition `prop:markov-reset-general`, so `S_p ≅ R_3^1` and (Corollary, l.1798)
`Con(S_p)` contains an `M₃` whose bottom is the equality relation and whose top is a congruence
strictly below the universal one; hence `Con(S_p)`, and `Con(S_A)` for every reachable exact
predictor, is non-distributive.
-/

namespace Dovetail.Predictor

/-- The transition matrix `M` of main.tex l.1689. -/
noncomputable def resetM : Fin 3 → Fin 3 → ℝ :=
  ![![1 / 2, 1 / 3, 1 / 6], ![1 / 3, 1 / 6, 1 / 2], ![1 / 6, 1 / 2, 1 / 3]]

/-- The three-symbol chain of main.tex l.1685: uniform initial distribution, transition
matrix `M`.  `M` is entrywise positive with pairwise distinct rows (l.1696). -/
noncomputable def resetChain3 : MarkovChain (Fin 3) where
  init := fun _ => 1 / 3
  trans := resetM
  init_pos := fun _ => by norm_num
  init_sum := by rw [Fin.sum_univ_three]; norm_num
  trans_pos := fun i j => by fin_cases i <;> fin_cases j <;> norm_num [resetM]
  trans_sum := fun i => by
    rw [Fin.sum_univ_three]
    fin_cases i
    · show (1 / 2 : ℝ) + 1 / 3 + 1 / 6 = 1
      norm_num
    · show (1 / 3 : ℝ) + 1 / 6 + 1 / 2 = 1
      norm_num
    · show (1 / 6 : ℝ) + 1 / 2 + 1 / 3 = 1
      norm_num
  rows_injective := by
    intro i j h
    have h0 := congrFun h 0
    fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; norm_num [resetM] at h0)

/-- **Corollary (main.tex l.1798)**: for the three-symbol chain, `Con(S_p)` contains `M₃` as an
interval `[⊥, θ]` with `θ` (the image of "merge the three reset maps, keep the identity
separate") strictly below the universal congruence. -/
theorem resetChain3_isM3 :
    ∃ a b c θ : Con resetChain3.lang.Sp, IsM3 ⊥ a b c θ ∧ θ ≠ ⊤ := by
  let e : Con (Reset (Fin 3)) ≃o Con resetChain3.lang.Sp :=
    (conCongr resetChain3.resetEquiv.symm).symm
  have h := Reset.isM3_fin3.map e e.injective (map_inf e) (map_sup e)
  rw [map_bot] at h
  refine ⟨_, _, _, _, h, fun htop => ?_⟩
  rw [← map_top e] at htop
  exact Reset.ofSetoid_ne_top _ (e.injective htop)

/-- **Corollary (main.tex l.1804)**: `Con(S_p)` is non-distributive for the three-symbol chain. -/
theorem resetChain3_nonDistrib : NonDistrib (Con resetChain3.lang.Sp) :=
  resetChain3.nonDistrib_con_Sp (x := 0) (y := 1) (z := 2) (by decide) (by decide) (by decide)

/-- **Conclusion (i) of main.tex l.1848**: every reachable exact predictor of the three-symbol
chain has a non-distributive congruence lattice. -/
theorem resetChain3_nonDistrib_agent {Q : Type*} (A : ExactAgent resetChain3.lang Q) :
    NonDistrib (Con A.SA) :=
  resetChain3.nonDistrib_con_SA (x := 0) (y := 1) (z := 2) (by decide) (by decide) (by decide) A

/-- Every symbol of the three-symbol chain is synchronising (Example, main.tex l.1136). -/
theorem resetChain3_rk (j : Fin 3) : rk (resetChain3.lang.tau j) = 1 := resetChain3.rk_tau j

end Dovetail.Predictor

#print axioms Dovetail.Predictor.resetChain3
#print axioms Dovetail.Predictor.resetChain3_isM3
#print axioms Dovetail.Predictor.resetChain3_nonDistrib_agent
