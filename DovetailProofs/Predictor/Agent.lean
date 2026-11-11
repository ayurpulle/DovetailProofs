import DovetailProofs.Predictor.Basic

/-!
# Every exact predictive agent contains the canonical machine

Formalises Section 3 of `Lattice/main.tex`:

* `descent_run`: Lemma `lem:descent` (l.325) in the paper's own word convention, obtained from
  the existing `Dovetail.descent`;
* `ExactAgent`: the Definition of a reachable exact predictive agent (l.373);
* `ExactAgent.L`, `ExactAgent.L_surjective`, `ExactAgent.L_step`: Theorem
  `thm:predictor-quotient` (l.423);
* `ExactAgent.Phi` and its properties: Corollary `cor:quotient` (l.460);
* `canonicalAgent`: the canonical machine is itself a reachable exact predictive agent with
  update monoid `S_p` (Remark `rem:tight`, l.844).
-/

namespace Dovetail.Predictor

open Function

section Descent

variable {O Q Y : Type*}

/-- Iterating `L ∘ δ_o = τ_o ∘ L` gives `L ∘ δ_w = τ_w ∘ L` (proof of Lemma `lem:descent`,
main.tex l.346). -/
theorem intertwine_run (δ : O → Q → Q) (τ : O → Y → Y) (L : Q → Y)
    (h : ∀ o q, L (δ o q) = τ o (L q)) (w : List O) (q : Q) :
    L (run δ w q) = run τ w (L q) := by
  induction w generalizing q with
  | nil => rfl
  | cons o w ih => rw [run_cons, ih, h, run_cons]

/-- **Descent** (Lemma `lem:descent`, main.tex l.325), in the paper's convention
`δ_w = δ_{o_n} ∘ ⋯ ∘ δ_{o_1}`: a surjection `L : Q → Y` with `L ∘ δ_o = τ_o ∘ L` induces a
well-defined surjective monoid homomorphism `Φ : S_Q → S_Y` with `Φ(δ_w) = τ_w`.
(The paper assumes a finite alphabet; this is not needed.) -/
theorem descent_run (δ : O → Q → Q) (τ : O → Y → Y) (L : Q → Y) (hL : Surjective L)
    (h : ∀ o q, L (δ o q) = τ o (L q)) :
    ∃ Φ : transitionMonoid (V := Q) δ →* transitionMonoid (V := Y) τ,
      Surjective Φ ∧
        ∀ w : List O, (Φ ⟨run δ w, run_mem_transitionMonoid δ w⟩ : Function.End Y) = run τ w := by
  obtain ⟨Φ, hΦ, hw⟩ := descent (V := Y) (V' := Q) τ δ L hL h
  refine ⟨Φ, hΦ, fun w => ?_⟩
  have := hw (FreeMonoid.ofList w.reverse)
  rw [← run_eq_lift τ w] at this
  rw [← this]
  congr 2
  exact Subtype.ext (run_eq_lift δ w)

end Descent

variable {O : Type*} [Fintype O]

/-- **Reachable exact predictive agent** `A = (Q, q₀, d, {δ_o}, F)` for `p`
(Definition, main.tex l.373).

Encoding notes (recorded differences from the text, none of which changes the content):
* `Q⁺ = {δ_u(q₀) : p(u) > 0}`, `d ∉ Q⁺` and `Q = Q⁺ ⊔ {d}` are expressed by `live` (no possible
  history reaches `d`) and `reachable` (every state other than `d` is reached by a possible
  history).
* The readout `F : Q⁺ → X_p` is a total function `readout : Q → (O* → ℝ)`; only its values on
  `Q⁺` are constrained (by `exact`), and `exact` forces those values to lie in `X_p`.
-/
structure ExactAgent (P : StochLang O) (Q : Type*) where
  /-- The initial state `q₀`. -/
  init : Q
  /-- The dead state `d`. -/
  dead : Q
  /-- The update maps `δ_o`. -/
  step : O → Q → Q
  /-- The readout `F` (constrained only on live states). -/
  readout : Q → List O → ℝ
  /-- `δ_o(d) = d`. -/
  step_dead : ∀ o, step o dead = dead
  /-- `d ∉ Q⁺`. -/
  live : ∀ u, 0 < P.p u → run step u init ≠ dead
  /-- `Q = Q⁺ ⊔ {d}`. -/
  reachable : ∀ q, q ≠ dead → ∃ u, 0 < P.p u ∧ run step u init = q
  /-- Trimming: `p(u) > 0`, `p(uo) = 0` imply `δ_o(δ_u(q₀)) = d`. -/
  trim : ∀ u o, 0 < P.p u → P.p (u ++ [o]) = 0 → step o (run step u init) = dead
  /-- Exactness: `F(δ_u(q₀)) = q_u` for every possible `u`. -/
  exact : ∀ u, 0 < P.p u → readout (run step u init) = P.q u

namespace ExactAgent

variable {P : StochLang O} {Q : Type*} (A : ExactAgent P Q)

/-- The dead state is absorbing for every word (main.tex l.403). -/
theorem run_dead (w : List O) : run A.step w A.dead = A.dead := by
  induction w with
  | nil => rfl
  | cons o w ih => rw [run_cons, A.step_dead, ih]

/-- An impossible history leads to the dead state (trimming convention, main.tex l.416). -/
theorem run_init_of_zero {u : List O} (h : P.p u = 0) : run A.step u A.init = A.dead := by
  induction u using List.reverseRecOn with
  | nil => exact absurd h (by rw [P.nil]; exact one_ne_zero)
  | append_singleton u o ih =>
    rw [run_snoc]
    by_cases hu : 0 < P.p u
    · exact A.trim u o hu h
    · rw [ih (P.not_pos_iff.1 hu), A.step_dead]

/-- The update monoid `S_A = ⟨δ_o : o ∈ O⟩ ⊆ 𝒯_Q` (main.tex l.458). -/
def SA : Submonoid (Function.End Q) := transitionMonoid (V := Q) A.step

open Classical in
/-- The map `L : Q → X̂_p` of Theorem `thm:predictor-quotient` (main.tex l.437):
`L(δ_u(q₀)) = q_u` on live states and `L(d) = †`.  It is defined through the readout, which is
the paper's well-definedness argument (`q_u = F(δ_u(q₀))`). -/
noncomputable def L (q : Q) : Option P.X :=
  if h : q = A.dead then none
  else some ⟨A.readout q, by
    obtain ⟨u, hu, rfl⟩ := A.reachable q h
    exact ⟨u, hu, A.exact u hu⟩⟩

/-- `L(d) = †` (main.tex l.438). -/
theorem L_dead : A.L A.dead = none := dif_pos rfl

/-- `L(δ_u(q₀)) = ν(u)` for every word `u`; for possible `u` this is `L(δ_u(q₀)) = q_u`
(main.tex l.437). -/
theorem L_run_init (u : List O) : A.L (run A.step u A.init) = P.nu u := by
  by_cases hu : 0 < P.p u
  · rw [P.nu_of_pos hu, L, dif_neg (A.live u hu)]
    exact congrArg some (StochLang.X.ext (A.exact u hu))
  · rw [P.nu_of_not_pos hu, A.run_init_of_zero (P.not_pos_iff.1 hu), L_dead]

/-- `L(q) = †` only for the dead state (main.tex l.1124). -/
theorem L_eq_none_iff {q : Q} : A.L q = none ↔ q = A.dead := by
  unfold L; split_ifs with h <;> simp [h]

/-- **Theorem `thm:predictor-quotient`, surjectivity** (main.tex l.423, l.442). -/
theorem L_surjective : Surjective A.L := by
  intro y
  cases y with
  | none => exact ⟨A.dead, A.L_dead⟩
  | some x =>
    obtain ⟨u, _, hx⟩ := P.exists_nu_eq_some x
    exact ⟨run A.step u A.init, by rw [A.L_run_init, hx]⟩

/-- **Theorem `thm:predictor-quotient`, equivariance** `L ∘ δ_o = τ_o ∘ L`
(main.tex l.423, l.443). -/
theorem L_step (o : O) (q : Q) : A.L (A.step o q) = P.tau o (A.L q) := by
  by_cases hq : q = A.dead
  · rw [hq, A.step_dead, A.L_dead, P.tau_none]
  · obtain ⟨u, _, rfl⟩ := A.reachable q hq
    rw [← run_snoc A.step u o A.init, A.L_run_init, A.L_run_init, P.tau_nu]

/-- **Theorem `thm:predictor-quotient`** (main.tex l.423): for a reachable exact predictive agent
there is a surjection `L : Q → X̂_p` with `L ∘ δ_o = τ_o ∘ L` for all `o`. -/
theorem predictor_quotient :
    ∃ L : Q → Option P.X, Surjective L ∧ ∀ o q, L (A.step o q) = P.tau o (L q) :=
  ⟨A.L, A.L_surjective, A.L_step⟩

/-- `L ∘ δ_w = τ_w ∘ L` (main.tex l.1121). -/
theorem L_run (w : List O) (q : Q) : A.L (run A.step w q) = run P.tau w (A.L q) :=
  intertwine_run A.step P.tau A.L A.L_step w q

/-- **Corollary `cor:quotient`** (main.tex l.460): there is a surjective monoid homomorphism
`Φ : S_A → S_p` with `Φ(δ_w) = τ_w`. -/
theorem exists_Phi :
    ∃ Φ : A.SA →* P.Sp, Surjective Φ ∧
      ∀ w : List O, (Φ ⟨run A.step w, run_mem_transitionMonoid A.step w⟩ :
        Function.End (Option P.X)) = run P.tau w :=
  descent_run A.step P.tau A.L A.L_surjective A.L_step

/-- The homomorphism `Φ : S_A → S_p` of Corollary `cor:quotient` (main.tex l.466).  It is
uniquely determined by `Φ(δ_w) = τ_w`. -/
noncomputable def Phi : A.SA →* P.Sp := Classical.choose A.exists_Phi

/-- `Φ` is surjective (Corollary `cor:quotient`, main.tex l.460). -/
theorem Phi_surjective : Surjective A.Phi := (Classical.choose_spec A.exists_Phi).1

/-- `Φ(δ_w) = τ_w` (Corollary `cor:quotient`, main.tex l.468). -/
theorem Phi_run (w : List O) :
    (A.Phi ⟨run A.step w, run_mem_transitionMonoid A.step w⟩ : Function.End (Option P.X)) =
      run P.tau w :=
  (Classical.choose_spec A.exists_Phi).2 w

/-- `Φ` is characterised by equivariance: `Φ(s) ∘ L = L ∘ s` for every `s ∈ S_A`
(main.tex l.346). -/
theorem Phi_apply_L (s : A.SA) (q : Q) :
    (A.Phi s : Function.End (Option P.X)) (A.L q) = A.L ((s : Function.End Q) q) := by
  obtain ⟨s, hs⟩ := s
  obtain ⟨w, rfl⟩ := (mem_transitionMonoid_iff A.step s).1 hs
  rw [A.Phi_run, A.L_run]

/-- The kernel `κ = ker Φ`, a congruence on `S_A` (main.tex l.476). -/
noncomputable def kappa : Con A.SA := Con.ker A.Phi

end ExactAgent

/-- **The canonical machine** `(X̂_p, q_ε, †, {τ_o}, id)` is a reachable exact predictive agent
(Remark `rem:tight`, main.tex l.844).  Its update monoid is `S_p` by definition
(`canonicalAgent_SA`). -/
noncomputable def canonicalAgent (P : StochLang O) : ExactAgent P (Option P.X) where
  init := P.nu []
  dead := none
  step := P.tau
  readout y := match y with
    | some x => x.1
    | none => 0
  step_dead := P.tau_none
  live u hu := by rw [← P.nu_eq_run, P.nu_of_pos hu]; exact Option.some_ne_none _
  reachable y hy := by
    cases y with
    | none => exact absurd rfl hy
    | some x =>
      obtain ⟨u, hu, hx⟩ := P.exists_nu_eq_some x
      exact ⟨u, hu, by rw [← P.nu_eq_run, hx]⟩
  trim u o hu h := by rw [← P.nu_eq_run, P.tau_nu, P.nu_eq_none_iff, h]
  exact u hu := by rw [← P.nu_eq_run, P.nu_of_pos hu]; rfl

/-- The update monoid of the canonical machine is `S_p` (Remark `rem:tight`, main.tex l.848). -/
theorem canonicalAgent_SA (P : StochLang O) : (canonicalAgent P).SA = P.Sp := rfl

end Dovetail.Predictor

#print axioms Dovetail.Predictor.descent_run
#print axioms Dovetail.Predictor.ExactAgent.predictor_quotient
#print axioms Dovetail.Predictor.ExactAgent.exists_Phi
#print axioms Dovetail.Predictor.canonicalAgent
