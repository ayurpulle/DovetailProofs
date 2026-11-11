import DovetailProofs.Predictor.Agent

/-!
# The possibility layer

Formalises Section 4 of `Lattice/main.tex`: follower sets and support states (Definition, l.507),
the updates `σ_o` (l.523), the monoid `S_supp` (l.537), Proposition `prop:support-quotient`
(l.544), Corollary `cor:support-tower` (l.567) and Remark `rem:full-support` (l.606).

`X̂_supp` is `Option P.Xsupp` with `none` for `†`.  `P.mu` is the labelling `u ↦ F_u` (or `†`),
the support analogue of `P.nu`.
-/

namespace Dovetail.Predictor

open Function

namespace StochLang

variable {O : Type*} [Fintype O] (P : StochLang O)

/-- The follower set `F_u = {v : p(uv) > 0}` (Definition, main.tex l.507).  For impossible `u`
this is the empty set, the extension used in the proof of Lemma `lem:syntactic`(ii), l.754. -/
def follower (u : List O) : Set (List O) := {v | 0 < P.p (u ++ v)}

/-- `F_u` contains `ε` iff `u` is possible (main.tex l.522, l.755). -/
theorem nil_mem_follower {u : List O} : [] ∈ P.follower u ↔ 0 < P.p u := by
  simp [follower]

/-- `F_u` is empty exactly when `u ∉ L_p` (main.tex l.755). -/
theorem follower_eq_empty {u : List O} (h : ¬ 0 < P.p u) : P.follower u = ∅ := by
  ext v
  simp only [follower, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  exact fun h' => h (P.pos_of_append_pos h')

/-- `F_u = {v : q_u(v) > 0}` is determined by `q_u` alone (proof of Proposition
`prop:support-quotient`, main.tex l.559). -/
theorem follower_eq_of_pos {u : List O} (h : 0 < P.p u) :
    P.follower u = {v | 0 < P.q u v} := by
  ext v; exact ((P.q_pos_iff h v).symm)

/-- **Support states** `X_supp = {F_u : p(u) > 0}` (Definition, main.tex l.513). -/
def Xsupp : Type _ := {F : Set (List O) // ∃ u, 0 < P.p u ∧ F = P.follower u}

/-- The support state `F_u` of a possible history. -/
def fState (u : List O) (h : 0 < P.p u) : P.Xsupp := ⟨P.follower u, u, h, rfl⟩

/-- The one-symbol shift on follower sets, `F ↦ {v : ov ∈ F}` (main.tex l.527). -/
def sshift (o : O) (F : Set (List O)) : Set (List O) := {v | o :: v ∈ F}

/-- `σ_o(F_u) = F_{uo}` at the level of sets (main.tex l.535). -/
theorem sshift_follower (o : O) (u : List O) :
    sshift o (P.follower u) = P.follower (u ++ [o]) := by
  ext v; simp [sshift, follower]

open Classical in
/-- **The support update** `σ_o : X̂_supp → X̂_supp` (main.tex l.523): `σ_o(F) = {v : ov ∈ F}` if
`o ∈ F`, `†` otherwise, and `σ_o(†) = †`.  It is a function of the set `F` itself. -/
noncomputable def sigmaStep (o : O) : Option P.Xsupp → Option P.Xsupp
  | none => none
  | some F =>
    if h : [o] ∈ F.1 then
      some ⟨sshift o F.1, by
        obtain ⟨u, hu, hF⟩ := F.2
        rw [hF] at h ⊢
        exact ⟨u ++ [o], h, P.sshift_follower o u⟩⟩
    else none

/-- `σ_o(†) = †` (main.tex l.531). -/
@[simp] theorem sigmaStep_none (o : O) : P.sigmaStep o none = none := rfl

open Classical in
/-- The support labelling `u ↦ F_u` for possible `u`, `†` otherwise (the map `u ↦ F_u` of the
proof of Lemma `lem:syntactic`(ii), main.tex l.754, with `†` read as the empty set). -/
noncomputable def mu (u : List O) : Option P.Xsupp :=
  if h : 0 < P.p u then some (P.fState u h) else none

/-- `μ(u) = F_u` for possible `u` (main.tex l.508). -/
theorem mu_of_pos {u : List O} (h : 0 < P.p u) : P.mu u = some (P.fState u h) := dif_pos h

/-- `μ(u) = †` for impossible `u` (main.tex l.756). -/
theorem mu_of_not_pos {u : List O} (h : ¬ 0 < P.p u) : P.mu u = none := dif_neg h

/-- `σ_o(F_u) = F_{uo}` whenever `p(uo) > 0`, while `o ∉ F_u` exactly when `p(uo) = 0`
(main.tex l.535); in terms of the labelling, `σ_o(μ(u)) = μ(uo)`. -/
theorem sigmaStep_mu (o : O) (u : List O) : P.sigmaStep o (P.mu u) = P.mu (u ++ [o]) := by
  by_cases hu : 0 < P.p u
  · rw [P.mu_of_pos hu]
    by_cases huo : 0 < P.p (u ++ [o])
    · rw [P.mu_of_pos huo]
      have : [o] ∈ (P.fState u hu).1 := huo
      simp only [sigmaStep, this, dite_true, Option.some.injEq]
      exact Subtype.ext (P.sshift_follower o u)
    · rw [P.mu_of_not_pos huo]
      have : ¬ [o] ∈ (P.fState u hu).1 := huo
      simp only [sigmaStep, this, dite_false]
  · rw [P.mu_of_not_pos hu, P.mu_of_not_pos, sigmaStep_none]
    exact fun h => hu (P.pos_of_append_pos h)

/-- `σ_w(μ(u)) = μ(uw)` (main.tex l.757). -/
theorem run_sigmaStep_mu (w u : List O) : run P.sigmaStep w (P.mu u) = P.mu (u ++ w) := by
  induction w generalizing u with
  | nil => simp
  | cons o w ih => rw [run_cons, P.sigmaStep_mu, ih]; simp

/-- Every `σ_w` fixes `†` (main.tex l.531). -/
@[simp] theorem run_sigmaStep_none (w : List O) : run P.sigmaStep w none = none := by
  induction w with
  | nil => rfl
  | cons o w ih => rw [run_cons, sigmaStep_none, ih]

/-- `μ(u) = μ(u')` iff the (extended) follower sets agree (main.tex l.754–757). -/
theorem mu_eq_mu_iff {u u' : List O} : P.mu u = P.mu u' ↔ P.follower u = P.follower u' := by
  by_cases hu : 0 < P.p u <;> by_cases hu' : 0 < P.p u'
  · rw [P.mu_of_pos hu, P.mu_of_pos hu', Option.some.injEq]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  · rw [P.mu_of_pos hu, P.mu_of_not_pos hu', P.follower_eq_empty hu']
    refine ⟨fun h => absurd h (Option.some_ne_none _), fun h => ?_⟩
    have : [] ∈ P.follower u := P.nil_mem_follower.2 hu
    rw [h] at this
    exact absurd this (Set.notMem_empty _)
  · rw [P.mu_of_not_pos hu, P.mu_of_pos hu', P.follower_eq_empty hu]
    refine ⟨fun h => absurd h.symm (Option.some_ne_none _), fun h => ?_⟩
    have : [] ∈ P.follower u' := P.nil_mem_follower.2 hu'
    rw [← h] at this
    exact absurd this (Set.notMem_empty _)
  · rw [P.mu_of_not_pos hu, P.mu_of_not_pos hu', P.follower_eq_empty hu,
      P.follower_eq_empty hu']
    simp

/-- **The possibility monoid** `S_supp = ⟨σ_o : o ∈ O⟩ ⊆ 𝒯_{X̂_supp}` (main.tex l.537). -/
noncomputable def Ssupp : Submonoid (Function.End (Option P.Xsupp)) :=
  transitionMonoid (V := Option P.Xsupp) P.sigmaStep

/-- The follower set of a predictive state, `{v : q(v) > 0}` (main.tex l.559). -/
def supp (x : P.X) : P.Xsupp :=
  ⟨{v | 0 < x.1 v}, by
    obtain ⟨u, hu, hx⟩ := x.2
    exact ⟨u, hu, by rw [hx, P.follower_eq_of_pos hu]⟩⟩

/-- **The map `σ : X̂_p → X̂_supp`** of Proposition `prop:support-quotient` (main.tex l.546):
`σ(q_u) = F_u`, `σ(†) = †`.  Defined on the function `q_u` itself, which is the paper's
well-definedness argument. -/
def sigma : Option P.X → Option P.Xsupp := Option.map P.supp

/-- `σ(ν(u)) = μ(u)`; for possible `u` this is `σ(q_u) = F_u` (main.tex l.550). -/
theorem sigma_nu (u : List O) : P.sigma (P.nu u) = P.mu u := by
  by_cases hu : 0 < P.p u
  · rw [P.nu_of_pos hu, P.mu_of_pos hu]
    exact congrArg some (Subtype.ext (P.follower_eq_of_pos hu).symm)
  · rw [P.nu_of_not_pos hu, P.mu_of_not_pos hu]; rfl

/-- **Proposition `prop:support-quotient`, surjectivity** (main.tex l.544, l.560). -/
theorem sigma_surjective : Surjective P.sigma := by
  intro y
  cases y with
  | none => exact ⟨none, rfl⟩
  | some F =>
    obtain ⟨F, u, hu, rfl⟩ := F
    exact ⟨P.nu u, by rw [P.sigma_nu, P.mu_of_pos hu]; rfl⟩

/-- **Proposition `prop:support-quotient`, equivariance** `σ ∘ τ_o = σ_o ∘ σ`
(main.tex l.544, l.561). -/
theorem sigma_tau (o : O) (y : Option P.X) :
    P.sigma (P.tau o y) = P.sigmaStep o (P.sigma y) := by
  cases y with
  | none => rfl
  | some x =>
    obtain ⟨u, hu, hx⟩ := P.exists_nu_eq_some x
    rw [← hx, P.tau_nu, P.sigma_nu, P.sigma_nu, P.sigmaStep_mu]

/-- **Proposition `prop:support-quotient`** (main.tex l.544): `σ : X̂_p → X̂_supp` is a
(well-defined) surjection with `σ ∘ τ_o = σ_o ∘ σ`. -/
theorem support_quotient :
    Surjective P.sigma ∧ ∀ o y, P.sigma (P.tau o y) = P.sigmaStep o (P.sigma y) :=
  ⟨P.sigma_surjective, P.sigma_tau⟩

/-- **Corollary `cor:support-tower`, first part** (main.tex l.567): descent applied to `σ` gives a
surjective monoid homomorphism `S_p → S_supp` with `τ_w ↦ σ_w`. -/
theorem exists_suppHom :
    ∃ Ψ : P.Sp →* P.Ssupp, Surjective Ψ ∧
      ∀ w : List O, (Ψ ⟨run P.tau w, run_mem_transitionMonoid P.tau w⟩ :
        Function.End (Option P.Xsupp)) = run P.sigmaStep w :=
  descent_run P.tau P.sigmaStep P.sigma P.sigma_surjective P.sigma_tau

/-- The homomorphism `S_p → S_supp` of Corollary `cor:support-tower` (main.tex l.569). -/
noncomputable def suppHom : P.Sp →* P.Ssupp := Classical.choose P.exists_suppHom

/-- `S_p → S_supp` is surjective (Corollary `cor:support-tower`, main.tex l.569). -/
theorem suppHom_surjective : Surjective P.suppHom := (Classical.choose_spec P.exists_suppHom).1

/-- `S_p → S_supp` sends `τ_w` to `σ_w` (Corollary `cor:support-tower`, main.tex l.569). -/
theorem suppHom_run (w : List O) :
    (P.suppHom ⟨run P.tau w, run_mem_transitionMonoid P.tau w⟩ :
      Function.End (Option P.Xsupp)) = run P.sigmaStep w :=
  (Classical.choose_spec P.exists_suppHom).2 w

/-- The kernel `κ_supp` of `S_p → S_supp` (main.tex l.570). -/
noncomputable def kappaSupp : Con P.Sp := Con.ker P.suppHom

/-- **Remark `rem:full-support`, forward direction** (main.tex l.606): if every word is possible
then every `σ_o` is the identity. -/
theorem sigmaStep_eq_id_of_full (h : ∀ w, 0 < P.p w) (o : O) : P.sigmaStep o = id := by
  have hF : ∀ u, P.follower u = Set.univ := fun u => by
    ext v; simp [follower, h]
  funext y
  cases y with
  | none => rfl
  | some F =>
    obtain ⟨F, u, hu, rfl⟩ := F
    have : (some ⟨P.follower u, u, hu, rfl⟩ : Option P.Xsupp) = P.mu u := (P.mu_of_pos hu).symm
    rw [this, P.sigmaStep_mu]
    show P.mu (u ++ [o]) = P.mu u
    rw [P.mu_eq_mu_iff, hF, hF]

/-- **Remark `rem:full-support`** (main.tex l.606): `S_supp` is the trivial monoid exactly when
every finite word is possible. -/
theorem Ssupp_trivial_iff : (∀ s ∈ P.Ssupp, s = 1) ↔ ∀ w, 0 < P.p w := by
  constructor
  · intro h w
    -- `σ_w = 1`, so `μ(w) = σ_w(μ(ε)) = μ(ε) ≠ †`
    have h1 := h _ (run_mem_transitionMonoid P.sigmaStep w)
    have h2 := congrFun h1 (P.mu [])
    rw [P.run_sigmaStep_mu, List.nil_append] at h2
    by_contra hw
    rw [P.mu_of_not_pos hw, P.mu_of_pos P.nil_pos] at h2
    exact Option.some_ne_none _ h2.symm
  · intro h s hs
    obtain ⟨w, rfl⟩ := (mem_transitionMonoid_iff P.sigmaStep s).1 hs
    clear hs
    induction w with
    | nil => rfl
    | cons o w ih =>
      funext y
      rw [run_cons, P.sigmaStep_eq_id_of_full h o]
      exact congrFun ih y

end StochLang

namespace ExactAgent

variable {O : Type*} [Fintype O] {P : StochLang O} {Q : Type*} (A : ExactAgent P Q)

/-- The composite `S_A → S_p → S_supp` of Corollary `cor:support-tower` (main.tex l.573). -/
noncomputable def PhiSupp : A.SA →* P.Ssupp := P.suppHom.comp A.Phi

/-- The composite `S_A → S_supp` is surjective (Corollary `cor:support-tower`, main.tex l.573). -/
theorem PhiSupp_surjective : Surjective A.PhiSupp :=
  P.suppHom_surjective.comp A.Phi_surjective

/-- The composite sends `δ_w` to `σ_w`, i.e. it is the map that Lemma `lem:descent` attaches to
the composite equivariant surjection `Q → X̂_p → X̂_supp` (proof of Corollary `cor:support-tower`,
main.tex l.581). -/
theorem PhiSupp_run (w : List O) :
    (A.PhiSupp ⟨run A.step w, run_mem_transitionMonoid A.step w⟩ :
      Function.End (Option P.Xsupp)) = run P.sigmaStep w := by
  have h : A.Phi ⟨run A.step w, run_mem_transitionMonoid A.step w⟩ =
      ⟨run P.tau w, run_mem_transitionMonoid P.tau w⟩ := Subtype.ext (A.Phi_run w)
  show (P.suppHom (A.Phi _) : Function.End (Option P.Xsupp)) = _
  rw [h, P.suppHom_run]

/-- The kernel `κ'` of the composite `S_A → S_p → S_supp` (main.tex l.577). -/
noncomputable def kappa' : Con A.SA := Con.ker A.PhiSupp

/-- **Corollary `cor:support-tower`, second part** (main.tex l.577): the kernel `κ'` of the
composite contains `κ = ker Φ`. -/
theorem kappa_le_kappa' : A.kappa ≤ A.kappa' := by
  intro s t h
  have h' : A.Phi s = A.Phi t := h
  show P.suppHom (A.Phi s) = P.suppHom (A.Phi t)
  rw [h']

end ExactAgent

end Dovetail.Predictor

#print axioms Dovetail.Predictor.StochLang.support_quotient
#print axioms Dovetail.Predictor.StochLang.exists_suppHom
#print axioms Dovetail.Predictor.StochLang.Ssupp_trivial_iff
#print axioms Dovetail.Predictor.ExactAgent.kappa_le_kappa'
