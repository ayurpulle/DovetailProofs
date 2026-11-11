import DovetailProofs.Predictor.Support

/-!
# Both canonical monoids are syntactic

Formalises Section 5.1 of `Lattice/main.tex`: the syntactic congruence and monoid of a map
`f : O* → Y` (l.699) and Lemma `lem:syntactic` (l.729):

* (i) `tau_eq_iff_synEq`: `τ_w = τ_{w'} ↔ w ≡_ν w'`, and `synMonoidEquiv : M(ν) ≃* S_pᵐᵒᵖ`
  (equivalently `S_p ≅ M(ν)ᵒᵖ`);
* (ii) `sigma_eq_iff_synEq`: `σ_w = σ_{w'} ↔ w ≡_{L_p} w'`, and
  `synMonoidSuppEquiv : M(L_p) ≃* S_suppᵐᵒᵖ`;
* (iii) `synEq_nu_iff`: `≡_ν = ⋂_{x ∈ X_p} ≡_{K_x}`; `synCon_nu_le` gives `≡_ν ⊆ ≡_{K_x}`, i.e. each
  `M(K_x)` is a quotient of `M(ν)`.  The embedding of `M(ν)` in `∏_x M(K_x)` is the statement
  that the intersection is `≡_ν`; the product monoid itself is not constructed.

Words in the congruence are elements of `FreeMonoid O` (definitionally lists), so that the
syntactic congruence is a `Con (FreeMonoid O)`.
-/

namespace Dovetail.Predictor

open Function

section SynCon

variable {O Y : Type*}

/-- The syntactic relation of `f : O* → Y` (main.tex l.699):
`w ≡_f w' ↔ f(uwv) = f(uw'v)` for all `u, v`. -/
def SynEq (f : List O → Y) (w w' : List O) : Prop :=
  ∀ u v : List O, f (u ++ w ++ v) = f (u ++ w' ++ v)

/-- The **syntactic congruence** `≡_f` on the free monoid `O*` (main.tex l.699). -/
def synCon (f : List O → Y) : Con (FreeMonoid O) where
  r w w' := SynEq f (FreeMonoid.toList w) (FreeMonoid.toList w')
  iseqv :=
    { refl := fun _ _ _ => rfl
      symm := fun h u v => (h u v).symm
      trans := fun h h' u v => (h u v).trans (h' u v) }
  mul' := fun {w x y z} h h' u v => by
    have e1 := h u (FreeMonoid.toList y ++ v)
    have e2 := h' (u ++ FreeMonoid.toList x) v
    simp only [FreeMonoid.toList_mul, List.append_assoc] at e1 e2 ⊢
    exact e1.trans e2

/-- Unfolding of the syntactic congruence (main.tex l.699). -/
theorem synCon_rel (f : List O → Y) (w w' : FreeMonoid O) :
    synCon f w w' ↔ SynEq f (FreeMonoid.toList w) (FreeMonoid.toList w') := Iff.rfl

/-- The **syntactic monoid** `M(f) = O* / ≡_f` (main.tex l.705). -/
abbrev SynMonoid (f : List O → Y) : Type _ := (synCon f).Quotient

end SynCon

namespace StochLang

variable {O : Type*} [Fintype O] (P : StochLang O)

/-- Two self-maps of `X̂_p` that fix `†` and agree on every `ν(u)` with `u` possible are equal
(proof of Lemma `lem:syntactic`(i), main.tex l.745: "every live state is `ν(u)` for some `u`"). -/
theorem ext_nu {f g : Option P.X → Option P.X} (h0 : f none = g none)
    (h : ∀ u, 0 < P.p u → f (P.nu u) = g (P.nu u)) : f = g := by
  funext y
  cases y with
  | none => exact h0
  | some x =>
    obtain ⟨u, hu, hx⟩ := P.exists_nu_eq_some x
    rw [← hx]; exact h u hu

/-- The analogue of `ext_nu` for support states (proof of Lemma `lem:syntactic`(ii),
main.tex l.757). -/
theorem ext_mu {f g : Option P.Xsupp → Option P.Xsupp} (h0 : f none = g none)
    (h : ∀ u, 0 < P.p u → f (P.mu u) = g (P.mu u)) : f = g := by
  funext y
  cases y with
  | none => exact h0
  | some F =>
    obtain ⟨F, u, hu, rfl⟩ := F
    have : (some ⟨P.follower u, u, hu, rfl⟩ : Option P.Xsupp) = P.mu u := (P.mu_of_pos hu).symm
    rw [this]; exact h u hu

/-- `τ_w = τ_{w'}` exactly when `ν(uw) = ν(uw')` for every `u` (proof of Lemma
`lem:syntactic`(i), main.tex l.749). -/
theorem tau_eq_iff_forall_nu (w w' : List O) :
    run P.tau w = run P.tau w' ↔ ∀ u, P.nu (u ++ w) = P.nu (u ++ w') := by
  constructor
  · intro h u
    rw [← P.run_tau_nu, ← P.run_tau_nu, h]
  · intro h
    refine P.ext_nu (by simp) fun u _ => ?_
    rw [P.run_tau_nu, P.run_tau_nu, h]

/-- **Lemma `lem:syntactic`(i)** (main.tex l.733): `τ_w = τ_{w'}` if and only if `w ≡_ν w'`. -/
theorem tau_eq_iff_synEq (w w' : List O) :
    run P.tau w = run P.tau w' ↔ SynEq P.nu w w' := by
  rw [P.tau_eq_iff_forall_nu]
  constructor
  · intro h u v
    rw [← P.run_tau_nu v, ← P.run_tau_nu v, h]
  · intro h u
    simpa using h u []

/-- The map `w ↦ τ_w` as a monoid homomorphism `O* → S_pᵐᵒᵖ`; it reverses products because
`τ_w ∘ τ_v = τ_{vw}` (main.tex l.751). -/
noncomputable def wordHom : FreeMonoid O →* (P.Sp)ᵐᵒᵖ where
  toFun w := MulOpposite.op ⟨run P.tau (FreeMonoid.toList w), run_mem_transitionMonoid _ _⟩
  map_one' := rfl
  map_mul' w w' := by
    apply MulOpposite.unop_injective
    apply Subtype.ext
    exact run_append_eq P.tau (FreeMonoid.toList w) (FreeMonoid.toList w')

/-- `w ↦ τ_w` is onto `S_p` (main.tex l.305). -/
theorem wordHom_surjective : Surjective P.wordHom := by
  intro s
  obtain ⟨⟨s, hs⟩⟩ := s
  obtain ⟨w, rfl⟩ := (P.mem_Sp_iff s).1 hs
  exact ⟨FreeMonoid.ofList w, rfl⟩

/-- The kernel of `w ↦ τ_w` is the syntactic congruence of `ν` (Lemma `lem:syntactic`(i),
main.tex l.733). -/
theorem ker_wordHom : Con.ker P.wordHom = synCon P.nu := by
  refine Con.ext fun w w' => ?_
  rw [Con.ker_rel, synCon_rel, ← P.tau_eq_iff_synEq]
  constructor
  · intro h
    exact congrArg (fun s : (P.Sp)ᵐᵒᵖ => (s.unop : Function.End (Option P.X))) h
  · intro h
    apply MulOpposite.unop_injective
    exact Subtype.ext h

/-- **Lemma `lem:syntactic`(i), second sentence** (main.tex l.734): `[w] ↦ τ_w` is an isomorphism
`M(ν) ≅ S_pᵒᵖ`; equivalently `S_p ≅ M(ν)ᵒᵖ`. -/
noncomputable def synMonoidEquiv : SynMonoid P.nu ≃* (P.Sp)ᵐᵒᵖ :=
  (Con.congr P.ker_wordHom.symm).trans
    (Con.quotientKerEquivOfSurjective P.wordHom P.wordHom_surjective)

/-- `σ_w = σ_{w'}` exactly when `F_{uw} = F_{uw'}` for every `u` (proof of Lemma
`lem:syntactic`(ii), main.tex l.758). -/
theorem sigma_eq_iff_forall_follower (w w' : List O) :
    run P.sigmaStep w = run P.sigmaStep w' ↔
      ∀ u, P.follower (u ++ w) = P.follower (u ++ w') := by
  simp only [← P.mu_eq_mu_iff]
  constructor
  · intro h u
    rw [← P.run_sigmaStep_mu, ← P.run_sigmaStep_mu, h]
  · intro h
    refine P.ext_mu (by simp) fun u _ => ?_
    rw [P.run_sigmaStep_mu, P.run_sigmaStep_mu, h]

/-- **Lemma `lem:syntactic`(ii)** (main.tex l.736): `σ_w = σ_{w'}` if and only if
`w ≡_{L_p} w'`, the syntactic congruence of (the indicator of) the language of possible words. -/
theorem sigma_eq_iff_synEq (w w' : List O) :
    run P.sigmaStep w = run P.sigmaStep w' ↔ SynEq (fun u => u ∈ P.Lp) w w' := by
  rw [P.sigma_eq_iff_forall_follower]
  constructor
  · intro h u v
    have := congrArg (fun F : Set (List O) => v ∈ F) (h u)
    simpa [follower, Lp] using this
  · intro h u
    ext v
    have := h u v
    simp only [Lp, Set.mem_setOf_eq, eq_iff_iff] at this
    simpa [follower] using this

/-- The map `w ↦ σ_w` as a monoid homomorphism `O* → S_suppᵐᵒᵖ` (main.tex l.737). -/
noncomputable def wordHomSupp : FreeMonoid O →* (P.Ssupp)ᵐᵒᵖ where
  toFun w := MulOpposite.op ⟨run P.sigmaStep (FreeMonoid.toList w), run_mem_transitionMonoid _ _⟩
  map_one' := rfl
  map_mul' w w' := by
    apply MulOpposite.unop_injective
    apply Subtype.ext
    exact run_append_eq P.sigmaStep (FreeMonoid.toList w) (FreeMonoid.toList w')

/-- `w ↦ σ_w` is onto `S_supp` (main.tex l.537). -/
theorem wordHomSupp_surjective : Surjective P.wordHomSupp := by
  intro s
  obtain ⟨⟨s, hs⟩⟩ := s
  obtain ⟨w, rfl⟩ := (mem_transitionMonoid_iff P.sigmaStep s).1 hs
  exact ⟨FreeMonoid.ofList w, rfl⟩

/-- The kernel of `w ↦ σ_w` is the syntactic congruence of `L_p` (Lemma `lem:syntactic`(ii),
main.tex l.736). -/
theorem ker_wordHomSupp : Con.ker P.wordHomSupp = synCon (fun u => u ∈ P.Lp) := by
  refine Con.ext fun w w' => ?_
  rw [Con.ker_rel, synCon_rel, ← P.sigma_eq_iff_synEq]
  constructor
  · intro h
    exact congrArg (fun s : (P.Ssupp)ᵐᵒᵖ => (s.unop : Function.End (Option P.Xsupp))) h
  · intro h
    apply MulOpposite.unop_injective
    exact Subtype.ext h

/-- **Lemma `lem:syntactic`(ii), second sentence** (main.tex l.737): `M(L_p) ≅ S_suppᵒᵖ`;
equivalently `S_supp ≅ M(L_p)ᵒᵖ`. -/
noncomputable def synMonoidSuppEquiv : SynMonoid (fun u => u ∈ P.Lp) ≃* (P.Ssupp)ᵐᵒᵖ :=
  (Con.congr P.ker_wordHomSupp.symm).trans
    (Con.quotientKerEquivOfSurjective P.wordHomSupp P.wordHomSupp_surjective)

/-- `K_x = {u : ν(u) = x}`, the set of histories that lead to the live state `x`
(main.tex l.723). -/
def K (x : P.X) : Set (List O) := {u | P.nu u = some x}

/-- **Lemma `lem:syntactic`(iii)** (main.tex l.738): `≡_ν = ⋂_{x ∈ X_p} ≡_{K_x}`. -/
theorem synEq_nu_iff (w w' : List O) :
    SynEq P.nu w w' ↔ ∀ x : P.X, SynEq (fun u => u ∈ P.K x) w w' := by
  constructor
  · intro h x u v
    show (P.nu (u ++ w ++ v) = some x) = (P.nu (u ++ w' ++ v) = some x)
    rw [h u v]
  · intro h u v
    have key : ∀ x : P.X, P.nu (u ++ w ++ v) = some x ↔ P.nu (u ++ w' ++ v) = some x :=
      fun x => iff_of_eq (h x u v)
    cases ha : P.nu (u ++ w ++ v) with
    | some x => exact ((key x).1 ha).symm
    | none =>
      cases hb : P.nu (u ++ w' ++ v) with
      | none => rfl
      | some x => rw [(key x).2 hb] at ha; exact absurd ha (Option.some_ne_none _)

/-- `≡_ν ⊆ ≡_{K_x}`: each `M(K_x)` is a quotient of `M(ν)` (Lemma `lem:syntactic`(iii),
main.tex l.739). -/
theorem synCon_nu_le (x : P.X) : synCon P.nu ≤ synCon (fun u => u ∈ P.K x) := by
  intro w w' h
  exact (P.synEq_nu_iff _ _).1 h x

end StochLang

end Dovetail.Predictor

#print axioms Dovetail.Predictor.StochLang.tau_eq_iff_synEq
#print axioms Dovetail.Predictor.StochLang.synMonoidEquiv
#print axioms Dovetail.Predictor.StochLang.sigma_eq_iff_synEq
#print axioms Dovetail.Predictor.StochLang.synMonoidSuppEquiv
#print axioms Dovetail.Predictor.StochLang.synEq_nu_iff
