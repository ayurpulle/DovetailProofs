import DovetailProofs.Predictor.Support
import DovetailProofs.Predictor.M3

/-!
# The inherited congruence interval

Formalises Corollary `cor:con-inheritance` of `Lattice/main.tex` (l.1640):

  `Con(S_supp) ≅ [κ', ⊤] ⊆ [κ, ⊤] ≅ Con(S_p) ⊆ Con(S_A)`,

and the transport of non-distributivity (`M₃`, failure of the distributive law) from `Con(S_p)`
to `Con(S_A)`.

The general statement (`conIciEquiv`) is the congruence correspondence theorem for a surjective
monoid homomorphism `f : M → N`: `[ker f, ⊤] ≅ Con N`, with inverse `d ↦ f⁻¹(d)` (`Con.comap`).
The embedding `Con N → Con M` preserves meets and joins (`comap_inf`, `comap_sup`), which is the
paper's "an interval is closed under meets and joins".
-/

namespace Dovetail.Predictor

open Function

section Correspondence

variable {M N : Type*} [Monoid M] [Monoid N]

/-- Pull back a congruence along a monoid homomorphism. -/
def comapCon (f : M →* N) (d : Con N) : Con M := Con.comap f f.map_mul d

/-- Unfolding of `comapCon`. -/
theorem comapCon_rel (f : M →* N) (d : Con N) (x y : M) :
    comapCon f d x y ↔ d (f x) (f y) := Iff.rfl

/-- The pullback of any congruence contains the kernel (main.tex l.1633). -/
theorem ker_le_comapCon (f : M →* N) (d : Con N) : Con.ker f ≤ comapCon f d := by
  intro x y h
  have h' : f x = f y := h
  rw [comapCon_rel, h']
  exact d.refl _

/-- **Congruence correspondence theorem** (cited at main.tex l.1634, l.1662) for a surjective
monoid homomorphism `f : M → N`: the interval `[ker f, ⊤]` of `Con M` is order-isomorphic to
`Con N`. -/
def conIciEquiv (f : M →* N) (hf : Surjective f) : {d : Con M // Con.ker f ≤ d} ≃o Con N :=
  Equiv.toOrderIso
    { toFun := fun d => d.1.mapOfSurjective f d.2 hf
      invFun := fun d => ⟨comapCon f d, ker_le_comapCon f d⟩
      left_inv := fun d => Subtype.ext <| Con.ext fun x y =>
        ⟨fun ⟨a, b, H, hx, hy⟩ =>
          d.1.trans (d.1.symm (d.2 (show f a = f x from hx)))
            (d.1.trans H (d.2 (show f b = f y from hy))),
          fun h => ⟨x, y, h, rfl, rfl⟩⟩
      right_inv := fun d => Con.ext fun x y => by
        constructor
        · rintro ⟨a, b, H, rfl, rfl⟩
          exact H
        · intro h
          obtain ⟨a, rfl⟩ := hf x
          obtain ⟨b, rfl⟩ := hf y
          exact ⟨a, b, h, rfl, rfl⟩ }
    (fun _ _ hst _ _ ⟨a, b, H, hx, hy⟩ => ⟨a, b, hst H, hx, hy⟩)
    (fun _ _ hst _ _ h => hst h)

/-- The inverse of the correspondence is the pullback (main.tex l.1634). -/
theorem conIciEquiv_symm_coe (f : M →* N) (hf : Surjective f) (d : Con N) :
    ((conIciEquiv f hf).symm d : Con M) = comapCon f d := rfl

/-- The pullback along a surjection is injective (main.tex l.1634). -/
theorem comapCon_injective (f : M →* N) (hf : Surjective f) : Injective (comapCon f) := by
  intro d d' h
  apply (conIciEquiv f hf).symm.injective
  exact Subtype.ext h

/-- The pullback along a surjection reflects the order (main.tex l.1634). -/
theorem comapCon_le_iff (f : M →* N) (hf : Surjective f) {d d' : Con N} :
    comapCon f d ≤ comapCon f d' ↔ d ≤ d' := by
  have := (conIciEquiv f hf).symm.le_iff_le (x := d) (y := d')
  rw [← this]
  exact Iff.rfl

/-- The pullback preserves meets (main.tex l.1657). -/
theorem comapCon_inf (f : M →* N) (d d' : Con N) :
    comapCon f (d ⊓ d') = comapCon f d ⊓ comapCon f d' := by
  refine Con.ext fun x y => ?_
  rw [comapCon_rel, Con.inf_iff_and, Con.inf_iff_and, comapCon_rel, comapCon_rel]

/-- The pullback along a surjection preserves joins: the interval `[ker f, ⊤]` is closed under
joins (main.tex l.1657). -/
theorem comapCon_sup (f : M →* N) (hf : Surjective f) (d d' : Con N) :
    comapCon f (d ⊔ d') = comapCon f d ⊔ comapCon f d' := by
  apply le_antisymm
  · -- the join of the pullbacks lies in the interval, hence is a pullback
    have hker : Con.ker f ≤ comapCon f d ⊔ comapCon f d' :=
      (ker_le_comapCon f d).trans le_sup_left
    set D : {c : Con M // Con.ker f ≤ c} := ⟨comapCon f d ⊔ comapCon f d', hker⟩ with hD
    have hD' : comapCon f (conIciEquiv f hf D) = comapCon f d ⊔ comapCon f d' := by
      rw [← conIciEquiv_symm_coe f hf, OrderIso.symm_apply_apply]
    rw [← hD', comapCon_le_iff f hf]
    refine sup_le ?_ ?_
    · rw [← comapCon_le_iff f hf, hD']; exact le_sup_left
    · rw [← comapCon_le_iff f hf, hD']; exact le_sup_right
  · refine sup_le ?_ ?_
    · exact (comapCon_le_iff f hf).2 le_sup_left
    · exact (comapCon_le_iff f hf).2 le_sup_right

/-- An isomorphism of monoids induces an isomorphism of congruence lattices. -/
def conCongr (e : M ≃* N) : Con M ≃o Con N :=
  Equiv.toOrderIso
    { toFun := fun d => comapCon e.symm.toMonoidHom d
      invFun := fun d => comapCon e.toMonoidHom d
      left_inv := fun d => Con.ext fun x y => by
        simp [comapCon_rel]
      right_inv := fun d => Con.ext fun x y => by
        simp [comapCon_rel] }
    (fun _ _ hst _ _ h => hst h)
    (fun _ _ hst _ _ h => hst h)

/-- **Non-distributivity passes from a quotient to the monoid** (Corollary
`cor:con-inheritance`, main.tex l.1655). -/
theorem NonDistrib.of_surjective (f : M →* N) (hf : Surjective f) (h : NonDistrib (Con N)) :
    NonDistrib (Con M) :=
  h.map (comapCon f) (comapCon_injective f hf) (comapCon_inf f) (comapCon_sup f hf)

/-- **Every `M₃` of the quotient occurs inside the interval `[ker f, ⊤]`** (Corollary
`cor:con-inheritance`, main.tex l.1656). -/
theorem IsM3.of_surjective (f : M →* N) (hf : Surjective f) {bot a b c top : Con N}
    (h : IsM3 bot a b c top) :
    IsM3 (comapCon f bot) (comapCon f a) (comapCon f b) (comapCon f c) (comapCon f top) ∧
      Con.ker f ≤ comapCon f bot :=
  ⟨h.map (comapCon f) (comapCon_injective f hf) (comapCon_inf f) (comapCon_sup f hf),
    ker_le_comapCon f bot⟩

end Correspondence

namespace ExactAgent

variable {O : Type*} [Fintype O] {P : StochLang O} {Q : Type*} (A : ExactAgent P Q)

/-- **Corollary `cor:con-inheritance`** (main.tex l.1640): `[κ, ⊤] ≅ Con(S_p)` inside
`Con(S_A)`. -/
noncomputable def intervalEquiv : {d : Con A.SA // A.kappa ≤ d} ≃o Con P.Sp :=
  conIciEquiv A.Phi A.Phi_surjective

/-- **Corollary `cor:con-inheritance`** (main.tex l.1640): `[κ', ⊤] ≅ Con(S_supp)` inside
`Con(S_A)`. -/
noncomputable def intervalSuppEquiv : {d : Con A.SA // A.kappa' ≤ d} ≃o Con P.Ssupp :=
  conIciEquiv A.PhiSupp A.PhiSupp_surjective

/-- **Corollary `cor:con-inheritance`** (main.tex l.1648): `[κ', ⊤] ⊆ [κ, ⊤]`. -/
theorem interval_subset {d : Con A.SA} (h : A.kappa' ≤ d) : A.kappa ≤ d :=
  A.kappa_le_kappa'.trans h

/-- **Corollary `cor:con-inheritance`, "in particular"** (main.tex l.1655): if `Con(S_p)` is
non-distributive then so is `Con(S_A)`. -/
theorem nonDistrib_of_Sp (h : NonDistrib (Con P.Sp)) : NonDistrib (Con A.SA) :=
  NonDistrib.of_surjective A.Phi A.Phi_surjective h

/-- **Corollary `cor:con-inheritance`, "in particular"** (main.tex l.1656): every `M₃` sublattice
of `Con(S_p)` occurs inside the interval `[κ, ⊤]` of `Con(S_A)`. -/
theorem exists_isM3_of_Sp {bot a b c top : Con P.Sp} (h : IsM3 bot a b c top) :
    ∃ bot' a' b' c' top' : Con A.SA, IsM3 bot' a' b' c' top' ∧ A.kappa ≤ bot' :=
  ⟨_, _, _, _, _, IsM3.of_surjective A.Phi A.Phi_surjective h⟩

end ExactAgent

end Dovetail.Predictor

#print axioms Dovetail.Predictor.conIciEquiv
#print axioms Dovetail.Predictor.comapCon_sup
#print axioms Dovetail.Predictor.ExactAgent.intervalEquiv
#print axioms Dovetail.Predictor.ExactAgent.nonDistrib_of_Sp
#print axioms Dovetail.Predictor.ExactAgent.exists_isM3_of_Sp
