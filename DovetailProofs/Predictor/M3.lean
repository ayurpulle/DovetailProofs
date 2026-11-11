import Mathlib

/-!
# `M₃` configurations and failure of distributivity

Lattice-theoretic vocabulary for Section 8 of `Lattice/main.tex` (l.1636, Figure `fig:m3n5`
l.1876): an `M₃` sublattice is a quintuple `(⊥', a, b, c, ⊤')` with `a, b, c` pairwise distinct,
all pairwise meets equal to `⊥'` and all pairwise joins equal to `⊤'`.  Such a quintuple is closed
under `⊓` and `⊔`, has five distinct elements (`IsM3.ne_bot`, `IsM3.ne_top`), and witnesses the
failure of the distributive law (`IsM3.not_distrib`).  It is carried along any injective map
preserving `⊓` and `⊔` (`IsM3.map`), which is how the paper transports it into an interval
(Corollary `cor:con-inheritance`, l.1655).
-/

namespace Dovetail.Predictor

/-- An `M₃` sublattice `{bot, a, b, c, top}` of a lattice (Figure `fig:m3n5`, main.tex l.1876):
three pairwise distinct elements any two of which meet at `bot` and join at `top`. -/
structure IsM3 {L : Type*} [Lattice L] (bot a b c top : L) : Prop where
  /-- `a ≠ b`. -/
  ab : a ≠ b
  /-- `b ≠ c`. -/
  bc : b ≠ c
  /-- `a ≠ c`. -/
  ac : a ≠ c
  /-- `a ⊓ b = ⊥'`. -/
  inf_ab : a ⊓ b = bot
  /-- `b ⊓ c = ⊥'`. -/
  inf_bc : b ⊓ c = bot
  /-- `a ⊓ c = ⊥'`. -/
  inf_ac : a ⊓ c = bot
  /-- `a ⊔ b = ⊤'`. -/
  sup_ab : a ⊔ b = top
  /-- `b ⊔ c = ⊤'`. -/
  sup_bc : b ⊔ c = top
  /-- `a ⊔ c = ⊤'`. -/
  sup_ac : a ⊔ c = top

namespace IsM3

variable {L : Type*} [Lattice L] {bot a b c top : L}

/-- In an `M₃` configuration the atom `a` is not the bottom (Figure `fig:m3n5`, main.tex
l.1907). -/
theorem ne_bot (h : IsM3 bot a b c top) : a ≠ bot := by
  intro hab
  -- `a = bot ≤ b, c`, so `b = a ⊔ b = top = a ⊔ c = c`
  have h1 : a ≤ b := by rw [hab, ← h.inf_ab]; exact inf_le_right
  have h2 : a ≤ c := by rw [hab, ← h.inf_ac]; exact inf_le_right
  have hb : b = top := by rw [← h.sup_ab]; exact (sup_eq_right.2 h1).symm
  have hc : c = top := by rw [← h.sup_ac]; exact (sup_eq_right.2 h2).symm
  exact h.bc (hb.trans hc.symm)

/-- In an `M₃` configuration the atom `a` is not the top (Figure `fig:m3n5`, main.tex l.1907). -/
theorem ne_top (h : IsM3 bot a b c top) : a ≠ top := by
  intro hat
  have h1 : b ≤ a := by rw [hat, ← h.sup_ab]; exact le_sup_right
  have h2 : c ≤ a := by rw [hat, ← h.sup_ac]; exact le_sup_right
  have hb : b = bot := by rw [← h.inf_ab]; exact (inf_eq_right.2 h1).symm
  have hc : c = bot := by rw [← h.inf_ac]; exact (inf_eq_right.2 h2).symm
  exact h.bc (hb.trans hc.symm)

/-- An `M₃` configuration violates the distributive law (main.tex l.1636, l.1873). -/
theorem not_distrib (h : IsM3 bot a b c top) : a ⊓ (b ⊔ c) ≠ (a ⊓ b) ⊔ (a ⊓ c) := by
  rw [h.sup_bc, h.inf_ab, h.inf_ac, sup_idem]
  have : a ≤ top := by rw [← h.sup_ab]; exact le_sup_left
  rw [inf_eq_left.2 this]
  exact h.ne_bot

/-- `M₃` configurations are carried along injective maps preserving `⊓` and `⊔`
(main.tex l.1655: "an interval is closed under meets and joins"). -/
theorem map {L' : Type*} [Lattice L'] (h : IsM3 bot a b c top) (f : L → L')
    (hf : Function.Injective f) (hinf : ∀ x y, f (x ⊓ y) = f x ⊓ f y)
    (hsup : ∀ x y, f (x ⊔ y) = f x ⊔ f y) : IsM3 (f bot) (f a) (f b) (f c) (f top) where
  ab := fun e => h.ab (hf e)
  bc := fun e => h.bc (hf e)
  ac := fun e => h.ac (hf e)
  inf_ab := by rw [← hinf, h.inf_ab]
  inf_bc := by rw [← hinf, h.inf_bc]
  inf_ac := by rw [← hinf, h.inf_ac]
  sup_ab := by rw [← hsup, h.sup_ab]
  sup_bc := by rw [← hsup, h.sup_bc]
  sup_ac := by rw [← hsup, h.sup_ac]

end IsM3

/-- A lattice is **non-distributive** when the distributive law fails for some triple
(main.tex l.1636). -/
def NonDistrib (L : Type*) [Lattice L] : Prop :=
  ∃ a b c : L, a ⊓ (b ⊔ c) ≠ (a ⊓ b) ⊔ (a ⊓ c)

/-- A lattice containing an `M₃` is non-distributive (main.tex l.1636). -/
theorem IsM3.nonDistrib {L : Type*} [Lattice L] {bot a b c top : L} (h : IsM3 bot a b c top) :
    NonDistrib L := ⟨a, b, c, h.not_distrib⟩

/-- Non-distributivity is carried along injective maps preserving `⊓` and `⊔`
(Corollary `cor:con-inheritance`, main.tex l.1655). -/
theorem NonDistrib.map {L L' : Type*} [Lattice L] [Lattice L'] (h : NonDistrib L) (f : L → L')
    (hf : Function.Injective f) (hinf : ∀ x y, f (x ⊓ y) = f x ⊓ f y)
    (hsup : ∀ x y, f (x ⊔ y) = f x ⊔ f y) : NonDistrib L' := by
  obtain ⟨a, b, c, habc⟩ := h
  refine ⟨f a, f b, f c, fun e => habc (hf ?_)⟩
  simp only [hinf, hsup]
  exact e

end Dovetail.Predictor
