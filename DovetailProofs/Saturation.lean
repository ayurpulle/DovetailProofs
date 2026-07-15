import Mathlib
import DovetailProofs.Descent

/-!
# `Con_f` completion and the saturation lemma

Completes the filter lemma of the paper's §8 replacement block and adds the
saturation lemma of the new finiteness subsection:

1. Boundary clauses: `⊤ ∈ Con_f` always; `⊥ ∈ Con_f ↔ M` finite.
2. Join closure (from the up-set property), and closure under finite
   (`Finset`-indexed) meets, by induction from the binary case.
3. **Saturation**: `Con_f` is finite iff it has a minimum `κ_f`
   (iff `M` admits a maximal finite quotient), in which case
   `Con_f = [κ_f, ⊤]`.

Design: `Con.FiniteIndex` stays a predicate; "`Con_f` as a set" is the
subtype `{c : Con M // c.FiniteIndex}`. No bundled sublattice object.

Depends on `Con.FiniteIndex`, `Con.FiniteIndex.of_le`,
`Con.FiniteIndex.inf` from `DovetailProofs.Descent`.
-/

namespace Dovetail

section ConfCompletion

variable {M : Type*} [Monoid M]

/-- `⊤` always has finite index: its quotient is a subsingleton.

Proof plan: `(⊤ : Con M).Quotient` is a subsingleton since `⊤` relates
everything (`Con.top_iff` / `trivial`); a subsingleton is finite.
Try `Finite.of_subsingleton` after establishing
`Subsingleton (⊤ : Con M).Quotient` via `Quotient.ind₂` and `Con.eq`. -/
theorem _root_.Con.FiniteIndex.top : (⊤ : Con M).FiniteIndex := by
  letI : Subsingleton (⊤ : Con M).Quotient :=
    ⟨fun x y => by
      induction x, y using Con.induction_on₂ with
      | _ x y => exact (⊤ : Con M).eq.2 trivial⟩
  exact Finite.of_subsingleton

/-- `⊥` has finite index iff `M` is finite: the `⊥`-quotient bijects
with `M`.

Proof plan: build `e : (⊥ : Con M).Quotient ≃ M` — `Con.mk'` in one
direction, `Quotient.lift id` in the other, using that `⊥` relates only
equal elements (`Con.bot_iff` / `Con.eq` at `⊥`). Then
`Finite.of_equiv` / `e.finite_iff` in both directions. Mathlib may
already have `Con.quotientBotEquiv` or similar; Loogle for
`Con` `⊥` `Quotient` `≃` first. -/
theorem _root_.Con.FiniteIndex.bot_iff :
    (⊥ : Con M).FiniteIndex ↔ Finite M := by
  constructor
  · intro h
    letI : Finite (⊥ : Con M).Quotient := h
    exact Finite.of_injective
      (fun x : M => (x : (⊥ : Con M).Quotient))
      (fun _ _ hxy => (⊥ : Con M).eq.1 hxy)
  · intro h
    letI : Finite M := h
    exact Finite.of_surjective
      (fun x : M => (x : (⊥ : Con M).Quotient))
      (fun q => Con.induction_on q fun x => ⟨x, rfl⟩)

/-- Join closure: one finite-index factor suffices. Immediate from the
up-set property. -/
theorem _root_.Con.FiniteIndex.sup {c d : Con M} (hc : c.FiniteIndex) :
    (c ⊔ d).FiniteIndex :=
  hc.of_le le_sup_left

/-- Closure under `Finset`-indexed meets: the finite-meet clause of the
filter lemma, from the binary case by induction.

Proof plan: `Finset.induction_on s`. Empty case: the infimum over `∅` is
`⊤` (`Finset.inf_empty`), use `Con.FiniteIndex.top`. Insert case:
`Finset.inf_insert` rewrites to a binary `⊓`, close with
`Con.FiniteIndex.inf` and the induction hypothesis. -/
theorem _root_.Con.FiniteIndex.finsetInf {ι : Type*} (s : Finset ι)
    (f : ι → Con M) (hf : ∀ i ∈ s, (f i).FiniteIndex) :
    (s.inf f).FiniteIndex := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (Con.FiniteIndex.top : (⊤ : Con M).FiniteIndex)
  | @insert a s ha ih =>
      rw [Finset.inf_insert]
      exact Con.FiniteIndex.inf
        (hf a (Finset.mem_insert_self a s))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end ConfCompletion

section Saturation

variable {M : Type*} [Monoid M]

/-- `M` admits a maximal finite quotient: a finite-index congruence below
every finite-index congruence. (Its quotient `M/κ_f` is the maximal
finite quotient `S_f`; the universal property — every finite quotient
factors through it — is the correspondence-theoretic reading of `κ_f ≤ c`
and is not restated separately.) -/
def AdmitsMaximalFiniteQuotient (M : Type*) [Monoid M] : Prop :=
  ∃ κ : Con M, κ.FiniteIndex ∧ ∀ c : Con M, c.FiniteIndex → κ ≤ c

/-- **Saturation, forward direction**: if the finite-index congruences
form a finite collection, they have a minimum.

Proof plan: let `s : Finset (Con M)` enumerate the subtype
`{c : Con M // c.FiniteIndex}` (via `Set.Finite.toFinset` after
converting `Finite` to `Set.Finite`, or `Finset.univ.image Subtype.val`
under the `Fintype` from `h`). The subtype is nonempty
(`Con.FiniteIndex.top`). Take `κ := s.inf id`; it has finite index by
`Con.FiniteIndex.finsetInf`, and is `≤ c` for each member by
`Finset.inf_le`. -/
theorem admitsMaximalFiniteQuotient_of_finite
    (h : Finite {c : Con M // c.FiniteIndex}) :
    AdmitsMaximalFiniteQuotient M := by
  classical
  letI : Finite {c : Con M // c.FiniteIndex} := h
  letI := Fintype.ofFinite {c : Con M // c.FiniteIndex}
  let κ : Con M := Finset.univ.inf fun c : {c : Con M // c.FiniteIndex} => c.1
  refine ⟨κ, ?_, ?_⟩
  · exact Con.FiniteIndex.finsetInf Finset.univ
      (fun c : {c : Con M // c.FiniteIndex} => c.1)
      (fun c _ => c.2)
  · intro c hc
    dsimp [κ]
    exact Finset.inf_le
      (Finset.mem_univ (⟨c, hc⟩ : {c : Con M // c.FiniteIndex}))

/-- **Interval identification**: given the minimum `κ_f`, the finite-index
congruences are exactly the interval `[κ_f, ⊤]`.

Proof plan: `←` is the up-set property `Con.FiniteIndex.of_le` applied to
`hκ.1`; `→` is `hκ.2`. Pure unfolding — this should be a few lines with
`Set.ext` and `Set.mem_Icc`, with `le_top` discharging the upper bound. -/
theorem finiteIndex_iff_mem_Icc {κ : Con M}
    (hκ : κ.FiniteIndex ∧ ∀ c : Con M, c.FiniteIndex → κ ≤ c) :
    ∀ c : Con M, c.FiniteIndex ↔ c ∈ Set.Icc κ ⊤ := by
  intro c
  constructor
  · intro hc
    exact ⟨hκ.2 c hc, le_top⟩
  · intro hc
    exact hκ.1.of_le hc.1

/-- **Saturation, reverse direction**: given the minimum, the finite-index
congruences form a finite collection.

Proof plan: by `finiteIndex_iff_mem_Icc` the subtype bijects with
`Set.Icc κ ⊤ ⊆ Con M`, and by the correspondence theorem
(`Con.correspondence κ : {d // κ ≤ d} ≃o Con κ.Quotient`) that interval
bijects with `Con κ.Quotient` — the congruence lattice of a finite type
(`hκ.1 : Finite κ.Quotient`). Congruences on a finite type form a finite
set: a congruence is determined by its underlying binary relation, so
inject `Con κ.Quotient → (κ.Quotient → κ.Quotient → Prop)`, a finite
type under `Finite` + `Prop` finiteness (may need `Classical.dec` /
`Finite.of_injective` with `FunLike.coe_injective` or `Con.ext`). This
last injection is the only real work; Loogle for `Finite (Con _)` first
in case mathlib has the instance. -/
theorem finite_of_admitsMaximalFiniteQuotient
    (h : AdmitsMaximalFiniteQuotient M) :
    Finite {c : Con M // c.FiniteIndex} := by
  classical
  rcases h with ⟨κ, hκ, hmin⟩
  letI : Finite κ.Quotient := hκ
  letI : Finite (Con κ.Quotient) :=
    Finite.of_injective
      (fun c : Con κ.Quotient =>
        (c : κ.Quotient → κ.Quotient → Prop))
      (fun _ _ hcd => Con.ext' hcd)
  exact Finite.of_injective
    (fun c : {c : Con M // c.FiniteIndex} =>
      Con.correspondence ⟨c.1, hmin c.1 c.2⟩)
    (fun c d hcd => by
      apply Subtype.ext
      have hsub :=
        (Con.correspondence (c := κ)).injective hcd
      exact congrArg
        (fun c : {c : Con M // κ ≤ c} => c.1) hsub)

/-- **The saturation lemma** (paper, finiteness subsection): the
agent-admissible lattice is finite iff the world admits a maximal finite
quotient. Packaging of the two directions. -/
theorem saturation_iff :
    Finite {c : Con M // c.FiniteIndex} ↔ AdmitsMaximalFiniteQuotient M :=
  ⟨admitsMaximalFiniteQuotient_of_finite,
   finite_of_admitsMaximalFiniteQuotient⟩

/- Next targets after this compiles, in order:
1. `Con_f(S) ≅ Con(S_f)`: compose `finiteIndex_iff_mem_Icc` with
   `Con.correspondence κ_f` to land in `Con κ_f.Quotient` as an order
   isomorphism. This is the same `Con.correspondence` plumbing the
   inheritance theorem needs — rehearsal with lower stakes.
2. Inheritance: `Con S ≅ [κ, ⊤] ⊆ Con S_agent` via
   `Con.quotientKerEquivOfSurjective` + `Con.correspondence`, then its
   index-exact restriction (the paper's Proposition).
3. M₃ embedding definition + certificates. -/

end Saturation

end Dovetail

#print axioms Dovetail.saturation_iff
