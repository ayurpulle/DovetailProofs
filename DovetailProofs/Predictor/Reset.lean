import Mathlib
import DovetailProofs.Predictor.M3

/-!
# The reset monoid `R_n^1` and its congruence lattice

Formalises Theorem `thm:reset-con` of `Lattice/main.tex` (l.1766) and the Corollary after it
(l.1798):

* `Reset α` is `R_n^1 = {1, c_i : i ∈ α}` with `c_i c_j = c_i` (for `α = Fin n` this is the
  paper's `R_n^1`; nothing below needs `α` finite);
* `Reset.eq_top_of_one_rel`, `Reset.one_class`: a congruence identifying `1` with a constant is
  universal, so every non-universal congruence has `{1}` as a singleton class;
* `Reset.ofSetoid`: every equivalence relation on the constants, with `1` kept alone, is a
  congruence;
* `Reset.conEquiv : Con (Reset α) ≃o WithTop (Setoid α)` for nonempty `α`: this is
  `Con(R_n^1) ≅ Π_n ⊕ 𝟏`, the partition lattice (`Setoid α` ordered by refinement) with a new top;
* `Reset.exists_isM3`, `Reset.nonDistrib`: for three distinct constants, `Con(R_n^1)` contains an
  `M₃` and is non-distributive;
* `Reset.isM3_fin3`: for `n = 3` the `M₃` is `{⊥, ·, ·, ·, θ}` with `θ` the congruence merging the
  three reset maps and keeping the identity separate (Corollary, l.1798).
-/

namespace Dovetail.Predictor

/-- The reset monoid `R^1 = {1} ∪ {c_i : i ∈ α}` with `c_i c_j = c_i` (Theorem `thm:reset-con`,
main.tex l.1768).  `none` is the identity and `some i` is the constant (reset) `c_i`. -/
def Reset (α : Type*) : Type _ := Option α

namespace Reset

variable {α : Type*}

/-- The constant `c_i` (main.tex l.1710, l.1770). -/
def c (i : α) : Reset α := some i

instance : Monoid (Reset α) where
  mul a b := match a with
    | none => b
    | some i => some i
  one := none
  mul_assoc a b c := by cases a <;> rfl
  one_mul _ := rfl
  mul_one a := by cases a <;> rfl

/-- `c_i x = c_i` for every `x`; in particular `c_i c_j = c_i` (main.tex l.1771). -/
@[simp] theorem c_mul (i : α) (x : Reset α) : c i * x = c i := rfl

/-- `c_i ≠ 1` (main.tex l.1770). -/
theorem c_ne_one (i : α) : c i ≠ 1 := fun h => Option.some_ne_none i h

/-- The constants are pairwise distinct (main.tex l.1770). -/
theorem c_injective : Function.Injective (c : α → Reset α) := fun _ _ h => Option.some.inj h

/-- Every element is `1` or a constant (main.tex l.1770). -/
theorem eq_one_or_c (x : Reset α) : x = 1 ∨ ∃ i, x = c i := by
  cases x with
  | none => exact Or.inl rfl
  | some i => exact Or.inr ⟨i, rfl⟩

/-- If a congruence identifies `1` with a constant then it is universal
(proof of Theorem `thm:reset-con`, main.tex l.1788). -/
theorem eq_top_of_one_rel (r : Con (Reset α)) {i : α} (h : r 1 (c i)) : r = ⊤ := by
  have hc : ∀ j, r (c j) (c i) := fun j => by
    have := r.mul h (r.refl (c j))
    simpa using this
  have hall : ∀ x, r x (c i) := fun x => by
    rcases eq_one_or_c x with rfl | ⟨j, rfl⟩
    · exact h
    · exact hc j
  exact top_unique fun x y _ => r.trans (hall x) (r.symm (hall y))

/-- **Theorem `thm:reset-con`, first half** (main.tex l.1773): every non-universal congruence has
`{1}` as a singleton class. -/
theorem one_class (r : Con (Reset α)) (hr : r ≠ ⊤) {x : Reset α} (h : r 1 x) : x = 1 := by
  rcases eq_one_or_c x with rfl | ⟨i, rfl⟩
  · rfl
  · exact absurd (eq_top_of_one_rel r h) hr

/-- The relation "`1` alone, constants related by `s`" (main.tex l.1783). -/
def rel (s : Setoid α) : Reset α → Reset α → Prop
  | none, none => True
  | some i, some j => s i j
  | _, _ => False

/-- **Theorem `thm:reset-con`, second half** (main.tex l.1783): any equivalence relation on the
constants, with `1` kept in a singleton class, is a congruence. -/
def ofSetoid (s : Setoid α) : Con (Reset α) where
  r := rel s
  iseqv :=
    { refl := fun x => by cases x with
        | none => trivial
        | some i => exact s.refl i
      symm := fun {x y} h => by
        cases x <;> cases y <;> first | trivial | exact s.symm h
      trans := fun {x y z} h h' => by
        cases x <;> cases y <;> cases z <;>
          first | trivial | exact s.trans h h' }
  mul' := fun {w x y z} h h' => by
    cases w <;> cases x <;> first | exact False.elim h | exact h' | exact h

/-- Unfolding `ofSetoid` on constants (main.tex l.1783). -/
@[simp] theorem ofSetoid_c (s : Setoid α) (i j : α) : ofSetoid s (c i) (c j) ↔ s i j := Iff.rfl

/-- In `ofSetoid s` the identity is not related to any constant (main.tex l.1783). -/
theorem not_ofSetoid_one_c (s : Setoid α) (i : α) : ¬ ofSetoid s 1 (c i) := fun h => h

/-- `ofSetoid s` is never universal when there is at least one constant (`n ≥ 1`,
main.tex l.1768). -/
theorem ofSetoid_ne_top (s : Setoid α) [Nonempty α] : ofSetoid s ≠ ⊤ := by
  intro h
  obtain ⟨i⟩ := ‹Nonempty α›
  have : (⊤ : Con (Reset α)) 1 (c i) := trivial
  rw [← h] at this
  exact not_ofSetoid_one_c s i this

/-- The restriction of a congruence to the constants (main.tex l.1774). -/
def restrict (r : Con (Reset α)) : Setoid α where
  r i j := r (c i) (c j)
  iseqv := ⟨fun _ => r.refl _, fun h => r.symm h, fun h h' => r.trans h h'⟩

/-- `restrict (ofSetoid s) = s` (main.tex l.1794). -/
theorem restrict_ofSetoid (s : Setoid α) : restrict (ofSetoid s) = s := by
  ext i j; rfl

/-- A non-universal congruence is `1` alone plus its restriction to the constants
(main.tex l.1794). -/
theorem ofSetoid_restrict (r : Con (Reset α)) (hr : r ≠ ⊤) : ofSetoid (restrict r) = r := by
  refine Con.ext fun x y => ?_
  rcases eq_one_or_c x with rfl | ⟨i, rfl⟩ <;> rcases eq_one_or_c y with rfl | ⟨j, rfl⟩
  · exact ⟨fun _ => r.refl _, fun _ => trivial⟩
  · exact ⟨fun h => False.elim h, fun h => absurd (one_class r hr h) (c_ne_one j)⟩
  · exact ⟨fun h => False.elim h, fun h => absurd (one_class r hr (r.symm h)) (c_ne_one i)⟩
  · exact Iff.rfl

open Classical in
/-- **Theorem `thm:reset-con`** (main.tex l.1766): `Con(R_n^1) ≅ Π_n ⊕ 𝟏`, the partition lattice
with one new top element adjoined.  Here `Π_n` is `Setoid α` (equivalence relations ordered by
refinement) and the adjoined top is `WithTop`.  Requires at least one constant (`n ≥ 1`), as in
the paper. -/
noncomputable def conEquiv [Nonempty α] : Con (Reset α) ≃o WithTop (Setoid α) :=
  Equiv.toOrderIso
    { toFun := fun r => if r = ⊤ then ⊤ else ((restrict r : Setoid α) : WithTop (Setoid α))
      invFun := fun t => WithTop.recTopCoe (C := fun _ => Con (Reset α)) ⊤ ofSetoid t
      left_inv := fun r => by
        by_cases hr : r = ⊤
        · simp [hr]
        · simp [hr, ofSetoid_restrict r hr]
      right_inv := fun t => by
        cases t with
        | top => simp
        | coe s => simp [ofSetoid_ne_top, restrict_ofSetoid] }
    (by
      intro r r' hrr'
      by_cases hr' : r' = ⊤
      · simp [hr']
      · have hr : r ≠ ⊤ := fun h => hr' (top_unique (h ▸ hrr'))
        simp only [Equiv.coe_fn_mk, if_neg hr, if_neg hr', WithTop.coe_le_coe]
        intro i j h
        exact hrr' h)
    (by
      intro t t' htt'
      cases t' with
      | top => exact le_top
      | coe s' =>
        cases t with
        | top => exact absurd htt' (by simp)
        | coe s =>
          have hss' : s ≤ s' := WithTop.coe_le_coe.1 htt'
          show ofSetoid s ≤ ofSetoid s'
          intro x y h
          rcases eq_one_or_c x with rfl | ⟨i, rfl⟩ <;> rcases eq_one_or_c y with rfl | ⟨j, rfl⟩
          · trivial
          · exact False.elim h
          · exact False.elim h
          · exact hss' h)

/-- `conEquiv` sends the universal congruence to the adjoined top (main.tex l.1779). -/
theorem conEquiv_top [Nonempty α] : conEquiv (⊤ : Con (Reset α)) = ⊤ := by
  simp [conEquiv]

/-- `conEquiv.symm` on a partition is `ofSetoid` (main.tex l.1779). -/
theorem conEquiv_symm_coe [Nonempty α] (s : Setoid α) :
    (conEquiv (α := α)).symm (s : WithTop (Setoid α)) = ofSetoid s := rfl

section Partition

/-- The equivalence relation merging the points of a set `s` and nothing else. -/
def mergeSet (s : Set α) : Setoid α where
  r u v := u = v ∨ (u ∈ s ∧ v ∈ s)
  iseqv :=
    { refl := fun _ => Or.inl rfl
      symm := fun h => Or.elim h (fun e => Or.inl e.symm) (fun e => Or.inr ⟨e.2, e.1⟩)
      trans := fun h h' => by
        rcases h with rfl | ⟨h1, h2⟩
        · exact h'
        · rcases h' with rfl | ⟨h3, h4⟩
          · exact Or.inr ⟨h1, h2⟩
          · exact Or.inr ⟨h1, h4⟩ }

/-- `mergeSet s ≤ d` iff `d` relates any two points of `s`. -/
theorem mergeSet_le_iff {s : Set α} {d : Setoid α} :
    mergeSet s ≤ d ↔ ∀ u ∈ s, ∀ v ∈ s, d u v := by
  constructor
  · intro h u hu v hv
    exact h (Or.inr ⟨hu, hv⟩)
  · intro h u v huv
    rcases huv with rfl | ⟨hu, hv⟩
    · exact d.refl _
    · exact h u hu v hv

/-- Meets of `mergeSet`s. -/
theorem mergeSet_inf (s t : Set α) : mergeSet s ⊓ mergeSet t = mergeSet (s ∩ t) := by
  ext u v
  rw [Setoid.inf_iff_and]
  constructor
  · rintro ⟨h1 | ⟨h1, h2⟩, h3 | ⟨h3, h4⟩⟩
    · exact Or.inl h1
    · exact Or.inl h1
    · exact Or.inl h3
    · exact Or.inr ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩
  · rintro (h | ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩)
    · exact ⟨Or.inl h, Or.inl h⟩
    · exact ⟨Or.inr ⟨h1, h2⟩, Or.inr ⟨h3, h4⟩⟩

/-- Merging a subsingleton merges nothing. -/
theorem mergeSet_eq_bot {s : Set α} (hs : s.Subsingleton) : mergeSet s = ⊥ := by
  refine le_bot_iff.1 fun u v h => ?_
  rw [Setoid.bot_def]
  rcases h with h | ⟨hu, hv⟩
  · exact h
  · exact hs hu hv

/-- The join of two overlapping pair-merges is the triple-merge. -/
theorem mergeSet_pair_sup (x y z : α) :
    mergeSet {x, y} ⊔ mergeSet {y, z} = mergeSet ({x, y, z} : Set α) := by
  apply le_antisymm
  · refine sup_le (mergeSet_le_iff.2 ?_) (mergeSet_le_iff.2 ?_)
    · intro u hu v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
      refine Or.inr ⟨?_, ?_⟩ <;> simp only [Set.mem_insert_iff, Set.mem_singleton_iff] <;> tauto
    · intro u hu v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
      refine Or.inr ⟨?_, ?_⟩ <;> simp only [Set.mem_insert_iff, Set.mem_singleton_iff] <;> tauto
  · set d := mergeSet {x, y} ⊔ mergeSet {y, z} with hd
    have hxy : d x y :=
      (le_sup_left : mergeSet {x, y} ≤ d) (Or.inr ⟨by simp, by simp⟩)
    have hyz : d y z :=
      (le_sup_right : mergeSet {y, z} ≤ d) (Or.inr ⟨by simp, by simp⟩)
    have hxz : d x z := Setoid.trans' d hxy hyz
    refine mergeSet_le_iff.2 ?_
    intro u hu v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with hu | hu | hu <;> rcases hv with hv | hv | hv <;> subst hu <;> subst hv
    · exact Setoid.refl' d _
    · exact hxy
    · exact hxz
    · exact Setoid.symm' d hxy
    · exact Setoid.refl' d _
    · exact hyz
    · exact Setoid.symm' d hxz
    · exact Setoid.symm' d hyz
    · exact Setoid.refl' d _

/-- **`Π_3`-type `M₃` in a partition lattice** (Corollary, main.tex l.1798): for three distinct
points `x, y, z`, the three pair-merges form an `M₃` between `⊥` and the triple-merge. -/
theorem isM3_mergeSet {x y z : α} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    IsM3 (⊥ : Setoid α) (mergeSet {x, y}) (mergeSet {y, z}) (mergeSet {x, z})
      (mergeSet {x, y, z}) where
  ab := fun h => hxz (by
    have h1 : mergeSet {y, z} x y := h ▸ (Or.inr ⟨by simp, by simp⟩ : mergeSet {x, y} x y)
    rcases h1 with h1 | ⟨h1, _⟩
    · exact absurd h1 hxy
    · rcases h1 with h1 | h1
      · exact absurd h1 hxy
      · exact h1)
  bc := fun h => hxy (by
    have h1 : mergeSet {x, z} y z := h ▸ (Or.inr ⟨by simp, by simp⟩ : mergeSet {y, z} y z)
    rcases h1 with h1 | ⟨h1, _⟩
    · exact absurd h1 hyz
    · rcases h1 with h1 | h1
      · exact h1.symm
      · exact absurd h1 hyz)
  ac := fun h => hyz (by
    have h1 : mergeSet {x, z} x y := h ▸ (Or.inr ⟨by simp, by simp⟩ : mergeSet {x, y} x y)
    rcases h1 with h1 | ⟨_, h1⟩
    · exact absurd h1 hxy
    · rcases h1 with h1 | h1
      · exact absurd h1.symm hxy
      · exact h1)
  inf_ab := by
    rw [mergeSet_inf]
    refine mergeSet_eq_bot fun u hu v hv => ?_
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    have hu' : u = y := by
      rcases hu with ⟨hu1 | hu1, hu2 | hu2⟩
      · exact hu2
      · exact absurd (hu1.symm.trans hu2) hxz
      · exact hu1
      · exact hu1
    have hv' : v = y := by
      rcases hv with ⟨hv1 | hv1, hv2 | hv2⟩
      · exact hv2
      · exact absurd (hv1.symm.trans hv2) hxz
      · exact hv1
      · exact hv1
    rw [hu', hv']
  inf_bc := by
    rw [mergeSet_inf]
    refine mergeSet_eq_bot fun u hu v hv => ?_
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    have hu' : u = z := by
      rcases hu with ⟨hu1 | hu1, hu2 | hu2⟩
      · exact absurd (hu1.symm.trans hu2) hxy.symm
      · exact hu2
      · exact absurd (hu1.symm.trans hu2) hxz.symm
      · exact hu1
    have hv' : v = z := by
      rcases hv with ⟨hv1 | hv1, hv2 | hv2⟩
      · exact absurd (hv1.symm.trans hv2) hxy.symm
      · exact hv2
      · exact absurd (hv1.symm.trans hv2) hxz.symm
      · exact hv1
    rw [hu', hv']
  inf_ac := by
    rw [mergeSet_inf]
    refine mergeSet_eq_bot fun u hu v hv => ?_
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    have hu' : u = x := by
      rcases hu with ⟨hu1 | hu1, hu2 | hu2⟩
      · exact hu1
      · exact hu1
      · exact hu2
      · exact absurd (hu1.symm.trans hu2) hyz
    have hv' : v = x := by
      rcases hv with ⟨hv1 | hv1, hv2 | hv2⟩
      · exact hv1
      · exact hv1
      · exact hv2
      · exact absurd (hv1.symm.trans hv2) hyz
    rw [hu', hv']
  sup_ab := mergeSet_pair_sup x y z
  sup_bc := by
    have h2 : ({x, z} : Set α) = {z, x} := Set.pair_comm x z
    have h3 : ({x, y, z} : Set α) = {y, z, x} := by
      ext u; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [h2, h3]
    exact mergeSet_pair_sup y z x
  sup_ac := by
    have h1 : ({x, y} : Set α) = {y, x} := Set.pair_comm x y
    have h3 : ({x, y, z} : Set α) = {y, x, z} := by
      ext u; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [h1, h3]
    exact mergeSet_pair_sup y x z

end Partition

/-- `ofSetoid` is injective. -/
theorem ofSetoid_injective : Function.Injective (ofSetoid : Setoid α → Con (Reset α)) := by
  intro s t h
  rw [← restrict_ofSetoid s, h, restrict_ofSetoid]

/-- `ofSetoid` preserves meets and joins (it is the inclusion of `Π_n` in `Π_n ⊕ 𝟏` composed with
the isomorphism of Theorem `thm:reset-con`, main.tex l.1777). -/
theorem ofSetoid_inf_sup [Nonempty α] (s t : Setoid α) :
    ofSetoid (s ⊓ t) = ofSetoid s ⊓ ofSetoid t ∧ ofSetoid (s ⊔ t) = ofSetoid s ⊔ ofSetoid t := by
  simp only [← conEquiv_symm_coe]
  refine ⟨?_, ?_⟩
  · rw [← map_inf, WithTop.coe_inf]
  · rw [← map_sup, WithTop.coe_sup]

/-- **`Con(R_n^1)` contains `M₃`** whenever there are three distinct constants
(Corollary, main.tex l.1798; Proposition `prop:markov-reset-general`, l.1821).  The `M₃` is the
image of the pair-merges of `Π_n`; its bottom is the equality relation and its top merges the
three chosen constants. -/
theorem exists_isM3 {x y z : α} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    IsM3 (ofSetoid (⊥ : Setoid α)) (ofSetoid (mergeSet {x, y})) (ofSetoid (mergeSet {y, z}))
      (ofSetoid (mergeSet {x, z})) (ofSetoid (mergeSet {x, y, z})) := by
  haveI : Nonempty α := ⟨x⟩
  exact (isM3_mergeSet hxy hyz hxz).map ofSetoid ofSetoid_injective
    (fun s t => (ofSetoid_inf_sup s t).1) (fun s t => (ofSetoid_inf_sup s t).2)

/-- The bottom of the `M₃` is the equality congruence. -/
theorem ofSetoid_bot : ofSetoid (⊥ : Setoid α) = ⊥ := by
  refine le_bot_iff.1 fun x y h => ?_
  rcases eq_one_or_c x with rfl | ⟨i, rfl⟩ <;> rcases eq_one_or_c y with rfl | ⟨j, rfl⟩
  · rfl
  · exact False.elim h
  · exact False.elim h
  · have : i = j := by
      have h' : (⊥ : Setoid α) i j := h
      rwa [Setoid.bot_def] at h'
    rw [this]
    exact Con.refl _ _

/-- **`Con(R_n^1)` is non-distributive for `n ≥ 3`** (Proposition `prop:markov-reset-general`,
main.tex l.1821; Corollary, l.1804). -/
theorem nonDistrib {x y z : α} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    NonDistrib (Con (Reset α)) :=
  (exists_isM3 hxy hyz hxz).nonDistrib

/-- **Corollary (main.tex l.1798)** for `n = 3`: the `M₃` in `Con(R_3^1)` consists of the equality
relation, the three congruences merging two reset maps, and the congruence `θ` that merges all
three reset maps while leaving the identity separate (`ofSetoid ⊤`). -/
theorem isM3_fin3 :
    IsM3 (⊥ : Con (Reset (Fin 3))) (ofSetoid (mergeSet {0, 1})) (ofSetoid (mergeSet {1, 2}))
      (ofSetoid (mergeSet {0, 2})) (ofSetoid ⊤) := by
  have h := exists_isM3 (α := Fin 3) (x := 0) (y := 1) (z := 2) (by decide) (by decide)
    (by decide)
  have htop : mergeSet ({0, 1, 2} : Set (Fin 3)) = ⊤ := by
    refine top_unique fun u v _ => Or.inr ⟨?_, ?_⟩
    · fin_cases u <;> simp
    · fin_cases v <;> simp
  rwa [ofSetoid_bot, htop] at h

end Reset

end Dovetail.Predictor

#print axioms Dovetail.Predictor.Reset.conEquiv
#print axioms Dovetail.Predictor.Reset.one_class
#print axioms Dovetail.Predictor.Reset.exists_isM3
#print axioms Dovetail.Predictor.Reset.nonDistrib
#print axioms Dovetail.Predictor.Reset.isM3_fin3
