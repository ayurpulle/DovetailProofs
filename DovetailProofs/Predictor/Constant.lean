import Mathlib

/-!
# A transitive aperiodic transformation monoid contains a constant map

The fact used in Section `sec:experiment` of `Lattice/main.tex` to explain why the latched
process must have a transient part: a finite aperiodic transformation monoid in which every point
can be moved to every other has a constant map, that is, a synchronising word.  So an aperiodic
process with no synchronising word cannot be strongly connected.

The paper argues through `eMe = {e}` for an idempotent `e` of minimum rank.  The proof here uses
the same minimum-rank element but avoids idempotents: any `s ∈ M` that maps the image `Y` of a
minimum-rank element into itself permutes `Y`, and an aperiodic permutation is the identity.
-/

namespace Dovetail.Predictor

open Function

/-- If `e` has minimum rank in a finite aperiodic transformation monoid `M`, every `s ∈ M` that
maps the image of `e` into itself fixes it pointwise. -/
theorem fixes_range_of_minimal_rank {X : Type*} [Finite X] (M : Submonoid (Function.End X))
    (hap : ∀ s ∈ M, ∃ n : ℕ, s ^ n = s ^ (n + 1))
    {e : Function.End X} (heM : e ∈ M)
    (hmin : ∀ s ∈ M, (Set.range e).ncard ≤ (Set.range s).ncard)
    {s : Function.End X} (hs : s ∈ M) (hmaps : Set.MapsTo s (Set.range e) (Set.range e))
    {z : X} (hz : z ∈ Set.range e) : s z = z := by
  have hYfin : (Set.range e).Finite := Set.toFinite _
  obtain ⟨n, hn⟩ := hap s hs
  have hpow : ∀ k, Set.MapsTo (s ^ k) (Set.range e) (Set.range e) := by
    intro k
    induction k with
    | zero =>
      intro w hw
      have h0 : (s ^ 0) w = w := congrFun (pow_zero s) w
      exact h0.symm ▸ hw
    | succ k ih =>
      intro w hw
      have h1 : (s ^ (k + 1)) w = (s ^ k) (s w) := congrFun (pow_succ s k) w
      exact h1.symm ▸ ih (hmaps hw)
  have himg : (s ^ n) '' Set.range e = Set.range e := by
    apply Set.eq_of_subset_of_ncard_le (hpow n).image_subset _ hYfin
    have h : (s ^ n) '' Set.range e = Set.range (s ^ n * e) := (Set.range_comp _ _).symm
    exact (hmin _ (M.mul_mem (M.pow_mem hs n) heM)).trans_eq (congrArg Set.ncard h.symm)
  have hinj : Set.InjOn (s ^ n) (Set.range e) :=
    (Set.ncard_image_iff hYfin).mp (by rw [himg])
  apply hinj (hmaps hz) hz
  have h : (s ^ n) z = (s ^ n) (s z) := (congrFun hn z).trans (congrFun (pow_succ s n) z)
  exact h.symm

/-- **A transitive aperiodic transformation monoid on a finite set contains a constant map**
(main.tex, Section `sec:experiment`, paragraph on the latched process). -/
theorem exists_const_of_aperiodic_of_transitive {X : Type*} [Finite X] [Nonempty X]
    (M : Submonoid (Function.End X))
    (hap : ∀ s ∈ M, ∃ n : ℕ, s ^ n = s ^ (n + 1))
    (htr : ∀ x y : X, ∃ m ∈ M, m x = y) :
    ∃ c ∈ M, ∃ x₀ : X, ∀ x, c x = x₀ := by
  obtain ⟨e, heM, hmin'⟩ :=
    WellFounded.has_min (measure fun s : Function.End X => (Set.range s).ncard).wf
      (M : Set (Function.End X)) ⟨1, M.one_mem⟩
  have hmin : ∀ s ∈ M, (Set.range e).ncard ≤ (Set.range s).ncard :=
    fun s hs => not_lt.mp (hmin' s hs)
  have he : ∀ z ∈ Set.range e, e z = z := fun z hz =>
    fixes_range_of_minimal_rank M hap heM hmin heM (fun _ _ => Set.mem_range_self _) hz
  obtain ⟨x₁⟩ := ‹Nonempty X›
  refine ⟨e, heM, e x₁, fun x => ?_⟩
  obtain ⟨m, hm, hmx⟩ := htr (e x) (e x₁)
  have h : e (m (e x)) = e x :=
    fixes_range_of_minimal_rank M hap heM hmin (M.mul_mem heM hm)
      (fun _ _ => Set.mem_range_self _) (Set.mem_range_self x)
  rw [hmx, he _ (Set.mem_range_self _)] at h
  exact h.symm

/-- Contrapositive, in the form the paper uses: an aperiodic transformation monoid with no
constant map is not transitive. -/
theorem not_transitive_of_aperiodic_of_no_const {X : Type*} [Finite X] [Nonempty X]
    (M : Submonoid (Function.End X))
    (hap : ∀ s ∈ M, ∃ n : ℕ, s ^ n = s ^ (n + 1))
    (hnc : ∀ c ∈ M, ∀ x₀ : X, ∃ x, c x ≠ x₀) :
    ∃ x y : X, ∀ m ∈ M, m x ≠ y := by
  by_contra hcon
  push Not at hcon
  obtain ⟨c, hc, x₀, hx₀⟩ := exists_const_of_aperiodic_of_transitive M hap hcon
  obtain ⟨x, hx⟩ := hnc c hc x₀
  exact hx (hx₀ x)

end Dovetail.Predictor
