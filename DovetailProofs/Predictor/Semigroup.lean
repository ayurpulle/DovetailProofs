import Mathlib

/-!
# Subgroups of monoids, division, aperiodicity: what passes along a surjection

Pure semigroup theory behind Theorem `thm:transport` of `Lattice/main.tex` (l.806):

* `IsSubgroup G`: `G` is a subsemigroup that is a group (main.tex l.795);
* `exists_subgroup_image_eq`: a subgroup of a homomorphic image of a *finite* semigroup is the
  image of a subgroup (proof of Theorem `thm:transport`(i), l.824);
* `Divides`: division of monoids (main.tex l.360, l.799), with transitivity;
* `IsAperiodic`: `∀ s, ∃ n, s ^ n = s ^ (n+1)` (main.tex l.798), its transport along a surjection
  (proof of Theorem `thm:transport`(ii), l.832), and the fact that an aperiodic monoid has only
  trivial subgroups.
-/

namespace Dovetail.Predictor

open Function

/-- A **subgroup of a semigroup** `M` (main.tex l.795): a subset closed under multiplication that
is a group under it.  Its identity `e` is an idempotent of `M` and need not be the identity
of `M`. -/
def IsSubgroup {M : Type*} [Mul M] (G : Set M) : Prop :=
  (∀ a ∈ G, ∀ b ∈ G, a * b ∈ G) ∧
    ∃ e ∈ G, (∀ g ∈ G, e * g = g ∧ g * e = g) ∧ ∀ g ∈ G, ∃ h ∈ G, g * h = e ∧ h * g = e

/-- A subgroup is nonempty (main.tex l.795). -/
theorem IsSubgroup.nonempty {M : Type*} [Mul M] {G : Set M} (hG : IsSubgroup G) : G.Nonempty :=
  let ⟨_, e, he, _⟩ := hG; ⟨e, he⟩

/-- "A semigroup in which `aH = H = Ha` for every `a` is a group" (main.tex l.828). -/
theorem isSubgroup_of_translates {M : Type*} [Semigroup M] {H : Set M} (hne : H.Nonempty)
    (hmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H)
    (hr : ∀ a ∈ H, ∀ b ∈ H, ∃ c ∈ H, a * c = b)
    (hl : ∀ a ∈ H, ∀ b ∈ H, ∃ c ∈ H, c * a = b) : IsSubgroup H := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨e, he, hae⟩ := hr a ha a ha
  obtain ⟨e', he', he'a⟩ := hl a ha a ha
  have re : ∀ b ∈ H, b * e = b := by
    intro b hb
    obtain ⟨c, _, rfl⟩ := hl a ha b hb
    rw [mul_assoc, hae]
  have le' : ∀ b ∈ H, e' * b = b := by
    intro b hb
    obtain ⟨c, _, rfl⟩ := hr a ha b hb
    rw [← mul_assoc, he'a]
  have hee : e' = e := (re e' he').symm.trans (le' e he)
  subst hee
  refine ⟨hmul, e', he, fun g hg => ⟨le' g hg, re g hg⟩, fun g hg => ?_⟩
  obtain ⟨h, hh, hgh⟩ := hr g hg e' he
  obtain ⟨h', hh', hh'g⟩ := hl g hg e' he
  have : h' = h := by
    calc h' = h' * e' := (re h' hh').symm
      _ = h' * (g * h) := by rw [hgh]
      _ = (h' * g) * h := (mul_assoc _ _ _).symm
      _ = h := by rw [hh'g, le' h hh]
  exact ⟨h, hh, hgh, this ▸ hh'g⟩

/-- Left translation by an element of a subgroup `G` maps `G` onto `G`
(the step `Φ(a) G = G`, main.tex l.827). -/
theorem IsSubgroup.mul_left_image {N : Type*} [Semigroup N] {G : Set N} (hG : IsSubgroup G)
    {g : N} (hg : g ∈ G) : (fun x => g * x) '' G = G := by
  obtain ⟨hmul, e, he, hid, hinv⟩ := hG
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hmul g hg x hx
  · intro x hx
    obtain ⟨h, hh, hgh, _⟩ := hinv g hg
    exact ⟨h * x, hmul h hh x hx, by simp only [← mul_assoc, hgh, (hid x hx).1]⟩

/-- Right translation by an element of a subgroup `G` maps `G` onto `G` (main.tex l.828). -/
theorem IsSubgroup.mul_right_image {N : Type*} [Semigroup N] {G : Set N} (hG : IsSubgroup G)
    {g : N} (hg : g ∈ G) : (fun x => x * g) '' G = G := by
  obtain ⟨hmul, e, he, hid, hinv⟩ := hG
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hmul x hx g hg
  · intro x hx
    obtain ⟨h, hh, _, hhg⟩ := hinv g hg
    exact ⟨x * h, hmul x hx h hh, by simp only [mul_assoc, hhg, (hid x hx).2]⟩

/-- **Lifting subgroups along a homomorphism from a finite semigroup**
(the argument of Theorem `thm:transport`(i), main.tex l.824).  If `M` is a finite semigroup,
`φ : M → N` is multiplicative and `G ⊆ φ(M)` is a subgroup of `N`, then there is a subgroup
`H ⊆ M` with `φ(H) = G`. -/
theorem exists_subgroup_image_eq {M N : Type*} [Semigroup M] [Finite M] [Semigroup N]
    (φ : M →ₙ* N) {G : Set N} (hG : IsSubgroup G) (hsub : G ⊆ Set.range φ) :
    ∃ H : Set M, IsSubgroup H ∧ φ '' H = G := by
  classical
  -- the family of subsemigroups mapping onto `G`
  let C : Set M → Prop := fun H => (∀ a ∈ H, ∀ b ∈ H, a * b ∈ H) ∧ φ '' H = G
  have hC0 : C (φ ⁻¹' G) := by
    refine ⟨fun a ha b hb => ?_, Set.image_preimage_eq_of_subset hsub⟩
    simp only [Set.mem_preimage, map_mul] at ha hb ⊢
    exact hG.1 _ ha _ hb
  obtain ⟨H, hHC, hHmin⟩ : ∃ H, C H ∧ ∀ K, C K → K ⊆ H → H ⊆ K := by
    have hfin : {H : Set M | C H}.Finite := Set.toFinite _
    obtain ⟨H, hmin⟩ := hfin.exists_minimal ⟨_, hC0⟩
    exact ⟨H, hmin.1, fun K hK hKH => hmin.2 hK hKH⟩
  obtain ⟨hmul, himg⟩ := hHC
  have hφ : ∀ a ∈ H, φ a ∈ G := fun a ha => himg ▸ Set.mem_image_of_mem φ ha
  -- `aH = H`
  have hleft : ∀ a ∈ H, (fun x => a * x) '' H = H := by
    intro a ha
    have hsubset : (fun x => a * x) '' H ⊆ H := by
      rintro _ ⟨x, hx, rfl⟩; exact hmul a ha x hx
    refine Set.Subset.antisymm hsubset (hHmin _ ⟨?_, ?_⟩ hsubset)
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact ⟨x * (a * y), hmul x hx _ (hmul a ha y hy), by simp only [mul_assoc]⟩
    · rw [Set.image_image]
      have : (fun x => φ (a * x)) = (fun y => φ a * y) ∘ φ := by
        funext x; simp
      rw [this, Set.image_comp, himg, hG.mul_left_image (hφ a ha)]
  -- `Ha = H`
  have hright : ∀ a ∈ H, (fun x => x * a) '' H = H := by
    intro a ha
    have hsubset : (fun x => x * a) '' H ⊆ H := by
      rintro _ ⟨x, hx, rfl⟩; exact hmul x hx a ha
    refine Set.Subset.antisymm hsubset (hHmin _ ⟨?_, ?_⟩ hsubset)
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact ⟨(x * a) * y, hmul _ (hmul x hx a ha) y hy, by simp only [mul_assoc]⟩
    · rw [Set.image_image]
      have : (fun x => φ (x * a)) = (fun y => y * φ a) ∘ φ := by
        funext x; simp
      rw [this, Set.image_comp, himg, hG.mul_right_image (hφ a ha)]
  have hne : H.Nonempty := by
    obtain ⟨g, hg⟩ := hG.nonempty
    rw [← himg] at hg
    obtain ⟨x, hx, _⟩ := hg
    exact ⟨x, hx⟩
  refine ⟨H, isSubgroup_of_translates hne hmul (fun a ha b hb => ?_) (fun a ha b hb => ?_), himg⟩
  · have : b ∈ (fun x => a * x) '' H := (hleft a ha).symm ▸ hb
    obtain ⟨c, hc, h⟩ := this
    exact ⟨c, hc, h⟩
  · have : b ∈ (fun x => x * a) '' H := (hright a ha).symm ▸ hb
    obtain ⟨c, hc, h⟩ := this
    exact ⟨c, hc, h⟩

/-- **Division** of monoids (main.tex l.360, l.799): `T` divides `S` when `T` is a quotient of a
submonoid of `S`. -/
def Divides (T S : Type*) [Monoid T] [Monoid S] : Prop :=
  ∃ (S' : Submonoid S) (f : S' →* T), Surjective f

/-- A quotient is a divisor (main.tex l.470). -/
theorem Divides.of_surjective {T S : Type*} [Monoid T] [Monoid S] (f : S →* T)
    (hf : Surjective f) : Divides T S :=
  ⟨⊤, f.comp (Submonoid.subtype ⊤), fun t => by
    obtain ⟨s, rfl⟩ := hf t
    exact ⟨⟨s, Submonoid.mem_top s⟩, rfl⟩⟩

/-- Division is transitive (main.tex l.829). -/
theorem Divides.trans {U T S : Type*} [Monoid U] [Monoid T] [Monoid S]
    (h₁ : Divides U T) (h₂ : Divides T S) : Divides U S := by
  obtain ⟨T', g, hg⟩ := h₁
  obtain ⟨S', f, hf⟩ := h₂
  let K : Submonoid S' := T'.comap f
  let e : K ≃* K.map S'.subtype := K.equivMapOfInjective S'.subtype Subtype.val_injective
  refine ⟨K.map S'.subtype, g.comp ((f.submonoidComap T').comp e.symm.toMonoidHom), ?_⟩
  intro u
  obtain ⟨⟨t, ht⟩, rfl⟩ := hg u
  obtain ⟨s, rfl⟩ := hf t
  refine ⟨e ⟨s, ht⟩, ?_⟩
  show g ((f.submonoidComap T') (e.symm (e ⟨s, ht⟩))) = g ⟨f s, ht⟩
  rw [e.symm_apply_apply]
  rfl

/-- **Aperiodicity** in the equational form of main.tex l.798: for every `s` there is `n` with
`s ^ n = s ^ (n + 1)`.  (The paper defines aperiodicity of a finite monoid by "all subgroups are
trivial" and states this form as equivalent; `IsAperiodic.subgroup_trivial` is the implication
from this form to that one.  The converse for finite monoids is not formalised.) -/
def IsAperiodic (M : Type*) [Monoid M] : Prop := ∀ s : M, ∃ n : ℕ, s ^ n = s ^ (n + 1)

/-- Aperiodicity passes to quotients (proof of Theorem `thm:transport`(ii), main.tex l.832). -/
theorem IsAperiodic.of_surjective {M N : Type*} [Monoid M] [Monoid N] (φ : M →* N)
    (hφ : Surjective φ) (h : IsAperiodic M) : IsAperiodic N := by
  intro t
  obtain ⟨s, rfl⟩ := hφ t
  obtain ⟨n, hn⟩ := h s
  exact ⟨n, by rw [← map_pow, hn, map_pow]⟩

/-- In an aperiodic monoid every subgroup is trivial (main.tex l.797). -/
theorem IsAperiodic.subgroup_trivial {M : Type*} [Monoid M] (h : IsAperiodic M) {G : Set M}
    (hG : IsSubgroup G) : ∃ e, G = {e} := by
  obtain ⟨_, e, he, hid, hinv⟩ := hG
  refine ⟨e, Set.eq_singleton_iff_unique_mem.2 ⟨he, fun g hg => ?_⟩⟩
  obtain ⟨k, hk, _, hkg⟩ := hinv g hg
  have step : ∀ n : ℕ, k * g ^ (n + 2) = g ^ (n + 1) := by
    intro n
    rw [pow_succ' g (n + 1), ← mul_assoc, hkg, pow_succ' g n, ← mul_assoc, (hid g hg).1]
  have key : ∀ n : ℕ, g ^ n = g ^ (n + 1) → g = e := by
    intro n
    induction n with
    | zero =>
      intro h0
      have hg1 : g = 1 := by simpa using h0.symm
      have := (hid g hg).1
      rw [hg1, mul_one] at this
      rw [hg1, this]
    | succ n ih =>
      intro hn
      cases n with
      | zero =>
        have := congrArg (fun x => k * x) hn
        simp only [zero_add, pow_one] at this
        rw [hkg, pow_two, ← mul_assoc, hkg, (hid g hg).1] at this
        exact this.symm
      | succ n =>
        apply ih
        have h2 : k * g ^ (n + 2) = k * g ^ (n + 1 + 2) := congrArg (fun x => k * x) hn
        rw [step n, step (n + 1)] at h2
        exact h2
  obtain ⟨n, hn⟩ := h g
  exact key n hn

end Dovetail.Predictor
