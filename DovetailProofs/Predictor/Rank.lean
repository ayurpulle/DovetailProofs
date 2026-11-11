import DovetailProofs.Predictor.Agent
import DovetailProofs.Predictor.Semigroup

/-!
# How much must be remembered: live rank

Formalises Section 6 of `Lattice/main.tex`: the live rank (Definition, l.1086), its monotonicity
under composition (l.1095), Theorem `thm:rank-bound` (the inherited memory bound, l.1107) with its
interpretation, and Proposition `prop:group-rank` (l.1220).

The live rank is an extended natural number (`ℕ∞`, via `Set.encard`), as in the paper's
`{0, 1, 2, …} ∪ {∞}`.  No finiteness is assumed anywhere.
-/

namespace Dovetail.Predictor

open Function

section LiveRank

variable {Y : Type*}

/-- The live image `s(X̂) ∩ X` of a self-map of `X̂ = X ∪ {†}` (main.tex l.1090, l.1223). -/
def liveImage (s : Option Y → Option Y) : Set Y := {x | ∃ y, s y = some x}

/-- **Live rank** `rk(s) = |s(X̂_p) ∩ X_p| ∈ {0, 1, 2, …} ∪ {∞}` (Definition, main.tex l.1086). -/
noncomputable def rk (s : Option Y → Option Y) : ℕ∞ := (liveImage s).encard

/-- `rk(s ∘ t) ≤ rk(s)`: the image of the composite is contained in the image of `s`
(main.tex l.1096). -/
theorem rk_comp_le_left (s t : Option Y → Option Y) : rk (s ∘ t) ≤ rk s :=
  Set.encard_le_encard fun _ ⟨y, hy⟩ => ⟨t y, hy⟩

/-- `rk(s ∘ t) ≤ rk(t)` when `s(†) = †` (main.tex l.1097). -/
theorem rk_comp_le_right (s t : Option Y → Option Y) (hs : s none = none) :
    rk (s ∘ t) ≤ rk t := by
  classical
  have hsub : some '' liveImage (s ∘ t) ⊆ s '' (some '' liveImage t) := by
    rintro _ ⟨x, ⟨y, hy⟩, rfl⟩
    cases hty : t y with
    | none => rw [Function.comp_apply, hty, hs] at hy; exact absurd hy (Option.some_ne_none x).symm
    | some z =>
      refine ⟨some z, ⟨z, ⟨y, hty⟩, rfl⟩, ?_⟩
      rw [← hty]; exact hy
  calc rk (s ∘ t) = (some '' liveImage (s ∘ t)).encard :=
        ((Option.some_injective Y).injOn.encard_image).symm
    _ ≤ (s '' (some '' liveImage t)).encard := Set.encard_le_encard hsub
    _ ≤ (some '' liveImage t).encard := Set.encard_image_le _ _
    _ = rk t := (Option.some_injective Y).injOn.encard_image

end LiveRank

section RankBound

variable {O : Type*} [Fintype O] {P : StochLang O} {Q : Type*} (A : ExactAgent P Q)

/-- The live states in the image of `τ_w` are exactly the `q_{uw}` over histories `u` with
`p(uw) > 0` (main.tex l.1102). -/
theorem liveImage_run_tau (w : List O) :
    liveImage (run P.tau w) = {x | ∃ u, 0 < P.p (u ++ w) ∧ P.nu (u ++ w) = some x} := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    cases y with
    | none => rw [P.run_tau_none] at hy; exact absurd hy (Option.some_ne_none x).symm
    | some z =>
      obtain ⟨u, _, hu⟩ := P.exists_nu_eq_some z
      rw [← hu, P.run_tau_nu] at hy
      exact ⟨u, (P.nu_eq_some_iff.1 hy).1, hy⟩
  · rintro ⟨u, _, hu⟩
    exact ⟨P.nu u, by rw [P.run_tau_nu, hu]⟩

/-- **Theorem `thm:rank-bound` (inherited memory bound)** (main.tex l.1107): for a reachable
exact predictive agent and every word `w`,
`rk(τ_w) ≤ |δ_w(Q) ∩ Q⁺|`, where `Q⁺ = Q \ {d}`. -/
theorem rank_bound (w : List O) :
    rk (run P.tau w) ≤ (Set.range (run A.step w) ∩ {q | q ≠ A.dead}).encard := by
  have hsub : some '' liveImage (run P.tau w) ⊆
      A.L '' (Set.range (run A.step w) ∩ {q | q ≠ A.dead}) := by
    rintro _ ⟨x, ⟨y, hy⟩, rfl⟩
    obtain ⟨q, rfl⟩ := A.L_surjective y
    rw [← A.L_run] at hy
    refine ⟨run A.step w q, ⟨⟨q, rfl⟩, fun hd => ?_⟩, hy⟩
    rw [hd, A.L_dead] at hy
    exact Option.some_ne_none x hy.symm
  calc rk (run P.tau w) = (some '' liveImage (run P.tau w)).encard :=
        ((Option.some_injective P.X).injOn.encard_image).symm
    _ ≤ (A.L '' (Set.range (run A.step w) ∩ {q | q ≠ A.dead})).encard :=
        Set.encard_le_encard hsub
    _ ≤ (Set.range (run A.step w) ∩ {q | q ≠ A.dead}).encard := Set.encard_image_le _ _

/-- The interpretation of the right-hand side of Theorem `thm:rank-bound` (main.tex l.1115,
l.1126): `δ_w(Q) ∩ Q⁺` is the set of live agent states reachable by a (possible) history ending
in `w`. -/
theorem range_run_inter_live (w : List O) :
    Set.range (run A.step w) ∩ {q | q ≠ A.dead} =
      {q | ∃ u, 0 < P.p (u ++ w) ∧ run A.step (u ++ w) A.init = q} := by
  ext q
  constructor
  · rintro ⟨⟨q', rfl⟩, hq⟩
    have hq' : q' ≠ A.dead := fun h => hq (by rw [h, A.run_dead])
    obtain ⟨u, _, rfl⟩ := A.reachable q' hq'
    refine ⟨u, ?_, run_append A.step u w A.init⟩
    by_contra hp
    exact hq (by
      rw [← run_append]
      exact A.run_init_of_zero (P.not_pos_iff.1 hp))
  · rintro ⟨u, hu, rfl⟩
    exact ⟨⟨run A.step u A.init, (run_append A.step u w A.init).symm⟩, A.live _ hu⟩

end RankBound

section GroupRank

variable {Y : Type*}

/-- **Proposition `prop:group-rank`, first claim** (main.tex l.1220): if `G` is a subgroup of a
monoid of self-maps of `X̂` with identity `e`, every `g ∈ G` has the same image as `e`; in
particular the same live image `I = e(X̂) ∩ X`. -/
theorem liveImage_eq_of_subgroup {G : Set (Function.End (Option Y))} {e : Function.End (Option Y)}
    (hid : ∀ g ∈ G, e * g = g ∧ g * e = g)
    (hinv : ∀ g ∈ G, ∃ h ∈ G, g * h = e ∧ h * g = e) {g : Function.End (Option Y)} (hg : g ∈ G) :
    liveImage g = liveImage e := by
  obtain ⟨h, _, hgh, _⟩ := hinv g hg
  ext x
  constructor
  · rintro ⟨y, hy⟩
    -- `g = e ∘ g`
    refine ⟨g y, ?_⟩
    have := congrFun (hid g hg).1 y
    rw [Function.End.mul_def, Function.comp_apply] at this
    rw [this, hy]
  · rintro ⟨y, hy⟩
    -- `e = g ∘ g⁻¹`
    refine ⟨h y, ?_⟩
    have := congrFun hgh y
    rw [Function.End.mul_def, Function.comp_apply] at this
    rw [this, hy]

/-- **Proposition `prop:group-rank`, "in particular"** (main.tex l.1225): `rk(g) = rk(e)` for
every `g` in a subgroup `G` with identity `e`. -/
theorem rk_eq_of_subgroup {G : Set (Function.End (Option Y))} {e : Function.End (Option Y)}
    (hid : ∀ g ∈ G, e * g = g ∧ g * e = g)
    (hinv : ∀ g ∈ G, ∃ h ∈ G, g * h = e ∧ h * g = e) {g : Function.End (Option Y)} (hg : g ∈ G) :
    rk g = rk e := by
  unfold rk; rw [liveImage_eq_of_subgroup hid hinv hg]

/-- The idempotent `e` fixes its (live) image pointwise (proof of Proposition `prop:group-rank`,
main.tex l.1232). -/
theorem apply_of_mem_liveImage {G : Set (Function.End (Option Y))} {e : Function.End (Option Y)}
    (he : e ∈ G) (hid : ∀ g ∈ G, e * g = g ∧ g * e = g) {x : Y} (hx : x ∈ liveImage e) :
    e (some x) = some x := by
  obtain ⟨y, hy⟩ := hx
  have := congrFun (hid e he).1 y
  rw [Function.End.mul_def, Function.comp_apply, hy] at this
  exact this

/-- Each `g ∈ G` maps the live image `I` of `e` into itself (proof of Proposition
`prop:group-rank`, main.tex l.1232–1235; this is where `g(†) = †` is used). -/
theorem mapsTo_liveImage_of_subgroup {G : Set (Function.End (Option Y))}
    {e : Function.End (Option Y)} (he : e ∈ G) (hfix : ∀ g ∈ G, g none = none)
    (hid : ∀ g ∈ G, e * g = g ∧ g * e = g)
    (hinv : ∀ g ∈ G, ∃ h ∈ G, g * h = e ∧ h * g = e)
    {g : Function.End (Option Y)} (hg : g ∈ G) :
    Set.MapsTo g (some '' liveImage e) (some '' liveImage e) := by
  rintro _ ⟨x, hx, rfl⟩
  have hex : e (some x) = some x := apply_of_mem_liveImage he hid hx
  obtain ⟨k, hk, _, hkg⟩ := hinv g hg
  have h1 : k (g (some x)) = some x := by
    have := congrFun hkg (some x)
    rw [Function.End.mul_def, Function.comp_apply] at this
    rw [this, hex]
  cases hgx : g (some x) with
  | none =>
    rw [hgx, hfix k hk] at h1
    exact absurd h1 (Option.some_ne_none x).symm
  | some z =>
    have hz : z ∈ liveImage g := ⟨some x, hgx⟩
    rw [liveImage_eq_of_subgroup hid hinv hg] at hz
    exact ⟨z, hz, rfl⟩

/-- **Proposition `prop:group-rank`, the permutation action** (main.tex l.1224): every `g` in a
subgroup `G` (with identity `e`) of self-maps fixing `†` permutes the live image `I` of `e`
(here `I` is viewed inside `X̂` as `some '' I`). -/
theorem bijOn_liveImage_of_subgroup {G : Set (Function.End (Option Y))}
    {e : Function.End (Option Y)} (he : e ∈ G) (hfix : ∀ g ∈ G, g none = none)
    (hid : ∀ g ∈ G, e * g = g ∧ g * e = g)
    (hinv : ∀ g ∈ G, ∃ h ∈ G, g * h = e ∧ h * g = e)
    {g : Function.End (Option Y)} (hg : g ∈ G) :
    Set.BijOn g (some '' liveImage e) (some '' liveImage e) := by
  obtain ⟨k, hk, hgk, hkg⟩ := hinv g hg
  refine ⟨mapsTo_liveImage_of_subgroup he hfix hid hinv hg, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ hxx'
    have h1 := congrFun hkg (some x)
    have h2 := congrFun hkg (some x')
    rw [Function.End.mul_def, Function.comp_apply, apply_of_mem_liveImage he hid hx] at h1
    rw [Function.End.mul_def, Function.comp_apply, apply_of_mem_liveImage he hid hx'] at h2
    rw [← h1, ← h2, hxx']
  · rintro _ ⟨z, hz, rfl⟩
    refine ⟨k (some z), mapsTo_liveImage_of_subgroup he hfix hid hinv hk ⟨z, hz, rfl⟩, ?_⟩
    have h1 := congrFun hgk (some z)
    rw [Function.End.mul_def, Function.comp_apply, apply_of_mem_liveImage he hid hz] at h1
    exact h1

/-- An element of `G` is determined by its values on the live image of `e`, because `g = g ∘ e`
(proof of Proposition `prop:group-rank`, main.tex l.1236). -/
theorem eq_of_eqOn_liveImage {G : Set (Function.End (Option Y))}
    {e : Function.End (Option Y)} (hfix : ∀ g ∈ G, g none = none)
    (hid : ∀ g ∈ G, e * g = g ∧ g * e = g)
    {g g' : Function.End (Option Y)} (hg : g ∈ G) (hg' : g' ∈ G)
    (h : ∀ x ∈ liveImage e, g (some x) = g' (some x)) : g = g' := by
  funext y
  have h1 := congrFun (hid g hg).2 y
  have h2 := congrFun (hid g' hg').2 y
  rw [Function.End.mul_def, Function.comp_apply] at h1 h2
  rw [← h1, ← h2]
  cases hey : e y with
  | none => rw [hfix g hg, hfix g' hg']
  | some x => exact h x ⟨y, hey⟩

/-- **Proposition `prop:group-rank`** (main.tex l.1220): for a subgroup `G` (identity `e`) of a
monoid of self-maps of `X̂` fixing `†`, restriction to the live image `I` of `e` is an injective
homomorphism `G → Sym(I)`.

Encoding: `I` is taken inside `X̂` as the set `some '' I`, `ρ g` is the permutation `x ↦ g x` of
it, "homomorphism" is stated as `ρ k = ρ g * ρ h` whenever `k = g * h` in `G` (so no group
structure has to be put on the subtype `G`). -/
theorem exists_perm_rep_of_subgroup {G : Set (Function.End (Option Y))}
    {e : Function.End (Option Y)} (he : e ∈ G) (hfix : ∀ g ∈ G, g none = none)
    (hid : ∀ g ∈ G, e * g = g ∧ g * e = g)
    (hinv : ∀ g ∈ G, ∃ h ∈ G, g * h = e ∧ h * g = e) :
    ∃ ρ : G → Equiv.Perm ↥(some '' liveImage e),
      (∀ (g : G) (x : ↥(some '' liveImage e)), ((ρ g x : ↥(some '' liveImage e)) : Option Y) =
        (g : Function.End (Option Y)) (x : Option Y)) ∧
      Function.Injective ρ ∧
      ∀ g h k : G, (k : Function.End (Option Y)) = (g : Function.End (Option Y)) * h →
        ρ k = ρ g * ρ h := by
  let ρ : G → Equiv.Perm ↥(some '' liveImage e) := fun g =>
    Set.BijOn.equiv g.1 (bijOn_liveImage_of_subgroup he hfix hid hinv g.2)
  have hρ : ∀ (g : G) (x : ↥(some '' liveImage e)),
      ((ρ g x : ↥(some '' liveImage e)) : Option Y) = (g : Function.End (Option Y)) x := by
    intro g x; rfl
  refine ⟨ρ, hρ, ?_, ?_⟩
  · intro g g' hgg'
    apply Subtype.ext
    refine eq_of_eqOn_liveImage hfix hid g.2 g'.2 fun x hx => ?_
    have := congrArg (fun π : Equiv.Perm ↥(some '' liveImage e) =>
      ((π ⟨some x, x, hx, rfl⟩ : ↥(some '' liveImage e)) : Option Y)) hgg'
    simpa only [hρ] using this
  · intro g h k hk
    ext x
    rw [Equiv.Perm.mul_apply, hρ, hρ, hρ, hk]
    rfl

end GroupRank

end Dovetail.Predictor

#print axioms Dovetail.Predictor.rank_bound
#print axioms Dovetail.Predictor.range_run_inter_live
#print axioms Dovetail.Predictor.rk_eq_of_subgroup
#print axioms Dovetail.Predictor.exists_perm_rep_of_subgroup
