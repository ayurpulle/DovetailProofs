import Mathlib
import DovetailProofs.Descent

/-!
# Stochastic languages, predictive states and the canonical monoid `S_p`

Formalises Section 2 of `Lattice/main.tex` ("What Every Exact Predictor Must Compute"):
stochastic languages (Definition, l.211), conditional futures `q_u` (l.236), the canonical
predictive states `X_p` and `X̂_p = X_p ∪ {†}` (Definition, l.249), the updates `τ_o` (l.265),
their well-definedness (Lemma, l.276), and the monoid `S_p` (Definition, l.296).

## Conventions

* Words are `List O`; the paper's `uo` is `u ++ [o]` and `uv` is `u ++ v`.
* `run step w` is the paper's `δ_w = δ_{o_n} ∘ ⋯ ∘ δ_{o_1}` for `w = o₁ ⋯ oₙ` (first letter acts
  first).  The existing `Dovetail.transitionMonoid` is the range of `FreeMonoid.lift`, which sends
  `o₁ ⋯ oₙ` to `T o₁ ∘ ⋯ ∘ T oₙ` (the opposite word order).  As a *set of maps with composition*
  the two agree: `run step w = FreeMonoid.lift step (ofList w.reverse)` (`run_eq_lift`), so
  `transitionMonoid step` is literally the paper's `⟨δ_o⟩ ⊆ 𝒯_Q` with ordinary composition
  (`mem_transitionMonoid_iff`).
* `X̂_p` is `Option P.X`, with `none` playing the role of `†`.
* `τ_o` is defined intrinsically on a future law `f` by the one-symbol shift
  `v ↦ f (o v) / f (o)`, so no choice of representative history is made; `tau_nu` shows it is
  the paper's map `q_u ↦ q_{uo}` (or `†`), and `q_congr` is the paper's well-definedness lemma.
-/

namespace Dovetail.Predictor

open Function

section Run

variable {O Q : Type*}

/-- The paper's `δ_w = δ_{o_n} ∘ ⋯ ∘ δ_{o_1}` for `w = o₁ ⋯ oₙ` (main.tex l.305, l.392):
the first letter of the word acts first. -/
def run (step : O → Q → Q) (w : List O) (x : Q) : Q :=
  w.foldl (fun x o => step o x) x

@[simp] theorem run_nil (step : O → Q → Q) (x : Q) : run step [] x = x := rfl

@[simp] theorem run_cons (step : O → Q → Q) (o : O) (w : List O) (x : Q) :
    run step (o :: w) x = run step w (step o x) := rfl

/-- `δ_{uv} = δ_v ∘ δ_u` (main.tex l.350). -/
@[simp] theorem run_append (step : O → Q → Q) (u v : List O) (x : Q) :
    run step (u ++ v) x = run step v (run step u x) := by
  simp [run, List.foldl_append]

theorem run_snoc (step : O → Q → Q) (u : List O) (o : O) (x : Q) :
    run step (u ++ [o]) x = step o (run step u x) := by simp

/-- `δ_ε = id` (main.tex l.395). -/
theorem run_nil_eq (step : O → Q → Q) : run step [] = (1 : Function.End Q) := rfl

/-- `δ_w ∘ δ_v = δ_{vw}` (main.tex l.350). -/
theorem run_append_eq (step : O → Q → Q) (u v : List O) :
    run step (u ++ v) = run step v ∘ run step u := by
  funext x; simp

/-- Translation between the paper's word convention and that of `Dovetail.transitionMonoid`:
`run step w` is `FreeMonoid.lift step` at the reversed word (main.tex l.336). -/
theorem run_eq_lift (step : O → Q → Q) (w : List O) :
    run step w = FreeMonoid.lift (M := Function.End Q) step (FreeMonoid.ofList w.reverse) := by
  induction w with
  | nil => rfl
  | cons o w ih =>
    funext x
    rw [List.reverse_cons, FreeMonoid.ofList_append, map_mul, FreeMonoid.ofList_singleton,
      FreeMonoid.lift_eval_of, Function.End.mul_def, Function.comp_apply, ← ih]
    rfl

/-- The converse translation of `run_eq_lift` (main.tex l.336). -/
theorem lift_eq_run (step : O → Q → Q) (w : FreeMonoid O) :
    FreeMonoid.lift (M := Function.End Q) step w = run step (FreeMonoid.toList w).reverse := by
  rw [run_eq_lift, List.reverse_reverse]; rfl

/-- The transition monoid `⟨δ_o : o ∈ O⟩ ⊆ 𝒯_Q` (main.tex l.296, l.334, l.458) is exactly the set
of maps `δ_w`. -/
theorem mem_transitionMonoid_iff (step : O → Q → Q) (s : Function.End Q) :
    s ∈ transitionMonoid (V := Q) step ↔ ∃ w : List O, run step w = s := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨_, (lift_eq_run step w).symm⟩
  · rintro ⟨w, rfl⟩
    exact ⟨FreeMonoid.ofList w.reverse, (run_eq_lift step w).symm⟩

/-- Each `δ_w` lies in the transition monoid (main.tex l.334). -/
theorem run_mem_transitionMonoid (step : O → Q → Q) (w : List O) :
    (run step w : Function.End Q) ∈ transitionMonoid (V := Q) step :=
  (mem_transitionMonoid_iff step _).2 ⟨w, rfl⟩

end Run

/-- **Stochastic language** (Definition, main.tex l.211): `p : O* → [0,1]` with `p(ε) = 1` and
`p(u) = ∑_o p(uo)`.  The bound `p ≤ 1` is derived (`StochLang.p_le_one`), not assumed. -/
structure StochLang (O : Type*) [Fintype O] where
  /-- `p u` is the probability that the process begins with the word `u`. -/
  p : List O → ℝ
  /-- Probabilities are nonnegative. -/
  nonneg : ∀ u, 0 ≤ p u
  /-- `p(ε) = 1`. -/
  nil : p [] = 1
  /-- Consistency: `p(u) = ∑_o p(uo)`. -/
  consistent : ∀ u, p u = ∑ o, p (u ++ [o])

namespace StochLang

variable {O : Type*} [Fintype O] (P : StochLang O)

/-- `p(uo) ≤ p(u)` (main.tex l.314). -/
theorem p_snoc_le (u : List O) (o : O) : P.p (u ++ [o]) ≤ P.p u := by
  rw [P.consistent u]
  exact Finset.single_le_sum (f := fun o => P.p (u ++ [o])) (fun o _ => P.nonneg _)
    (Finset.mem_univ o)

/-- Consistency gives `p(u) ≥ p(uv)` (main.tex l.314). -/
theorem p_append_le (u v : List O) : P.p (u ++ v) ≤ P.p u := by
  induction v using List.reverseRecOn with
  | nil => simp
  | append_singleton v o ih =>
    rw [← List.append_assoc]
    exact (P.p_snoc_le _ _).trans ih

/-- `p` takes values in `[0,1]` (main.tex l.214). -/
theorem p_le_one (u : List O) : P.p u ≤ 1 := by
  simpa [P.nil] using P.p_append_le [] u

/-- If `p(u) = 0` then `p(uv) = 0` for every `v` (main.tex l.244). -/
theorem p_append_eq_zero {u : List O} (h : P.p u = 0) (v : List O) : P.p (u ++ v) = 0 :=
  le_antisymm (h ▸ P.p_append_le u v) (P.nonneg _)

/-- `L_p` is closed under prefixes (main.tex l.315). -/
theorem pos_of_append_pos {u v : List O} (h : 0 < P.p (u ++ v)) : 0 < P.p u :=
  lt_of_lt_of_le h (P.p_append_le u v)

/-- A word is impossible iff its probability is not positive (main.tex l.244). -/
theorem not_pos_iff {u : List O} : ¬ 0 < P.p u ↔ P.p u = 0 :=
  ⟨fun h => le_antisymm (not_lt.1 h) (P.nonneg u), fun h => h ▸ lt_irrefl _⟩

/-- The empty word is possible (main.tex l.218). -/
theorem nil_pos : 0 < P.p [] := by rw [P.nil]; exact one_pos

/-- Every possible word has a possible one-symbol extension (main.tex l.316). -/
theorem exists_snoc_pos {u : List O} (h : 0 < P.p u) : ∃ o, 0 < P.p (u ++ [o]) := by
  by_contra hne
  push Not at hne
  have : P.p u = 0 := by
    rw [P.consistent u]
    exact Finset.sum_eq_zero fun o _ => le_antisymm (hne o) (P.nonneg _)
  exact h.ne' this

/-- The conditional future `q_u(v) = p(uv) / p(u)` (main.tex l.236).  Only meaningful when
`p u > 0`. -/
noncomputable def q (u : List O) : List O → ℝ := fun v => P.p (u ++ v) / P.p u

/-- Unfolding of `q_u(v)` (main.tex l.238). -/
theorem q_apply (u v : List O) : P.q u v = P.p (u ++ v) / P.p u := rfl

/-- `q_u(ε) = 1` (main.tex l.241). -/
theorem q_nil {u : List O} (h : 0 < P.p u) : P.q u [] = 1 := by
  simp [q, h.ne']

/-- `q_ε = p` (main.tex l.238 with `u = ε`). -/
theorem q_nil_left : P.q [] = P.p := by
  funext v; simp [q, P.nil]

/-- `q_u(v) > 0` iff `p(uv) > 0` (main.tex l.559). -/
theorem q_pos_iff {u : List O} (h : 0 < P.p u) (v : List O) :
    0 < P.q u v ↔ 0 < P.p (u ++ v) := by
  rw [q_apply]
  refine ⟨fun h' => ?_, fun h' => div_pos h' h⟩
  by_contra hn
  rw [P.not_pos_iff] at hn
  simp [hn] at h'

/-- The one-symbol shift of a future law: `f ↦ (v ↦ f(ov) / f(o))`.  This is the intrinsic form
of the predictive update, cf. the displayed computation in the proof at main.tex l.290. -/
noncomputable def shift (o : O) (f : List O → ℝ) : List O → ℝ := fun v => f (o :: v) / f [o]

/-- `q_{uo}(v) = q_u(ov) / q_u(o)` (main.tex l.290). -/
theorem shift_q {u : List O} {o : O} (h : 0 < P.p (u ++ [o])) :
    shift o (P.q u) = P.q (u ++ [o]) := by
  have hu : 0 < P.p u := P.pos_of_append_pos h
  funext v
  simp only [shift, q_apply, List.append_assoc, List.singleton_append]
  field_simp

/-- **Well-definedness of `τ_o`** (Lemma, main.tex l.276): if `q_u = q_{u'}` then either both
`p(uo)` and `p(u'o)` vanish, or `q_{uo} = q_{u'o}`. -/
theorem q_congr {u u' : List O} (hu : 0 < P.p u) (hu' : 0 < P.p u') (h : P.q u = P.q u') (o : O) :
    (P.p (u ++ [o]) = 0 ∧ P.p (u' ++ [o]) = 0) ∨ P.q (u ++ [o]) = P.q (u' ++ [o]) := by
  have key : 0 < P.p (u ++ [o]) ↔ 0 < P.p (u' ++ [o]) := by
    rw [← P.q_pos_iff hu, ← P.q_pos_iff hu', h]
  by_cases h1 : 0 < P.p (u ++ [o])
  · right
    rw [← P.shift_q h1, ← P.shift_q (key.1 h1), h]
  · left
    exact ⟨P.not_pos_iff.1 h1, P.not_pos_iff.1 (fun h2 => h1 (key.2 h2))⟩

/-- **Canonical predictive states** `X_p = {q_u : p(u) > 0}` (Definition, main.tex l.249).
`X̂_p = X_p ∪ {†}` is `Option P.X`, with `none` for `†`. -/
def X : Type _ := {f : List O → ℝ // ∃ u, 0 < P.p u ∧ f = P.q u}

/-- The live state `q_u` for a possible history `u` (main.tex l.252). -/
noncomputable def qState (u : List O) (h : 0 < P.p u) : P.X := ⟨P.q u, u, h, rfl⟩

/-- Two predictive states are equal iff they are the same future law (main.tex l.242). -/
theorem X.ext {P : StochLang O} {x y : P.X} (h : x.1 = y.1) : x = y := Subtype.ext h

/-- Every live state is `q_u` for a possible `u` (main.tex l.252). -/
theorem exists_qState (x : P.X) : ∃ u h, x = P.qState u h := by
  obtain ⟨f, u, hu, rfl⟩ := x
  exact ⟨u, hu, rfl⟩

open Classical in
/-- **The predictive update** `τ_o : X̂_p → X̂_p` (main.tex l.265): `τ_o(q_u) = q_{uo}` if
`p(uo) > 0`, `†` otherwise, and `τ_o(†) = †`.  Defined intrinsically via `shift`; see
`tau_nu`, `tau_qState_of_pos`, `tau_qState_of_zero`. -/
noncomputable def tau (o : O) : Option P.X → Option P.X
  | none => none
  | some x =>
    if h : 0 < x.1 [o] then
      some ⟨shift o x.1, by
        obtain ⟨u, hu, hx⟩ := x.2
        rw [hx] at h ⊢
        have h' := (P.q_pos_iff hu _).1 h
        exact ⟨u ++ [o], h', P.shift_q h'⟩⟩
    else none

/-- `τ_o(†) = †` (main.tex l.273). -/
@[simp] theorem tau_none (o : O) : P.tau o none = none := rfl

open Classical in
/-- **State labelling** `ν : O* → X̂_p` (main.tex l.710): `ν(u) = q_u` if `p(u) > 0`, else `†`. -/
noncomputable def nu (u : List O) : Option P.X :=
  if h : 0 < P.p u then some (P.qState u h) else none

/-- `ν(u) = q_u` for possible `u` (main.tex l.716). -/
theorem nu_of_pos {u : List O} (h : 0 < P.p u) : P.nu u = some (P.qState u h) := dif_pos h

/-- `ν(u) = †` for impossible `u` (main.tex l.717). -/
theorem nu_of_not_pos {u : List O} (h : ¬ 0 < P.p u) : P.nu u = none := dif_neg h

/-- `ν(u) = †` iff `p(u) = 0` (main.tex l.717). -/
theorem nu_eq_none_iff {u : List O} : P.nu u = none ↔ P.p u = 0 := by
  unfold nu; split_ifs with h
  · simp [h.ne']
  · simp [P.not_pos_iff.1 h]

/-- `ν(u) = x` live iff `u` is possible with future law `x` (main.tex l.716). -/
theorem nu_eq_some_iff {u : List O} {x : P.X} : P.nu u = some x ↔ 0 < P.p u ∧ x.1 = P.q u := by
  unfold nu; split_ifs with h
  · simp only [Option.some.injEq, h, true_and]
    exact ⟨fun h' => h' ▸ rfl, fun h' => X.ext h'.symm⟩
  · simp [h]

/-- The defining property of `τ_o` (main.tex l.265): `τ_o(q_u) = q_{uo}` if `p(uo) > 0` and `†`
otherwise; in terms of the labelling, `τ_o(ν(u)) = ν(uo)` for every word `u`. -/
theorem tau_nu (o : O) (u : List O) : P.tau o (P.nu u) = P.nu (u ++ [o]) := by
  by_cases hu : 0 < P.p u
  · rw [P.nu_of_pos hu]
    by_cases huo : 0 < P.p (u ++ [o])
    · rw [P.nu_of_pos huo]
      have : 0 < (P.qState u hu).1 [o] := (P.q_pos_iff hu _).2 huo
      simp only [tau, this, dite_true, Option.some.injEq]
      exact X.ext (P.shift_q huo)
    · rw [P.nu_of_not_pos huo]
      have : ¬ 0 < (P.qState u hu).1 [o] := fun h => huo ((P.q_pos_iff hu _).1 h)
      simp only [tau, this, dite_false]
  · rw [P.nu_of_not_pos hu, P.nu_of_not_pos, tau_none]
    exact fun h => hu (P.pos_of_append_pos h)

/-- `τ_o(q_u) = q_{uo}` when `p(uo) > 0` (main.tex l.269). -/
theorem tau_qState_of_pos {o : O} {u : List O} (h : 0 < P.p (u ++ [o])) :
    P.tau o (some (P.qState u (P.pos_of_append_pos h))) = some (P.qState (u ++ [o]) h) := by
  rw [← P.nu_of_pos, P.tau_nu, P.nu_of_pos]

/-- `τ_o(q_u) = †` when `p(uo) = 0` (main.tex l.270). -/
theorem tau_qState_of_zero {o : O} {u : List O} (hu : 0 < P.p u) (h : P.p (u ++ [o]) = 0) :
    P.tau o (some (P.qState u hu)) = none := by
  rw [← P.nu_of_pos, P.tau_nu, P.nu_eq_none_iff, h]

/-- `τ_w(ν(u)) = ν(uw)`; in particular `τ_w(q_u) = q_{uw}` whenever `p(uw) > 0`
(main.tex l.307, l.747). -/
theorem run_tau_nu (w u : List O) : run P.tau w (P.nu u) = P.nu (u ++ w) := by
  induction w generalizing u with
  | nil => simp
  | cons o w ih => rw [run_cons, P.tau_nu, ih]; simp

/-- `ν(u) = τ_u(q_ε)` for every word `u` (main.tex l.720). -/
theorem nu_eq_run (u : List O) : P.nu u = run P.tau u (P.nu []) := by
  rw [P.run_tau_nu]; simp

/-- Every `τ_w` fixes `†` (main.tex l.745). -/
@[simp] theorem run_tau_none (w : List O) : run P.tau w none = none := by
  induction w with
  | nil => rfl
  | cons o w ih => rw [run_cons, tau_none, ih]

/-- Every live state is `ν(u)` for a possible word `u` (main.tex l.746). -/
theorem exists_nu_eq_some (x : P.X) : ∃ u, 0 < P.p u ∧ P.nu u = some x := by
  obtain ⟨u, hu, rfl⟩ := P.exists_qState x
  exact ⟨u, hu, P.nu_of_pos hu⟩

/-- **The canonical monoid** `S_p = ⟨τ_o : o ∈ O⟩ ⊆ 𝒯_{X̂_p}` (Definition, main.tex l.296),
as a submonoid of `Function.End (Option P.X)` under ordinary composition. -/
noncomputable def Sp : Submonoid (Function.End (Option P.X)) :=
  transitionMonoid (V := Option P.X) P.tau

/-- Elements of `S_p` are exactly the maps `τ_w` (main.tex l.305). -/
theorem mem_Sp_iff (s : Function.End (Option P.X)) : s ∈ P.Sp ↔ ∃ w, run P.tau w = s :=
  mem_transitionMonoid_iff _ _

/-- Every element of `S_p` fixes `†` (main.tex l.745). -/
theorem Sp_apply_none {s : Function.End (Option P.X)} (hs : s ∈ P.Sp) : s none = none := by
  obtain ⟨w, rfl⟩ := (P.mem_Sp_iff s).1 hs
  exact P.run_tau_none w

/-- The set of possible words `L_p = {w : p(w) > 0}` (main.tex l.310). -/
def Lp : Set (List O) := {w | 0 < P.p w}

end StochLang

end Dovetail.Predictor
