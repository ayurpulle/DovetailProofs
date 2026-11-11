import DovetailProofs.Predictor.Transport
import DovetailProofs.Predictor.Syntactic

/-!
# Finiteness cannot be dropped: the history-storing predictor

Formalises Example `ex:free-predictor` of `Lattice/main.tex` (l.854).

`coin` is the process on `O = Bool` emitting independent symbols, a fair coin at odd positions and
a coin with bias `1/3` at even positions.  Then:

* every word is possible (`coin_pos`);
* `S_p` is the two-element group (`coin_Sp_isSubgroup`, `coin_Sp_card`);
* `historyAgent`, which stores the whole history, is a reachable exact predictive agent whose
  update maps satisfy `δ_w = δ_{w'} → w = w'` (`historyAgent_run_injective`);
* its update monoid has no nontrivial subgroup (`historyAgent_subgroup_trivial`), so the
  conclusion of Theorem `thm:transport`(i) fails for it (`transport_fails_without_finiteness`);
* `τ(O^t)` is a single element for every `t` (`coin_run_eq_of_length_eq`, used at l.1016).
-/

namespace Dovetail.Predictor

open Function

namespace Coin

/-- One-symbol weight: at an odd position (`par = false`) a fair coin, at an even position
(`par = true`) the symbol `true` has probability `1/3` (main.tex l.856). -/
noncomputable def wt (par o : Bool) : ℝ :=
  if par then (if o then 1 / 3 else 2 / 3) else 1 / 2

/-- Probability of emitting the word `w` starting at a position of parity `par`. -/
noncomputable def pFrom : Bool → List Bool → ℝ
  | _, [] => 1
  | par, o :: w => wt par o * pFrom (!par) w

/-- The position parity after reading `w` from parity `par`. -/
def after : Bool → List Bool → Bool
  | par, [] => par
  | par, _ :: w => after (!par) w

/-- The weights are positive (main.tex l.858: every word is possible). -/
theorem wt_pos (par o : Bool) : 0 < wt par o := by
  cases par <;> cases o <;> norm_num [wt]

/-- The weights at each position sum to one (main.tex l.856). -/
theorem wt_sum (par : Bool) : wt par true + wt par false = 1 := by
  cases par <;> norm_num [wt]

/-- Every word has positive probability from either parity (main.tex l.858). -/
theorem pFrom_pos (par : Bool) (w : List Bool) : 0 < pFrom par w := by
  induction w generalizing par with
  | nil => exact one_pos
  | cons o w ih => exact mul_pos (wt_pos par o) (ih _)

/-- Parity after a concatenation (main.tex l.858). -/
theorem after_append (par : Bool) (u v : List Bool) :
    after par (u ++ v) = after (after par u) v := by
  induction u generalizing par with
  | nil => rfl
  | cons o u ih => exact ih _

/-- Flipping the starting parity flips the final parity (main.tex l.858). -/
theorem after_not (par : Bool) (w : List Bool) : after (!par) w = !(after par w) := by
  induction w generalizing par with
  | nil => rfl
  | cons o w ih => exact ih _

/-- Each symbol flips the parity (main.tex l.859). -/
theorem after_snoc (par : Bool) (u : List Bool) (o : Bool) :
    after par (u ++ [o]) = !(after par u) := by
  rw [after_append]; rfl

/-- Independence: the probability of `uv` factorises (main.tex l.856). -/
theorem pFrom_append (par : Bool) (u v : List Bool) :
    pFrom par (u ++ v) = pFrom par u * pFrom (after par u) v := by
  induction u generalizing par with
  | nil => simp [pFrom, after]
  | cons o u ih =>
    simp only [List.cons_append, pFrom, after, ih, mul_assoc]

/-- The parity after a word depends only on its length. -/
theorem after_eq_of_length_eq (par : Bool) {w w' : List Bool} (h : w.length = w'.length) :
    after par w = after par w' := by
  induction w generalizing par w' with
  | nil =>
    cases w' with
    | nil => rfl
    | cons _ _ => simp at h
  | cons o w ih =>
    cases w' with
    | nil => simp at h
    | cons o' w' => exact ih _ (by simpa using h)

end Coin

open Coin

/-- **The process of Example `ex:free-predictor`** (main.tex l.856): independent symbols, fair at
odd positions, bias `1/3` at even positions. -/
noncomputable def coin : StochLang Bool where
  p := pFrom false
  nonneg u := (pFrom_pos false u).le
  nil := rfl
  consistent u := by
    rw [Fintype.sum_bool]
    simp only [pFrom_append, pFrom, mul_one]
    rw [← mul_add, wt_sum, mul_one]

/-- Every word is possible (main.tex l.858). -/
theorem coin_pos (u : List Bool) : 0 < coin.p u := pFrom_pos false u

/-- The conditional future after `u` depends only on the parity of `|u|` (main.tex l.858). -/
theorem coin_q (u : List Bool) : coin.q u = pFrom (after false u) := by
  funext v
  have h : pFrom false u ≠ 0 := (pFrom_pos false u).ne'
  show pFrom false (u ++ v) / pFrom false u = _
  rw [pFrom_append, mul_div_cancel_left₀ _ h]

/-- The two parity laws are distinct: `1/2 ≠ 1/3` (main.tex l.858). -/
theorem pFrom_false_ne_true : pFrom false ≠ pFrom true := by
  intro h
  have := congrFun h [true]
  norm_num [pFrom, wt] at this

/-- There are two predictive states according to the parity of the history length
(main.tex l.858). -/
theorem coin_nu_eq_iff (u u' : List Bool) :
    coin.nu u = coin.nu u' ↔ after false u = after false u' := by
  rw [coin.nu_of_pos (coin_pos u), coin.nu_of_pos (coin_pos u'), Option.some.injEq]
  constructor
  · intro h
    have h' : coin.q u = coin.q u' := congrArg Subtype.val h
    rw [coin_q, coin_q] at h'
    revert h'
    cases after false u <;> cases after false u' <;> intro h'
    · rfl
    · exact absurd h' pFrom_false_ne_true
    · exact absurd h'.symm pFrom_false_ne_true
    · rfl
  · intro h
    apply StochLang.X.ext
    show coin.q u = coin.q u'
    rw [coin_q, coin_q, h]

/-- `τ_w = τ_{w'}` iff `|w|` and `|w'|` have the same parity (main.tex l.859). -/
theorem coin_run_eq_iff (w w' : List Bool) :
    run coin.tau w = run coin.tau w' ↔ after false w = after false w' := by
  rw [coin.tau_eq_iff_forall_nu]
  constructor
  · intro h
    simpa using (coin_nu_eq_iff _ _).1 (h [])
  · intro h u
    rw [coin_nu_eq_iff, after_append, after_append]
    cases after false u
    · exact h
    · exact (after_not false w).trans ((congrArg (!·) h).trans (after_not false w').symm)

/-- `τ(O^t)` is a single element for every `t` (main.tex l.1016). -/
theorem coin_run_eq_of_length_eq {w w' : List Bool} (h : w.length = w'.length) :
    run coin.tau w = run coin.tau w' :=
  (coin_run_eq_iff w w').2 (after_eq_of_length_eq false h)

/-- The swap `τ_0 = τ_1` as an element of `S_p` (main.tex l.859). -/
noncomputable def coinSwap : coin.Sp := ⟨run coin.tau [true], run_mem_transitionMonoid _ _⟩

/-- Both symbols act by the same map (main.tex l.859). -/
theorem coin_tau_false_eq_true : coin.tau false = coin.tau true := by
  have := coin_run_eq_of_length_eq (w := [false]) (w' := [true]) rfl
  funext y
  exact congrFun this y

/-- The swap is not the identity (main.tex l.859). -/
theorem coinSwap_ne_one : coinSwap ≠ 1 := by
  intro h
  have h' : run coin.tau [true] = run coin.tau [] := congrArg Subtype.val h
  rw [coin_run_eq_iff] at h'
  exact absurd h' (by decide)

/-- The swap is an involution (main.tex l.860). -/
theorem coinSwap_mul_self : coinSwap * coinSwap = 1 := by
  apply Subtype.ext
  show run coin.tau [true] ∘ run coin.tau [true] = run coin.tau []
  rw [← run_append_eq]
  exact (coin_run_eq_iff _ _).2 rfl

/-- Every element of `S_p` is the identity or the swap (main.tex l.860). -/
theorem coin_Sp_eq (s : coin.Sp) : s = 1 ∨ s = coinSwap := by
  obtain ⟨s, hs⟩ := s
  obtain ⟨w, rfl⟩ := (coin.mem_Sp_iff s).1 hs
  cases h : after false w
  · left
    apply Subtype.ext
    exact (coin_run_eq_iff w []).2 h
  · right
    apply Subtype.ext
    exact (coin_run_eq_iff w [true]).2 h

/-- **`S_p` is a group** (Example `ex:free-predictor`, main.tex l.860). -/
theorem coin_Sp_isSubgroup : IsSubgroup (Set.univ : Set coin.Sp) := by
  refine ⟨fun _ _ _ _ => Set.mem_univ _, 1, Set.mem_univ _, fun g _ => ⟨one_mul g, mul_one g⟩,
    fun g _ => ?_⟩
  rcases coin_Sp_eq g with rfl | rfl
  · exact ⟨1, Set.mem_univ _, one_mul 1, one_mul 1⟩
  · exact ⟨coinSwap, Set.mem_univ _, coinSwap_mul_self, coinSwap_mul_self⟩

/-- **`S_p` has exactly two elements** (Example `ex:free-predictor`, main.tex l.860). -/
theorem coin_Sp_card : Nat.card coin.Sp = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨1, coinSwap, fun h => coinSwap_ne_one h.symm, ?_⟩
  ext s
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  exact coin_Sp_eq s

/-- The update of the history-storing predictor, `δ_o(u) = uo`, `δ_o(d) = d` (main.tex l.861). -/
def histStep (o : Bool) : Option (List Bool) → Option (List Bool) := Option.map (· ++ [o])

/-- `δ_w(u) = uw` (main.tex l.861). -/
theorem histStep_run (w v : List Bool) : run histStep w (some v) = some (v ++ w) := by
  induction w generalizing v with
  | nil => simp
  | cons o w ih =>
    rw [run_cons]
    show run histStep w (some (v ++ [o])) = _
    rw [ih]; simp

/-- **The history-storing predictor** (Example `ex:free-predictor`, main.tex l.860):
`Q⁺ = O*`, `δ_o(u) = uo`, `F(u) = q_u`; the dead state is `none`. -/
noncomputable def historyAgent : ExactAgent coin (Option (List Bool)) where
  init := some []
  dead := none
  step := histStep
  readout y := match y with
    | some u => coin.q u
    | none => 0
  step_dead _ := rfl
  live u _ := by rw [histStep_run]; exact Option.some_ne_none _
  reachable y hy := by
    cases y with
    | none => exact absurd rfl hy
    | some u => exact ⟨u, coin_pos u, by rw [histStep_run]; simp⟩
  trim u o _ h := absurd h (coin_pos _).ne'
  exact u _ := by rw [histStep_run]; simp

/-- `δ_w(u) = uw` for the history-storing predictor (main.tex l.861). -/
theorem historyAgent_run (w v : List Bool) :
    run historyAgent.step w (some v) = some (v ++ w) := histStep_run w v

/-- **`δ_w = δ_{w'}` only when `w = w'`** (main.tex l.862): the update monoid is free. -/
theorem historyAgent_run_injective {w w' : List Bool}
    (h : run historyAgent.step w = run historyAgent.step w') : w = w' := by
  have := congrFun h (some [])
  rw [historyAgent_run, historyAgent_run] at this
  simpa using this

/-- **The free monoid has no nontrivial subgroup** (main.tex l.865): every subgroup of the update
monoid of the history-storing predictor is `{1}`. -/
theorem historyAgent_subgroup_trivial {H : Set historyAgent.SA} (hH : IsSubgroup H) :
    H = {1} := by
  obtain ⟨_, e, he, hid, hinv⟩ := hH
  -- every element is `δ_w`; products concatenate words
  have hrep : ∀ s : historyAgent.SA, ∃ w, s = ⟨run historyAgent.step w,
      run_mem_transitionMonoid _ _⟩ := by
    rintro ⟨s, hs⟩
    obtain ⟨w, rfl⟩ := (mem_transitionMonoid_iff historyAgent.step s).1 hs
    exact ⟨w, rfl⟩
  have hmul : ∀ w w' : List Bool,
      (⟨run historyAgent.step w, run_mem_transitionMonoid _ _⟩ : historyAgent.SA) *
        ⟨run historyAgent.step w', run_mem_transitionMonoid _ _⟩ =
        ⟨run historyAgent.step (w' ++ w), run_mem_transitionMonoid _ _⟩ := by
    intro w w'
    apply Subtype.ext
    exact (run_append_eq historyAgent.step w' w).symm
  have hone : (1 : historyAgent.SA) = ⟨run historyAgent.step [], run_mem_transitionMonoid _ _⟩ :=
    rfl
  have hinj : ∀ w w' : List Bool,
      (⟨run historyAgent.step w, run_mem_transitionMonoid _ _⟩ : historyAgent.SA) =
        ⟨run historyAgent.step w', run_mem_transitionMonoid _ _⟩ → w = w' :=
    fun w w' h => historyAgent_run_injective (congrArg Subtype.val h)
  -- the identity of `H` is idempotent, hence `1`
  have he1 : e = 1 := by
    obtain ⟨w, rfl⟩ := hrep e
    have h1 := (hid _ he).1
    rw [hmul] at h1
    have h2 := congrArg List.length (hinj _ _ h1)
    rw [List.length_append] at h2
    have h3 : w = [] := List.length_eq_zero_iff.1 (by omega)
    subst h3
    rfl
  subst he1
  refine Set.eq_singleton_iff_unique_mem.2 ⟨he, fun g hg => ?_⟩
  obtain ⟨k, _, hgk, _⟩ := hinv g hg
  obtain ⟨w, rfl⟩ := hrep g
  obtain ⟨w', rfl⟩ := hrep k
  rw [hmul, hone] at hgk
  have h2 := congrArg List.length (hinj _ _ hgk)
  rw [List.length_append, List.length_nil] at h2
  have h3 : w = [] := List.length_eq_zero_iff.1 (by omega)
  subst h3
  rfl

/-- **Finiteness cannot be dropped in Theorem `thm:transport`(i)** (Example `ex:free-predictor`,
main.tex l.865): for the history-storing predictor of `coin`, the subgroup `G = S_p` (a group of
order two) is not the image under `Φ` of any subgroup of `S_A`. -/
theorem transport_fails_without_finiteness :
    ¬ ∃ H : Set historyAgent.SA, IsSubgroup H ∧ historyAgent.Phi '' H = Set.univ := by
  rintro ⟨H, hH, himg⟩
  rw [historyAgent_subgroup_trivial hH, Set.image_singleton, map_one] at himg
  have : coinSwap ∈ ({1} : Set coin.Sp) := himg ▸ Set.mem_univ _
  exact coinSwap_ne_one this

/-- The update monoid of the history-storing predictor is infinite, as it must be by
Theorem `thm:transport`(i) (main.tex l.866). -/
theorem historyAgent_SA_infinite : ¬ Finite historyAgent.SA := by
  intro h
  haveI := h
  obtain ⟨H, hH, himg⟩ := historyAgent.transport_subgroup coin_Sp_isSubgroup
  exact transport_fails_without_finiteness ⟨H, hH, himg⟩

end Dovetail.Predictor

#print axioms Dovetail.Predictor.coin_Sp_isSubgroup
#print axioms Dovetail.Predictor.coin_Sp_card
#print axioms Dovetail.Predictor.historyAgent
#print axioms Dovetail.Predictor.historyAgent_run_injective
#print axioms Dovetail.Predictor.historyAgent_subgroup_trivial
#print axioms Dovetail.Predictor.transport_fails_without_finiteness
