import DovetailProofs.Predictor.Interval
import DovetailProofs.Predictor.Reset
import DovetailProofs.Predictor.Rank

/-!
# First-order Markov chains: `S_p ≅ R_n^1` and a non-distributive inherited interval

Formalises Proposition `prop:markov-reset-general` of `Lattice/main.tex` (l.1810) and its
consequences (l.1845): for a first-order Markov chain on `n ≥ 2` symbols with strictly positive
initial distribution and strictly positive transition matrix with pairwise distinct rows,

* `S_p ≅ R_n^1` (`MarkovChain.resetEquiv`);
* `Con(S_p) ≅ Π_n ⊕ 𝟏` (`MarkovChain.conSpEquiv`);
* for `n ≥ 3`, `Con(S_p)` is non-distributive (`MarkovChain.nonDistrib_con_Sp`), and so is
  `Con(S_A)` for every reachable exact predictive agent `A` (`MarkovChain.nonDistrib_con_SA`);
* every generator has live rank one (`MarkovChain.rk_tau`, Example at l.1136).

The alphabet is an arbitrary finite type `O` (the paper's `{1, …, n}`); `n ≥ 2` is `Nontrivial O`
and `n ≥ 3` is the existence of three distinct symbols.
-/

namespace Dovetail.Predictor

open Function

/-- A first-order Markov chain on the finite alphabet `O` with strictly positive initial
distribution `π`, strictly positive transition matrix `M` and pairwise distinct rows
(hypotheses of Proposition `prop:markov-reset-general`, main.tex l.1812). -/
structure MarkovChain (O : Type*) [Fintype O] where
  /-- The initial distribution. -/
  init : O → ℝ
  /-- The transition matrix; `trans i j` is the probability of `j` after `i`. -/
  trans : O → O → ℝ
  /-- The initial distribution is strictly positive. -/
  init_pos : ∀ i, 0 < init i
  /-- The initial distribution sums to one. -/
  init_sum : ∑ i, init i = 1
  /-- The transition matrix is strictly positive. -/
  trans_pos : ∀ i j, 0 < trans i j
  /-- Each row of the transition matrix sums to one. -/
  trans_sum : ∀ i, ∑ j, trans i j = 1
  /-- The rows of the transition matrix are pairwise distinct. -/
  rows_injective : Injective trans

namespace MarkovChain

variable {O : Type*} [Fintype O] (C : MarkovChain O)

/-- The law `g_i` of the future after a history ending in `i`
(main.tex l.1698, l.1825): `g_i(j₁ ⋯ j_k) = M_{i j₁} M_{j₁ j₂} ⋯`. -/
noncomputable def chainFrom : O → List O → ℝ
  | _, [] => 1
  | i, j :: w => C.trans i j * chainFrom j w

/-- The last symbol of `i · w`. -/
def endSym : O → List O → O
  | i, [] => i
  | _, j :: w => endSym j w

omit [Fintype O] in
/-- The last symbol after appending one symbol. -/
theorem endSym_snoc (i : O) (w : List O) (o : O) : endSym i (w ++ [o]) = o := by
  induction w generalizing i with
  | nil => rfl
  | cons j w ih => exact ih j

/-- Markov property: the chain law factorises through the last symbol (main.tex l.1825). -/
theorem chainFrom_append (i : O) (u v : List O) :
    C.chainFrom i (u ++ v) = C.chainFrom i u * C.chainFrom (endSym i u) v := by
  induction u generalizing i with
  | nil => simp [chainFrom, endSym]
  | cons j u ih => simp only [List.cons_append, chainFrom, endSym, ih, mul_assoc]

/-- Full support of the transition matrix (main.tex l.1827). -/
theorem chainFrom_pos (i : O) (w : List O) : 0 < C.chainFrom i w := by
  induction w generalizing i with
  | nil => exact one_pos
  | cons j w ih => exact mul_pos (C.trans_pos i j) (ih j)

/-- The word probabilities of the chain: `p(i w) = π_i g_i(w)` (main.tex l.1812). -/
noncomputable def prob : List O → ℝ
  | [] => 1
  | i :: w => C.init i * C.chainFrom i w

/-- Every word is possible (main.tex l.1827). -/
theorem prob_pos (w : List O) : 0 < C.prob w := by
  cases w with
  | nil => exact one_pos
  | cons i w => exact mul_pos (C.init_pos i) (C.chainFrom_pos i w)

/-- The stochastic language of the Markov chain (main.tex l.1812). -/
noncomputable def lang : StochLang O where
  p := C.prob
  nonneg w := (C.prob_pos w).le
  nil := rfl
  consistent u := by
    cases u with
    | nil => simp [prob, chainFrom, C.init_sum]
    | cons i w =>
      simp only [List.cons_append, prob, chainFrom_append, chainFrom, mul_one]
      rw [← Finset.mul_sum, ← Finset.mul_sum, C.trans_sum, mul_one]

/-- Every word is possible (main.tex l.1827). -/
theorem lang_pos (w : List O) : 0 < C.lang.p w := C.prob_pos w

/-- After every nonempty history the conditional future law is the law `g_j` of its last symbol
(main.tex l.1825). -/
theorem q_snoc (u : List O) (j : O) : C.lang.q (u ++ [j]) = C.chainFrom j := by
  funext v
  show C.prob (u ++ [j] ++ v) / C.prob (u ++ [j]) = _
  cases u with
  | nil =>
    have h : C.init j ≠ 0 := (C.init_pos j).ne'
    simp only [List.nil_append, List.singleton_append, prob, chainFrom, mul_one]
    rw [mul_div_cancel_left₀ _ h]
  | cons i w =>
    have h : C.init i * C.chainFrom i (w ++ [j]) ≠ 0 :=
      (mul_pos (C.init_pos i) (C.chainFrom_pos i _)).ne'
    simp only [List.cons_append, prob]
    rw [chainFrom_append, endSym_snoc, ← mul_assoc, mul_div_cancel_left₀ _ h]

/-- The predictive state `g_j` (main.tex l.1698). -/
noncomputable def g (j : O) : C.lang.X := C.lang.qState [j] (C.lang_pos [j])

/-- `ν(u j) = g_j` (main.tex l.1825). -/
theorem nu_snoc (u : List O) (j : O) : C.lang.nu (u ++ [j]) = some (C.g j) := by
  rw [C.lang.nu_of_pos (C.lang_pos _)]
  refine congrArg some (StochLang.X.ext ?_)
  show C.lang.q (u ++ [j]) = C.lang.q ([] ++ [j])
  rw [q_snoc, q_snoc]

/-- Distinct transition rows make the `g_i` pairwise distinct (main.tex l.1826). -/
theorem g_injective : Injective C.g := by
  intro i j h
  have h1 : C.lang.q ([] ++ [i]) = C.lang.q ([] ++ [j]) := congrArg Subtype.val h
  rw [q_snoc, q_snoc] at h1
  apply C.rows_injective
  funext k
  have := congrFun h1 [k]
  simpa [chainFrom] using this

/-- The reset map `c_j` on `X̂_p`: every live state goes to `g_j`, and `†` is fixed
(main.tex l.1709). -/
noncomputable def cmap (j : O) : Option C.lang.X → Option C.lang.X :=
  Option.map fun _ => C.g j

/-- Observing `j` resets every live state to `g_j` (main.tex l.1709, l.1828). -/
theorem tau_eq_cmap (j : O) : C.lang.tau j = C.cmap j := by
  funext y
  cases y with
  | none => rfl
  | some x =>
    obtain ⟨u, _, hx⟩ := C.lang.exists_nu_eq_some x
    rw [← hx, C.lang.tau_nu, nu_snoc, C.lang.nu_of_pos (C.lang_pos u)]
    rfl

/-- The representation `R^1 → 𝒯_{X̂_p}`: `1 ↦ id`, `c_j ↦` the reset to `g_j`
(main.tex l.1710). -/
noncomputable def resetHom : Reset O →* Function.End (Option C.lang.X) where
  toFun r := match r with
    | none => 1
    | some j => C.cmap j
  map_one' := rfl
  map_mul' a b := by
    cases a with
    | none => rfl
    | some i =>
      cases b with
      | none => rfl
      | some j =>
        funext y
        cases y <;> rfl

/-- The representation is faithful when `n ≥ 2`: the `n` resets are distinct (distinct rows) and
none is the identity (main.tex l.1830). -/
theorem resetHom_injective [Nontrivial O] : Injective C.resetHom := by
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some j =>
      obtain ⟨k, hk⟩ := exists_ne j
      have := congrFun h (some (C.g k))
      have h' : some (C.g k) = some (C.g j) := this
      exact absurd (C.g_injective (Option.some.inj h')) hk
  | some i =>
    cases b with
    | none =>
      obtain ⟨k, hk⟩ := exists_ne i
      have := congrFun h (some (C.g k))
      have h' : some (C.g i) = some (C.g k) := this
      exact absurd (C.g_injective (Option.some.inj h')).symm hk
    | some j =>
      have := congrFun h (some (C.g i))
      have h' : some (C.g i) = some (C.g j) := this
      exact congrArg some (C.g_injective (Option.some.inj h'))

/-- The generated transformations are precisely the identity and the reset maps
(main.tex l.1829). -/
theorem range_resetHom (s : Function.End (Option C.lang.X)) :
    s ∈ C.lang.Sp ↔ ∃ r, C.resetHom r = s := by
  constructor
  · intro hs
    obtain ⟨w, rfl⟩ := (C.lang.mem_Sp_iff s).1 hs
    clear hs
    induction w using List.reverseRecOn with
    | nil => exact ⟨1, rfl⟩
    | append_singleton w o _ =>
      refine ⟨Reset.c o, ?_⟩
      funext y
      rw [run_snoc, tau_eq_cmap]
      show C.cmap o y = C.cmap o (run C.lang.tau w y)
      cases y with
      | none => rw [C.lang.run_tau_none]
      | some x =>
        obtain ⟨u, _, hx⟩ := C.lang.exists_nu_eq_some x
        rw [← hx, C.lang.run_tau_nu, C.lang.nu_of_pos (C.lang_pos u),
          C.lang.nu_of_pos (C.lang_pos (u ++ w))]
        rfl
  · rintro ⟨r, rfl⟩
    cases r with
    | none => exact C.lang.Sp.one_mem
    | some j =>
      refine (C.lang.mem_Sp_iff _).2 ⟨[j], ?_⟩
      show C.lang.tau j = C.cmap j
      exact C.tau_eq_cmap j

/-- **Proposition `prop:markov-reset-general`** (main.tex l.1810): for a first-order Markov chain
on `n ≥ 2` symbols with strictly positive initial distribution and strictly positive transition
matrix with pairwise distinct rows, `S_p ≅ R_n^1`. -/
noncomputable def resetEquiv [Nontrivial O] : Reset O ≃* C.lang.Sp :=
  MulEquiv.ofBijective
    (C.resetHom.codRestrict C.lang.Sp fun r => (C.range_resetHom _).2 ⟨r, rfl⟩)
    ⟨fun a b h => C.resetHom_injective (congrArg Subtype.val h),
      fun ⟨s, hs⟩ => by
        obtain ⟨r, hr⟩ := (C.range_resetHom s).1 hs
        exact ⟨r, Subtype.ext hr⟩⟩

/-- The isomorphism sends the constant `c_j` to `τ_j` (main.tex l.1830). -/
theorem resetEquiv_c [Nontrivial O] (j : O) :
    ((C.resetEquiv (Reset.c j) : C.lang.Sp) : Function.End (Option C.lang.X)) = C.lang.tau j :=
  (C.tau_eq_cmap j).symm

/-- **Proposition `prop:markov-reset-general`, "consequently"** (main.tex l.1817):
`Con(S_p) ≅ Π_n ⊕ 𝟏`. -/
noncomputable def conSpEquiv [Nontrivial O] : Con C.lang.Sp ≃o WithTop (Setoid O) :=
  (conCongr C.resetEquiv.symm).trans Reset.conEquiv

/-- **`Con(S_p)` contains `M₃`** for a Markov chain as above on at least three symbols
(Corollary, main.tex l.1798). -/
theorem exists_isM3_con_Sp [Nontrivial O] {x y z : O} (hxy : x ≠ y) (hyz : y ≠ z)
    (hxz : x ≠ z) : ∃ bot a b c top : Con C.lang.Sp, IsM3 bot a b c top :=
  ⟨_, _, _, _, _, (IsM3.of_surjective C.resetEquiv.symm.toMonoidHom
    C.resetEquiv.symm.surjective (Reset.exists_isM3 hxy hyz hxz)).1⟩

/-- **Proposition `prop:markov-reset-general`, last claim** (main.tex l.1821): `Con(S_p)` is
non-distributive for every `n ≥ 3`. -/
theorem nonDistrib_con_Sp [Nontrivial O] {x y z : O} (hxy : x ≠ y) (hyz : y ≠ z)
    (hxz : x ≠ z) : NonDistrib (Con C.lang.Sp) :=
  NonDistrib.of_surjective C.resetEquiv.symm.toMonoidHom C.resetEquiv.symm.surjective
    (Reset.nonDistrib hxy hyz hxz)

/-- **Conclusion (i) of main.tex l.1848**: every reachable exact predictor of such a chain on at
least three symbols inherits a non-distributive congruence lattice (containing a non-distributive
interval `[κ, ⊤]`). -/
theorem nonDistrib_con_SA [Nontrivial O] {x y z : O} (hxy : x ≠ y) (hyz : y ≠ z)
    (hxz : x ≠ z) {Q : Type*} (A : ExactAgent C.lang Q) : NonDistrib (Con A.SA) :=
  A.nonDistrib_of_Sp (C.nonDistrib_con_Sp hxy hyz hxz)

/-- **Every single symbol is synchronising**: `rk(τ_j) = 1` (Example, main.tex l.1136). -/
theorem rk_tau (j : O) : rk (C.lang.tau j) = 1 := by
  have : liveImage (C.lang.tau j) = {C.g j} := by
    rw [tau_eq_cmap]
    ext x
    constructor
    · rintro ⟨y, hy⟩
      cases y with
      | none => exact absurd hy (Option.some_ne_none x).symm
      | some z => exact (Option.some.inj hy).symm
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨some (C.g j), rfl⟩
  rw [rk, this, Set.encard_singleton]

end MarkovChain

end Dovetail.Predictor

#print axioms Dovetail.Predictor.MarkovChain.resetEquiv
#print axioms Dovetail.Predictor.MarkovChain.conSpEquiv
#print axioms Dovetail.Predictor.MarkovChain.nonDistrib_con_Sp
#print axioms Dovetail.Predictor.MarkovChain.nonDistrib_con_SA
#print axioms Dovetail.Predictor.MarkovChain.rk_tau
