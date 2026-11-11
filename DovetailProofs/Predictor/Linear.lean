import DovetailProofs.Predictor.Syntactic

/-!
# The linear realisation and the likelihood layer

Formalises Sections 7 and 8 of `Lattice/main.tex`:

* the Hankel rows `r_u`, the space `V = span{r_u}`, the shift operators `T_o` and the word
  operators `T_w` (l.1273–1313);
* observability and the readout identity `p(w) = λ(T_w r_ε)` (Proposition, l.1341);
* Proposition `prop:linear-quotient` (l.1355): every reachable linear realisation surjects
  linearly and equivariantly onto `V`, hence `dim V ≤ dim V'` and the operator monoid of `V'`
  surjects onto that of `V`;
* the monoid `𝒩 ⋊ S_p` (Definition l.1507, Lemma l.1515): `LikSkel`;
* Proposition `prop:faithful` (l.1466), Theorem `thm:semidirect` (l.1530) and Corollary
  `cor:projection` (l.1552), **stated at the level of words** (see below).

## How the likelihood layer is stated

`S_lin = {T_w|_V}`.  The paper defines `α(T)` and `ℓ_T` from the operator `T` via positive rays.
Here they are defined from a word: `α(T_w) := τ_w` and `ℓ_{T_w}(q_u) := q_u(w) = p(uw)/p(u)`
(`lik`; this is the displayed formula at l.1461), with `ℓ(†) = 1`.  Then

  `T_w|_V = T_{w'}|_V  ↔  τ_w = τ_{w'} ∧ ℓ_w = ℓ_{w'}`        (`linRun_eqOn_iff`)

says simultaneously that `Λ(T_w) := (ℓ_w, τ_w)` is well defined on `S_lin` (direction `→`, which
includes the well-definedness of `α` and of `ℓ`) and injective (direction `←`, which is
Proposition `prop:faithful`).  `Lam_append` is the cocycle identity, i.e. `Λ` is multiplicative.
The bundled `MonoidHom` out of the submonoid `S_lin ⊆ End(V)` is not constructed.
-/

namespace Dovetail.Predictor

open Function

section LinRun

variable {O V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The word operator `A_w = A_{o_n} ⋯ A_{o_1}` for `w = o₁ ⋯ oₙ` (main.tex l.1299, l.1358). -/
def linRun (A : O → V →ₗ[ℝ] V) : List O → (V →ₗ[ℝ] V)
  | [] => LinearMap.id
  | o :: w => linRun A w ∘ₗ A o

/-- `A_ε = id` (main.tex l.1358). -/
@[simp] theorem linRun_nil (A : O → V →ₗ[ℝ] V) (x : V) : linRun A [] x = x := rfl

/-- `A_{ow} = A_w A_o` (main.tex l.1358). -/
@[simp] theorem linRun_cons (A : O → V →ₗ[ℝ] V) (o : O) (w : List O) (x : V) :
    linRun A (o :: w) x = linRun A w (A o x) := rfl

/-- `A_{uv} = A_v A_u` (main.tex l.1390). -/
theorem linRun_append (A : O → V →ₗ[ℝ] V) (u v : List O) (x : V) :
    linRun A (u ++ v) x = linRun A v (linRun A u x) := by
  induction u generalizing x with
  | nil => rfl
  | cons o u ih => simp [ih]

/-- The word operator is the paper's composite `δ_w` of the underlying maps (main.tex l.1358). -/
theorem linRun_eq_run (A : O → V →ₗ[ℝ] V) (w : List O) (x : V) :
    linRun A w x = run (fun o => ⇑(A o)) w x := by
  induction w generalizing x with
  | nil => rfl
  | cons o w ih => simp [ih]

end LinRun

/-- The shift operator `(T_o f)(v) = f(ov)` on `W = ℝ^{O*}` (main.tex l.1294). -/
def shiftOp {O : Type*} (o : O) : (List O → ℝ) →ₗ[ℝ] (List O → ℝ) where
  toFun f := fun v => f (o :: v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `(T_w f)(v) = f(wv)` (main.tex l.1296, l.1299). -/
theorem linRun_shiftOp_apply {O : Type*} (w : List O) (f : List O → ℝ) (v : List O) :
    linRun shiftOp w f v = f (w ++ v) := by
  induction w generalizing f with
  | nil => rfl
  | cons o w ih => rw [linRun_cons, ih]; rfl

namespace StochLang

variable {O : Type*} [Fintype O] (P : StochLang O)

/-- The unnormalised Hankel row `r_u(v) = p(uv)` (main.tex l.1278). -/
def row (u : List O) : List O → ℝ := fun v => P.p (u ++ v)

/-- `V = span{r_u : u ∈ O*} ⊆ ℝ^{O*}` (main.tex l.1284). -/
def hankelSpace : Submodule ℝ (List O → ℝ) := Submodule.span ℝ (Set.range P.row)

/-- Every row lies in `V` (main.tex l.1284). -/
theorem row_mem (u : List O) : P.row u ∈ P.hankelSpace := Submodule.subset_span ⟨u, rfl⟩

/-- `T_o r_u = r_{uo}` (main.tex l.1298). -/
theorem shiftOp_row (o : O) (u : List O) : shiftOp o (P.row u) = P.row (u ++ [o]) := by
  funext v
  show P.p (u ++ o :: v) = P.p (u ++ [o] ++ v)
  simp

/-- `T_w r_u = r_{uw}` (main.tex l.1303). -/
theorem linRun_shiftOp_row (w u : List O) : linRun shiftOp w (P.row u) = P.row (u ++ w) := by
  funext v
  rw [linRun_shiftOp_apply]
  show P.p (u ++ (w ++ v)) = P.p (u ++ w ++ v)
  simp

/-- `T_o` restricts to an endomorphism of `V` (main.tex l.1298). -/
theorem shiftOp_mem (o : O) {f : List O → ℝ} (hf : f ∈ P.hankelSpace) :
    shiftOp o f ∈ P.hankelSpace := by
  have h : Submodule.map (shiftOp o) P.hankelSpace ≤ P.hankelSpace := by
    rw [hankelSpace, Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    exact ⟨u ++ [o], (P.shiftOp_row o u).symm⟩
  exact h (Submodule.mem_map_of_mem hf)

/-- The readout identity `p(w) = λ(T_w r_ε)` with `λ(f) = f(ε)` (main.tex l.1312). -/
theorem readout_linRun (w : List O) : linRun shiftOp w (P.row []) [] = P.p w := by
  rw [linRun_shiftOp_apply]; simp [row]

omit [Fintype O] in
/-- **Observability** of the canonical realisation (Proposition, main.tex l.1341): if
`λ(T_v f) = 0` for every `v` then `f = 0`. -/
theorem observable (f : List O → ℝ) (h : ∀ v, linRun shiftOp v f [] = 0) : f = 0 := by
  funext v
  have := h v
  rw [linRun_shiftOp_apply] at this
  simpa using this

/-- `r_u = p(u) q_u` for possible `u` (main.tex l.1317). -/
theorem row_eq_smul {u : List O} (hu : 0 < P.p u) : P.row u = P.p u • P.q u := by
  funext v
  show P.p (u ++ v) = P.p u * (P.p (u ++ v) / P.p u)
  have h := hu.ne'
  field_simp

/-- Impossible histories have zero rows (main.tex l.1483). -/
theorem row_eq_zero {u : List O} (hu : P.p u = 0) : P.row u = 0 := by
  funext v
  exact P.p_append_eq_zero hu v

/-- `λ(r_u) = p(u)`: a nonzero row has positive `ε`-coordinate (main.tex l.1480). -/
theorem row_nil (u : List O) : P.row u [] = P.p u := by simp [row]

/-- Equal rows give equal predictive states (the ray map `β` is well defined and injective,
main.tex l.1330). -/
theorem nu_eq_of_row_eq {a b : List O} (h : P.row a = P.row b) : P.nu a = P.nu b := by
  have hp : P.p a = P.p b := by rw [← P.row_nil, ← P.row_nil, h]
  by_cases ha : 0 < P.p a
  · have hb : 0 < P.p b := hp ▸ ha
    rw [P.nu_of_pos ha, P.nu_of_pos hb]
    refine congrArg some (X.ext ?_)
    funext v
    show P.p (a ++ v) / P.p a = P.p (b ++ v) / P.p b
    have hv : P.p (a ++ v) = P.p (b ++ v) := congrFun h v
    rw [hv, hp]
  · have hb : ¬ 0 < P.p b := hp ▸ ha
    rw [P.nu_of_not_pos ha, P.nu_of_not_pos hb]

/-- A predictive state together with the probability of its history determines the row
("its positive ray together with that coordinate determines it uniquely", main.tex l.1480). -/
theorem row_eq_of_nu_eq {a b : List O} (h : P.nu a = P.nu b) (hp : P.p a = P.p b) :
    P.row a = P.row b := by
  by_cases ha : 0 < P.p a
  · have hb : 0 < P.p b := hp ▸ ha
    rw [P.nu_of_pos ha, P.nu_of_pos hb, Option.some.injEq] at h
    have hq : P.q a = P.q b := congrArg Subtype.val h
    rw [P.row_eq_smul ha, P.row_eq_smul hb, hq, hp]
  · have hb : ¬ 0 < P.p b := hp ▸ ha
    rw [P.row_eq_zero (P.not_pos_iff.1 ha), P.row_eq_zero (P.not_pos_iff.1 hb)]

section LinearQuotient

variable {V' : Type*} [AddCommGroup V'] [Module ℝ V']

/-- **Proposition `prop:linear-quotient`** (main.tex l.1355): if `(V', x₀, {A_o}, λ')` is a
reachable linear realisation of `p`, i.e. `p(w) = λ'(A_w x₀)` and `V' = span{A_u x₀}`, then there
is a linear map `L : V' → ℝ^{O*}` with image exactly `V` (a surjection `V' → V`) and
`L A_o = T_o L`. -/
theorem linear_quotient (x₀ : V') (A : O → V' →ₗ[ℝ] V') (lam : V' →ₗ[ℝ] ℝ)
    (hp : ∀ w, P.p w = lam (linRun A w x₀))
    (hreach : Submodule.span ℝ (Set.range fun u => linRun A u x₀) = ⊤) :
    ∃ L : V' →ₗ[ℝ] (List O → ℝ),
      LinearMap.range L = P.hankelSpace ∧ (∀ u, L (linRun A u x₀) = P.row u) ∧
        ∀ o x, L (A o x) = shiftOp o (L x) := by
  let L : V' →ₗ[ℝ] (List O → ℝ) := LinearMap.pi fun v => lam ∘ₗ linRun A v
  have hL : ∀ x v, L x v = lam (linRun A v x) := fun _ _ => rfl
  have hrow : ∀ u, L (linRun A u x₀) = P.row u := by
    intro u
    funext v
    show lam (linRun A v (linRun A u x₀)) = P.p (u ++ v)
    rw [← linRun_append, ← hp]
  refine ⟨L, ?_, hrow, fun o x => by funext v; rfl⟩
  rw [LinearMap.range_eq_map, ← hreach, Submodule.map_span, hankelSpace]
  congr 1
  ext f
  constructor
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, (hrow u).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨_, ⟨u, rfl⟩, hrow u⟩

/-- **Minimality of the canonical realisation** (Proposition, main.tex l.1341): every reachable
(finite-dimensional) linear realisation of `p` has dimension at least `dim V`. -/
theorem finrank_hankelSpace_le [FiniteDimensional ℝ V'] (x₀ : V') (A : O → V' →ₗ[ℝ] V')
    (lam : V' →ₗ[ℝ] ℝ) (hp : ∀ w, P.p w = lam (linRun A w x₀))
    (hreach : Submodule.span ℝ (Set.range fun u => linRun A u x₀) = ⊤) :
    Module.finrank ℝ P.hankelSpace ≤ Module.finrank ℝ V' := by
  obtain ⟨L, hL, _⟩ := P.linear_quotient x₀ A lam hp hreach
  have := LinearMap.finrank_range_le L
  rwa [hL] at this

/-- The restriction of `T_o` to `V` (main.tex l.1298). -/
def shiftV (o : O) : P.hankelSpace → P.hankelSpace :=
  fun f => ⟨shiftOp o f.1, P.shiftOp_mem o f.2⟩

/-- **Proposition `prop:linear-quotient`, last sentence** (main.tex l.1375, l.1393): the linear
surjection induces a surjective homomorphism `Ψ` from the operator monoid `⟨A_o⟩` onto the minimal
operator monoid `S_lin = ⟨T_o|_V⟩`, with `Ψ(A_w) = T_w`.  (Both monoids are taken as monoids of
maps under composition, as in Lemma `lem:descent`.) -/
theorem linear_quotient_monoid (x₀ : V') (A : O → V' →ₗ[ℝ] V') (lam : V' →ₗ[ℝ] ℝ)
    (hp : ∀ w, P.p w = lam (linRun A w x₀))
    (hreach : Submodule.span ℝ (Set.range fun u => linRun A u x₀) = ⊤) :
    ∃ Ψ : transitionMonoid (V := V') (fun o => ⇑(A o)) →*
        transitionMonoid (V := P.hankelSpace) P.shiftV,
      Surjective Ψ ∧ ∀ w : List O,
        (Ψ ⟨run (fun o => ⇑(A o)) w, run_mem_transitionMonoid _ w⟩ :
          Function.End P.hankelSpace) = run P.shiftV w := by
  obtain ⟨L, hL, _, hLA⟩ := P.linear_quotient x₀ A lam hp hreach
  have hmem : ∀ x, L x ∈ P.hankelSpace := fun x => by
    rw [← hL]; exact LinearMap.mem_range_self L x
  refine descent_run (fun o => ⇑(A o)) P.shiftV (fun x => ⟨L x, hmem x⟩) ?_ ?_
  · rintro ⟨f, hf⟩
    rw [← hL] at hf
    obtain ⟨x, rfl⟩ := hf
    exact ⟨x, rfl⟩
  · intro o x
    exact Subtype.ext (hLA o x)

end LinearQuotient

/-- **The likelihood** `ℓ_{T_w} : X̂_p → ℝ≥0` (main.tex l.1452, l.1461):
`ℓ_{T_w}(q_u) = p(uw)/p(u) = q_u(w)` and `ℓ(†) = 1`. -/
noncomputable def lik (w : List O) : Option P.X → NNReal
  | none => 1
  | some x => (x.1 w).toNNReal

/-- `ℓ_{T_w}([r_u]) = p(uw)/p(u)` (main.tex l.1461). -/
theorem lik_nu {u : List O} (hu : 0 < P.p u) (w : List O) :
    P.lik w (P.nu u) = (P.p (u ++ w) / P.p u).toNNReal := by
  rw [P.nu_of_pos hu]; rfl

/-- **The cocycle identity** `ℓ_{TU}(x) = ℓ_T(U·x) ℓ_U(x)` for `U = T_v`, `T = T_w`
(main.tex l.1457, l.1542), valid at every `x ∈ X̂_p` including `†` and states killed by `U`. -/
theorem lik_append (v w : List O) (y : Option P.X) :
    P.lik (v ++ w) y = P.lik w (run P.tau v y) * P.lik v y := by
  cases y with
  | none => rw [P.run_tau_none]; simp [lik]
  | some x =>
    obtain ⟨u, hu, hx⟩ := P.exists_nu_eq_some x
    rw [← hx, P.run_tau_nu, P.lik_nu hu, P.lik_nu hu]
    by_cases huv : 0 < P.p (u ++ v)
    · rw [P.lik_nu huv, ← Real.toNNReal_mul (div_nonneg (P.nonneg _) huv.le)]
      congr 1
      rw [List.append_assoc]
      have h1 := hu.ne'
      have h2 := huv.ne'
      field_simp
    · have h0 : P.p (u ++ v) = 0 := P.not_pos_iff.1 huv
      have h1 : P.p (u ++ (v ++ w)) = 0 := by
        rw [← List.append_assoc]; exact P.p_append_eq_zero h0 w
      rw [h0, h1]
      simp

/-- **Proposition `prop:faithful` together with the well-definedness of `α` and `ℓ`**
(main.tex l.1466, l.1420, l.1452): two word operators agree on `V` if and only if they induce
the same update of `X̂_p` and the same likelihood function.

* `→`: `α(T_w) := τ_w` and `ℓ_{T_w}` depend only on the operator `T_w|_V`;
* `←`: this is Proposition `prop:faithful`: same action and same likelihoods force `T = T'`. -/
theorem linRun_eqOn_iff (w w' : List O) :
    Set.EqOn (linRun shiftOp w) (linRun shiftOp w') P.hankelSpace ↔
      run P.tau w = run P.tau w' ∧ P.lik w = P.lik w' := by
  constructor
  · intro h
    have hrow : ∀ u, P.row (u ++ w) = P.row (u ++ w') := fun u => by
      rw [← P.linRun_shiftOp_row, ← P.linRun_shiftOp_row]
      exact h (P.row_mem u)
    refine ⟨(P.tau_eq_iff_forall_nu w w').2 fun u => P.nu_eq_of_row_eq (hrow u), ?_⟩
    funext y
    cases y with
    | none => rfl
    | some x =>
      obtain ⟨u, hu, hx⟩ := P.exists_nu_eq_some x
      rw [← hx, P.lik_nu hu, P.lik_nu hu, ← P.row_nil (u ++ w), ← P.row_nil (u ++ w'), hrow u]
  · rintro ⟨hτ, hℓ⟩
    show Set.EqOn _ _ (Submodule.span ℝ (Set.range P.row) : Set (List O → ℝ))
    refine LinearMap.eqOn_span ?_
    rintro _ ⟨u, rfl⟩
    rw [P.linRun_shiftOp_row, P.linRun_shiftOp_row]
    by_cases hu : 0 < P.p u
    · have hν : P.nu (u ++ w) = P.nu (u ++ w') := by
        rw [← P.run_tau_nu, ← P.run_tau_nu, hτ]
      have hl := congrFun hℓ (P.nu u)
      rw [P.lik_nu hu, P.lik_nu hu,
        Real.toNNReal_eq_toNNReal_iff (div_nonneg (P.nonneg _) hu.le)
          (div_nonneg (P.nonneg _) hu.le)] at hl
      have hp : P.p (u ++ w) = P.p (u ++ w') := (div_left_inj' hu.ne').1 hl
      exact P.row_eq_of_nu_eq hν hp
    · have h0 : P.p u = 0 := P.not_pos_iff.1 hu
      rw [P.row_eq_zero (P.p_append_eq_zero h0 w), P.row_eq_zero (P.p_append_eq_zero h0 w')]

end StochLang

/-- **The monoid `𝒩 ⋊ S`** (Definition, main.tex l.1507): pairs `(f, s)` of a nonnegative
function on the state set and an update, with `(f, s)(g, t) = ((f ∘ t) g, s t)`.
For `X = X̂_p` and `S = S_p` this is the paper's `𝒩 ⋊ S_p`. -/
@[ext] structure LikSkel (X : Type*) (S : Submonoid (Function.End X)) where
  /-- The likelihood coordinate, an element of `𝒩 = (ℝ≥0)^X`. -/
  weight : X → NNReal
  /-- The update coordinate. -/
  update : S

namespace LikSkel

variable {X : Type*} {S : Submonoid (Function.End X)}

/-- The multiplication `(f, s)(g, t) = ((f ∘ t) g, s t)` (Definition, main.tex l.1511). -/
instance : Mul (LikSkel X S) :=
  ⟨fun a b => ⟨fun x => a.weight ((b.update : Function.End X) x) * b.weight x,
    a.update * b.update⟩⟩

/-- The identity `(𝟏, id)` (Lemma, main.tex l.1516). -/
instance : One (LikSkel X S) := ⟨⟨fun _ => 1, 1⟩⟩

/-- The multiplication of `𝒩 ⋊ S`, first coordinate (main.tex l.1511). -/
theorem mul_weight (a b : LikSkel X S) (x : X) :
    (a * b).weight x = a.weight ((b.update : Function.End X) x) * b.weight x := rfl

/-- The multiplication of `𝒩 ⋊ S`, second coordinate (main.tex l.1511). -/
theorem mul_update (a b : LikSkel X S) : (a * b).update = a.update * b.update := rfl

/-- **Lemma (main.tex l.1515)**: `𝒩 ⋊ S_p` is a monoid with identity `(𝟏, id)`. -/
instance : Monoid (LikSkel X S) where
  mul_assoc a b c := LikSkel.ext (funext fun x => by
    show a.weight ((b.update : Function.End X) ((c.update : Function.End X) x)) *
        b.weight ((c.update : Function.End X) x) * c.weight x =
      a.weight ((b.update : Function.End X) ((c.update : Function.End X) x)) *
        (b.weight ((c.update : Function.End X) x) * c.weight x)
    rw [mul_assoc]) (mul_assoc _ _ _)
  one_mul a := LikSkel.ext (funext fun x => by
    show (1 : NNReal) * a.weight x = a.weight x
    rw [one_mul]) (one_mul _)
  mul_one a := LikSkel.ext (funext fun x => by
    show a.weight x * (1 : NNReal) = a.weight x
    rw [mul_one]) (mul_one _)

/-- The projection `π : 𝒩 ⋊ S_p → S_p` (Corollary `cor:projection`, main.tex l.1554). -/
def proj : LikSkel X S →* S where
  toFun a := a.update
  map_one' := rfl
  map_mul' _ _ := rfl

end LikSkel

namespace StochLang

variable {O : Type*} [Fintype O] (P : StochLang O)

/-- `Λ(T_w) = (ℓ_{T_w}, α(T_w)) ∈ 𝒩 ⋊ S_p` (Theorem `thm:semidirect`, main.tex l.1534). -/
noncomputable def Lam (w : List O) : LikSkel (Option P.X) P.Sp :=
  ⟨P.lik w, ⟨run P.tau w, run_mem_transitionMonoid P.tau w⟩⟩

/-- `Λ(id) = (𝟏, id)` (Theorem `thm:semidirect`, main.tex l.1530). -/
theorem Lam_nil : P.Lam [] = 1 := by
  refine LikSkel.ext (funext fun y => ?_) rfl
  cases y with
  | none => rfl
  | some x =>
    obtain ⟨u, hu, hx⟩ := P.exists_nu_eq_some x
    show P.lik [] (some x) = 1
    rw [← hx, P.lik_nu hu]
    simp [hu.ne']

/-- **Theorem `thm:semidirect`, multiplicativity** (main.tex l.1530, l.1542): since
`T_w T_v = T_{vw}`, the homomorphism property of `Λ` is `Λ(T_{vw}) = Λ(T_w) Λ(T_v)`; its first
coordinate is the cocycle identity and its second is `τ_w ∘ τ_v = τ_{vw}`. -/
theorem Lam_append (v w : List O) : P.Lam (v ++ w) = P.Lam w * P.Lam v := by
  refine LikSkel.ext (funext fun y => ?_) (Subtype.ext ?_)
  · exact P.lik_append v w y
  · exact run_append_eq P.tau v w

/-- **Theorem `thm:semidirect`, well-definedness and injectivity** (main.tex l.1530):
`Λ(T_w) = Λ(T_{w'})` if and only if `T_w = T_{w'}` on `V`.  So `T_w|_V ↦ Λ(T_w)` is a well-defined
injective map `S_lin → 𝒩 ⋊ S_p`; with `Lam_nil` and `Lam_append` it is an injective monoid
homomorphism. -/
theorem Lam_eq_iff (w w' : List O) :
    P.Lam w = P.Lam w' ↔ Set.EqOn (linRun shiftOp w) (linRun shiftOp w') P.hankelSpace := by
  rw [P.linRun_eqOn_iff, LikSkel.ext_iff, and_comm]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨congrArg Subtype.val h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Subtype.ext h1, h2⟩

/-- **Corollary `cor:projection`** (main.tex l.1552): `α = π ∘ Λ`; two operators are
`κ_pred`-related (same update) exactly when their images under `Λ` agree in the second
coordinate. -/
theorem proj_Lam (w : List O) :
    (LikSkel.proj (P.Lam w) : Function.End (Option P.X)) = run P.tau w := rfl

end StochLang

end Dovetail.Predictor

#print axioms Dovetail.Predictor.StochLang.linear_quotient
#print axioms Dovetail.Predictor.StochLang.finrank_hankelSpace_le
#print axioms Dovetail.Predictor.StochLang.linear_quotient_monoid
#print axioms Dovetail.Predictor.StochLang.linRun_eqOn_iff
#print axioms Dovetail.Predictor.StochLang.Lam_append
#print axioms Dovetail.Predictor.StochLang.Lam_eq_iff
