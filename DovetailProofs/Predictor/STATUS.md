# Formalisation status: `Lattice/main.tex` → `DovetailProofs/Predictor/`

Source: "What Every Exact Predictor Must Compute: Divisibility Lower Bounds from Predictive
Monoids" (`Lattice/main.tex`). Toolchain `leanprover/lean4:v4.32.0-rc1`, Mathlib `v4.32.0-rc1`.

Scope (as revised by the author): only results that are new in the paper, with the paper's own
proofs; cited background is listed in one line each and not formalised beyond what the proofs of
the new results need.

No `sorry`, `admit`, `axiom`, `native_decide` or `implemented_by` anywhere in the 15 modules. No
`*Open.lean` file was needed. No gap or false statement was found in any result that was
formalised.

## Conventions that differ from the text (all recorded in docstrings)

- Words are `List O`; `run step w` is the paper's `δ_w = δ_{o_n} ∘ ⋯ ∘ δ_{o_1}`. The existing
  `Dovetail.transitionMonoid` (range of `FreeMonoid.lift`) uses the reversed word order, but as a
  set of maps under composition it is exactly the paper's `⟨δ_o⟩`
  (`mem_transitionMonoid_iff`, `run_eq_lift`). The comment in `Descent.lean` that it is "the
  opposite monoid of the paper's `S`" is therefore inaccurate: only the parametrisation by words
  is reversed. `Descent.lean` was reused unchanged.
- `X̂_p = Option P.X`, `†` = `none`. `τ_o` is defined intrinsically by the shift
  `f ↦ f(o·)/f(o)`; `tau_nu` proves it is the paper's `q_u ↦ q_{uo}` or `†`.
- Agent definition: `F : Q⁺ → X_p` is a total `readout : Q → (O* → ℝ)` constrained only on live
  states; `Q = Q⁺ ⊔ {d}` is the pair of fields `live`, `reachable`.
- "Subgroup of a monoid" is the predicate `IsSubgroup G` on a subset; aperiodicity is the
  equational form `∀ s ∃ n, sⁿ = sⁿ⁺¹`.
- `M₃` sublattice = `IsM3 bot a b c top`; non-distributive = `NonDistrib L` (the distributive law
  fails for some triple). `Π_n` = `Setoid α`; `Π_n ⊕ 𝟏` = `WithTop (Setoid α)`.

## Results

"Kind": N = new (author's), B = background (cited).

| Paper result (line) | Kind | Lean name (file) | Status |
|---|---|---|---|
| Def. stochastic language (211) | N | `StochLang` (Basic) | definition |
| Def. canonical predictive states (249), `τ_o` (265) | N | `StochLang.X`, `tau`, `nu` (Basic) | definition |
| Lemma, `τ_o` well defined (276) | N | `StochLang.q_congr`, `tau_nu` (Basic) | proved |
| Def. `S_p` (296) | N | `StochLang.Sp` (Basic) | definition |
| Lemma `lem:descent` (325) | N | `descent_run` (Agent), from existing `Dovetail.descent` | proved (alphabet need not be finite) |
| Def. reachable exact predictive agent (373) | N | `ExactAgent` (Agent) | definition (encoding above) |
| Thm `thm:predictor-quotient` (423) | N | `ExactAgent.predictor_quotient`, `L`, `L_surjective`, `L_step` (Agent) | proved |
| Cor `cor:quotient` (460) | N | `ExactAgent.exists_Phi`, `Phi`, `Phi_run`, `kappa` (Agent) | proved |
| Remark `rem:uniform` (481) | N | — | not formalised (remark, not needed by any theorem) |
| Def. follower sets, `σ_o`, `S_supp` (507–542) | N | `follower`, `Xsupp`, `sigmaStep`, `Ssupp` (Support) | definition |
| Prop `prop:support-quotient` (544) | N | `StochLang.support_quotient` (Support) | proved |
| Cor `cor:support-tower` (567) | N | `exists_suppHom`, `ExactAgent.PhiSupp`, `PhiSupp_run`, `kappa_le_kappa'` (Support) | proved (differs: composite defined as `Ψ ∘ Φ`; `PhiSupp_run` shows it is the descent map of the composite surjection) |
| Remark `rem:full-support` (606) | N | `StochLang.Ssupp_trivial_iff` (Support) | proved (differs: converse via `σ_w(F_ε) = F_w ≠ †`, not via a shortest impossible word) |
| Z1R / RRXOR computations (619), Example `ex:one-zero` (656) | N | — | not formalised: computed examples, out of scope |
| Lemma `lem:syntactic` (i) (729) | N | `tau_eq_iff_synEq`, `synMonoidEquiv : M(ν) ≃* S_pᵐᵒᵖ` (Syntactic) | proved |
| Lemma `lem:syntactic` (ii) | N | `sigma_eq_iff_synEq`, `synMonoidSuppEquiv` (Syntactic) | proved |
| Lemma `lem:syntactic` (iii) | N | `synEq_nu_iff`, `synCon_nu_le` (Syntactic) | proved (differs: `≡_ν = ⋂ ≡_{K_x}` and `≡_ν ⊆ ≡_{K_x}` proved; the product monoid `∏ M(K_x)` is not constructed) |
| Remark `rem:word-problem` (782) | N | `nu_eq_run` (Basic), `tau_eq_iff_forall_rep` (WordProblem) | proved |
| Thm `thm:transport`, `S_p` finite (806) | N | `ExactAgent.Sp_finite`, `SA_finite_of_finite` (Transport) | proved |
| Thm `thm:transport` (i) | N | `exists_subgroup_image_eq` (Semigroup), `ExactAgent.transport_subgroup`, `transport_divides` (Transport) | proved (paper's minimal-subsemigroup argument) |
| Thm `thm:transport` (ii) | N | `IsAperiodic.of_surjective` (Semigroup), `ExactAgent.transport_aperiodic` (Transport) | proved (equational form of aperiodicity; `IsAperiodic.subgroup_trivial` gives "all subgroups trivial"; the converse for finite monoids is background, not formalised) |
| Thm `thm:transport` (iii), `c(S_p) ≤ c(S_A)` | N | — | out of reach (group complexity, wreath products and the Krohn–Rhodes theorem are not in Mathlib; the proof is one line of cited monotonicity) |
| Remark `rem:tight` (844) | N | `canonicalAgent`, `canonicalAgent_SA`, `aperiodic_iff_exists_agent` (Agent, Transport) | proved for the canonical machine and aperiodicity; the `c` half is out of reach |
| Example `ex:free-predictor` (854) | N (counterexample the theorem depends on) | `coin`, `coin_Sp_isSubgroup`, `coin_Sp_card`, `historyAgent`, `historyAgent_run_injective`, `historyAgent_subgroup_trivial`, `transport_fails_without_finiteness` (FreePredictor) | proved (not stated: "every finite 2-generated monoid is a quotient of it") |
| Prop `prop:pred-word` (i) (910) | N | `StochLang.nextSymbol_eq_of_tau_eq` (WordProblem) | proved |
| Prop `prop:pred-word` (ii) | N | — | out of reach (constant-depth circuit reductions) |
| Thm `thm:pred-complexity` (960) | N | — | out of reach (no `AC⁰`/`ACC⁰`/`TC⁰`/`NC¹` in Mathlib; rests on Barrington, Barrington–Thérien, Smolensky). Read, no gap found. The remark at l.1016 is `coin_run_eq_of_length_eq` |
| Cor `cor:transformers` (1043) | N | — | out of reach (as above; conditional on `TC⁰ ≠ NC¹`) |
| Def. live rank (1086), monotonicity (1095) | N | `liveImage`, `rk`, `rk_comp_le_left`, `rk_comp_le_right` (Rank) | proved |
| Thm `thm:rank-bound` (1107) | N | `rank_bound`, `range_run_inter_live` (Rank) | proved |
| Example, reset chain is synchronising (1136) | N | `MarkovChain.rk_tau` (MarkovReset) | proved |
| Example `ex:polya` (1146) | N | — | not formalised: example, out of scope |
| Prop `prop:group-rank` (1220) | N | `liveImage_eq_of_subgroup`, `rk_eq_of_subgroup`, `bijOn_liveImage_of_subgroup`, `exists_perm_rep_of_subgroup` (Rank) | proved (differs: `Sym(I)` is taken on `some '' I ⊆ X̂`; "homomorphism" stated as `ρ k = ρ g * ρ h` whenever `k = g * h`) |
| Prop, canonical realisation minimal (1341) | N (construction classical) | `StochLang.observable`, `readout_linRun`, `finrank_hankelSpace_le` (Linear) | proved (dimension bound for finite-dimensional `V'`) |
| Prop `prop:linear-quotient` (1355) | N | `StochLang.linear_quotient`, `linear_quotient_monoid` (Linear) | proved (`L : V' → ℝ^{O*}` with range exactly `V`) |
| Prop `prop:faithful` (1466) | N | `StochLang.linRun_eqOn_iff` (←) (Linear) | proved (differs: word level, see below) |
| Def. and Lemma, `𝒩 ⋊ S_p` is a monoid (1507, 1515) | N | `LikSkel` and its `Monoid` instance (Linear) | proved |
| Thm `thm:semidirect` (1530) | N | `Lam`, `Lam_nil`, `Lam_append`, `Lam_eq_iff`, `lik_append` (Linear) | proved (differs: word level, see below) |
| Cor `cor:projection` (1552) | N | `LikSkel.proj`, `StochLang.proj_Lam` (Linear) | proved (word level) |
| Cor `cor:con-inheritance` (1640) | N | `conIciEquiv`, `comapCon_inf`, `comapCon_sup`, `ExactAgent.intervalEquiv`, `intervalSuppEquiv`, `interval_subset`, `nonDistrib_of_Sp`, `exists_isM3_of_Sp` (Interval) | proved (differs: the cited correspondence theorem is proved directly; `N₅` not treated separately, it is covered by `NonDistrib`) |
| `θ_scal ⊊ κ_pred` computation (1744) | N | — | not formalised: computation, out of scope |
| Thm `thm:reset-con` (1766) | N | `Reset`, `Reset.one_class`, `Reset.ofSetoid`, `Reset.conEquiv` (Reset) | proved (for any nonempty index type) |
| Cor, `M₃` in `Con(S_p)` (1798) | N | `Reset.isM3_fin3`, `resetChain3_isM3`, `resetChain3_nonDistrib` (Reset, ResetChain3) | proved (differs: the `M₃` `{⊥, a, b, c, θ}` with `θ ≠ ⊤` is exhibited; that `[⊥, θ]` has no further element is not stated separately, it follows from `conEquiv`) |
| Prop `prop:markov-reset-general` (1810) | N | `MarkovChain.resetEquiv`, `conSpEquiv`, `nonDistrib_con_Sp`, `nonDistrib_con_SA` (MarkovReset) | proved |
| Remark `rem:controllers` (1982) | N | — | not formalised (discussion, open) |

Background, not formalised:

- Krohn–Rhodes theorem; group complexity and its monotonicity under division — not formalised: background.
- Barrington; Barrington–Thérien; Barrington et al. (word problems in `NC¹`/`AC⁰`/`ACC⁰`) — not formalised: background.
- Smolensky (`MOD_r ∉ AC⁰`) — not formalised: background.
- Merrill–Sabharwal (transformers in `TC⁰`); Liu et al.; Yang–Chiang–Angluin — not formalised: background.
- Schützenberger's star-free theorem — not formalised: background.
- Finite monoid aperiodic ⇔ all subgroups trivial (converse direction) — not formalised: background.
- Birkhoff representation; `M₃`/`N₅` characterisation of distributivity — not formalised: background (only "`M₃` ⇒ distributive law fails" is proved, `IsM3.not_distrib`).
- Congruence correspondence theorem (Howie) — background, but proved (`conIciEquiv`) because Cor `cor:con-inheritance` needs it for a surjection rather than a quotient.
- Refinement lemma, ε-machines, follower-set automata, Hankel/OOM realisations (Fliess, Jaeger) — not formalised: background.

### Word-level statement of the likelihood layer

The paper defines `α(T)` and `ℓ_T` from an operator `T ∈ S_lin` through positive rays. The Lean
defines them from a word: `α(T_w) := τ_w`, `ℓ_{T_w}(q_u) := q_u(w)` (the paper's formula at
l.1461), `ℓ(†) = 1`. `linRun_eqOn_iff` proves
`T_w|_V = T_{w'}|_V ↔ τ_w = τ_{w'} ∧ ℓ_w = ℓ_{w'}`: direction → is the well-definedness of `α`,
`ℓ` and `Λ` on `S_lin`, direction ← is Prop `prop:faithful` and injectivity of `Λ`. `Lam_append`
is the cocycle identity, i.e. multiplicativity. A bundled `MonoidHom` out of the submonoid
`S_lin ⊆ End(V)` and the ray space are not constructed.

## Build

**Where the build was run.** A harness hook in this session refuses writes to the
`project-a-lean` worktree ("belongs to a different worktree"). The modules were therefore
developed and built in the session scratchpad, in a mirror of the Lake project (same
`lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, unmodified `Descent.lean` and
`Saturation.lean`, `.lake/packages` symlinked to the same shared prebuilt Mathlib, root file
extended with the 15 new imports). The full `lake build` below is of that mirror. It has not been
run inside `project-a-lean` itself, because the files are not there yet.

```
info: DovetailProofs/Predictor/ResetChain3.lean:70:0: 'Dovetail.Predictor.resetChain3' depends on axioms: [propext, Classical.choice, Quot.sound]
info: DovetailProofs/Predictor/ResetChain3.lean:71:0: 'Dovetail.Predictor.resetChain3_isM3' depends on axioms: [propext, Classical.choice, Quot.sound]
info: DovetailProofs/Predictor/ResetChain3.lean:72:0: 'Dovetail.Predictor.resetChain3_nonDistrib_agent' depends on axioms: [propext, Classical.choice, Quot.sound]
✔ [8597/8598] Built DovetailProofs (80s)
Build completed successfully (8598 jobs).
```

Zero errors. The only warnings are Mathlib style linters enabled by the lakefile (missing
copyright header, `show` used where `change` is preferred); the pre-existing `Descent.lean` and
`Saturation.lean` raise the same header warning.

## Axioms

Every `#print axioms` in the modules reports a subset of
`[propext, Classical.choice, Quot.sound]`, including: `descent_run`,
`ExactAgent.predictor_quotient`, `ExactAgent.exists_Phi`, `canonicalAgent`,
`StochLang.support_quotient`, `StochLang.exists_suppHom`, `StochLang.Ssupp_trivial_iff`,
`ExactAgent.kappa_le_kappa'`, `StochLang.tau_eq_iff_synEq`, `synMonoidEquiv`,
`sigma_eq_iff_synEq`, `synMonoidSuppEquiv`, `synEq_nu_iff`, `ExactAgent.transport_subgroup`,
`transport_divides`, `transport_aperiodic`, `aperiodic_iff_exists_agent`, `coin_Sp_isSubgroup`,
`coin_Sp_card`, `historyAgent`, `historyAgent_subgroup_trivial`,
`transport_fails_without_finiteness`, `rank_bound`, `range_run_inter_live`,
`exists_perm_rep_of_subgroup`, `Reset.conEquiv`, `Reset.exists_isM3`, `Reset.isM3_fin3`,
`conIciEquiv`, `comapCon_sup`, `ExactAgent.intervalEquiv`, `nonDistrib_of_Sp`,
`MarkovChain.resetEquiv`, `conSpEquiv`, `nonDistrib_con_SA`, `resetChain3_isM3`,
`StochLang.linear_quotient`, `linRun_eqOn_iff`, `Lam_append`, `Lam_eq_iff`.
(`Reset.one_class`, `conIciEquiv`, `comapCon_sup` use only `propext`, `Quot.sound`.)

## Gaps or errors found in the paper

None in the formalised results. Minor observations, none affecting correctness:

1. Lemma `lem:descent` and everything built on it never use finiteness of the alphabet.
2. Thm `thm:transport` (ii) and the "in particular" of (i) need no finiteness of `S_A`; only the
   subgroup-lifting statement of (i) does (and `transport_fails_without_finiteness` confirms it
   cannot be dropped there).
3. Prop `prop:markov-reset-general` does not need `q_ε` to differ from every `g_i` (the text
   before it argues this for the 3-symbol chain; the proof of the proposition does not use it,
   and neither does the Lean).
4. The complexity section (Thm `thm:pred-complexity`, including the perfect-subgroup length
   argument in (iii)) was read and checked by hand only; no gap was seen, but it is not
   machine-checked.

## Next steps, in order

1. Bundle `Λ : S_lin →* 𝒩 ⋊ S_p` as a `MonoidHom` with the ray action, to state Thm
   `thm:semidirect` exactly as written.
2. Lemma `lem:syntactic` (iii): construct the embedding `M(ν) ↪ ∏ M(K_x)`.
3. The purely algebraic step of Thm `thm:pred-complexity` (iii): a perfect subgroup of `S_p`
   lies in `τ(O^t)` for one `t`.
4. Finite monoids: "all subgroups trivial ⇒ `∀ s ∃ n, sⁿ = sⁿ⁺¹`", to state (ii) in the paper's
   primary form.
5. Group complexity and circuit classes would need new Mathlib-scale developments; not planned.
