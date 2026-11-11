import DovetailProofs.Predictor.Agent
import DovetailProofs.Predictor.Semigroup

/-!
# Transport to finite predictors

Formalises Theorem `thm:transport` of `Lattice/main.tex` (l.806), parts (i) and (ii), and the
formalisable part of Remark `rem:tight` (l.844).

Part (iii), `c(S_p) ≤ c(S_A)` for the Krohn–Rhodes group complexity `c`, is **not formalised**:
Mathlib has neither wreath products of transformation monoids, nor the Krohn–Rhodes theorem,
nor group complexity.
-/

namespace Dovetail.Predictor

open Function

universe u

namespace ExactAgent

variable {O : Type*} [Fintype O] {P : StochLang O} {Q : Type*} (A : ExactAgent P Q)

/-- The update monoid is finite whenever `Q` is finite (Theorem `thm:transport`, main.tex
l.809). -/
theorem SA_finite_of_finite [Finite Q] : Finite A.SA := by
  haveI : Finite (Function.End Q) := inferInstanceAs (Finite (Q → Q))
  exact Finite.of_injective (fun s : A.SA => (s : Function.End Q)) Subtype.val_injective

/-- **Theorem `thm:transport`, first claim** (main.tex l.809): if `S_A` is finite then `S_p` is
finite. -/
theorem Sp_finite [Finite A.SA] : Finite P.Sp :=
  Finite.of_surjective A.Phi A.Phi_surjective

/-- **Theorem `thm:transport`(i)** (main.tex l.812): if `S_A` is finite, then for every subgroup
`G ⊆ S_p` there is a subgroup `H ⊆ S_A` with `Φ(H) = G`. -/
theorem transport_subgroup [Finite A.SA] {G : Set P.Sp} (hG : IsSubgroup G) :
    ∃ H : Set A.SA, IsSubgroup H ∧ A.Phi '' H = G :=
  exists_subgroup_image_eq (MonoidHom.toMulHom A.Phi) hG fun g _ => A.Phi_surjective g

/-- **Theorem `thm:transport`(i), "in particular"** (main.tex l.814): every monoid (in particular
every group) that divides `S_p` divides `S_A`.  As the paper's proof says, this is transitivity
of division; no finiteness is needed. -/
theorem transport_divides {T : Type*} [Monoid T] (h : Divides T P.Sp) : Divides T A.SA :=
  h.trans (Divides.of_surjective A.Phi A.Phi_surjective)

/-- `S_p` divides `S_A` (Corollary `cor:quotient`, main.tex l.470). -/
theorem Sp_divides : Divides P.Sp A.SA := Divides.of_surjective A.Phi A.Phi_surjective

/-- **Theorem `thm:transport`(ii)** (main.tex l.815): if `S_A` is aperiodic then `S_p` is
aperiodic.  (Aperiodicity in the equational form `∀ s ∃ n, sⁿ = sⁿ⁺¹`; the proof needs no
finiteness.) -/
theorem transport_aperiodic (h : IsAperiodic A.SA) : IsAperiodic P.Sp :=
  h.of_surjective A.Phi A.Phi_surjective

end ExactAgent

/-- **Remark `rem:tight`, aperiodic half** (main.tex l.849): `S_p` is aperiodic if and only if
some reachable exact predictive agent has an aperiodic update monoid.  (The paper restricts to
finite predictors when `X_p` is finite; the canonical machine is the witness in either case and
is finite exactly when `X_p` is.) -/
theorem aperiodic_iff_exists_agent {O : Type u} [Fintype O] (P : StochLang O) :
    IsAperiodic P.Sp ↔ ∃ (Q : Type u) (A : ExactAgent P Q), IsAperiodic A.SA :=
  ⟨fun h => ⟨Option P.X, canonicalAgent P, h⟩, fun ⟨_, A, h⟩ => A.transport_aperiodic h⟩

end Dovetail.Predictor

#print axioms Dovetail.Predictor.ExactAgent.transport_subgroup
#print axioms Dovetail.Predictor.ExactAgent.transport_divides
#print axioms Dovetail.Predictor.ExactAgent.transport_aperiodic
#print axioms Dovetail.Predictor.aperiodic_iff_exists_agent
