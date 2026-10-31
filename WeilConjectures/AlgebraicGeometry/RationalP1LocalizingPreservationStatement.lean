/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1LocalizingPreservation

/-! # Rational projective-line localizing preservation, current route

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-p1-adjunction-rational/
sk-prop-p1-adjunction-rational-unit-counit.proof.md, Well-definedness (1)--(3): the
localizing domains, proper base change and projection-formula hypotheses for the unit and
counit (blueprint: lem-sfb-rational-p1-localizing-preservation).

Stated anew after the 2026-10-31 re-anchor, which withdrew the attachment to
`localizingPreservationChecks` because its proof follows the removed closure-equality route
(`localizingClosure_ctf_equals_bc`, blueprint id det-def-localizing-closure-ctf-equals-bc).
The clause-grouping structures `ProjectiveLineLocalizingChecks`,
`ProjectiveLineLocalizingGeometry`, `ProjectiveLineLocalizingObjectChecks` and
`LocalizingFunctorChecks` are reused unchanged.

## Main statements

- `localizingPreservationChecks_current`: the full localizing-preservation assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

/-- For distinct primes `ℓ ≠ p`, a field `k` of characteristic `p`, a separated finite-type
`k`-scheme `Y` and `Λ = E` (`c = some E`) or the finite-subextension-valued `Q̄_ℓ`
(`c = none`): `Y`, `P = P¹_Y`, `W = P ×_Y P` are Noetherian and qcqs, `q, p₁, p₂, Δ` are
proper, `Δ` is closed with quasi-compact open complement, `ℓ` is a unit on every residue
field, the standing structure maps are separated of finite type; pullback and proper
pushforward along `q, p₁, p₂, Δ` preserve `𝓛 = Loc(Dbc)` and restrict to exact functors;
the unit and `L_Z = Λ_Z(1)` lie in `Dbc(Z, Λ)`, `𝓛_Z` is tensor-closed and
`T_Z = (- ⊗ L_Z)[2]` restricts exactly; hence `Rq_*` and `T_P q^*` are exact functors between
the `𝓛`. Source: blueprint `sk-prop-p1-adjunction-rational-unit-counit.proof.md`,
Well-definedness (1)--(3) (blueprint: lem-sfb-rational-p1-localizing-preservation).

Proof.
1. `q : P = P({0,1}; Y) → Y` is proper (lemma-nagata-projective-space-base-change-proper);
   `p₁, p₂` are proper as base changes (lem-weil-pbc-proper-fp-permanence (b)); `q` is
   separated (def-weil-proper-morphism), so `Δ` is a closed immersion, hence proper.
   `Spec k` is Noetherian, so `Y, P, W` are Noetherian (lem-weil-pbc-finite-type-over-
   noetherian), quasi-compact and quasi-separated
   (lem-weil-pbc-locally-noetherian-quasi-separated). For affine `V ⊆ W`,
   `V \ Δ(P)` is Noetherian (lem-weil-pbc-noetherian-open-subscheme-noetherian), so `j` is
   quasi-compact (def-weil-finite-type-morphism) and of finite type
   (lem-weil-pbc-qc-open-immersion-finite-type); composites give the standing separated
   finite-type structure maps. `ℓ ≠ p = char k` makes `ℓ` a unit in every residue field.
2. The pulled-back condensed coefficient and Tate systems are identified along every
   morphism (sk-prop-sfb-cartesian-coefficients) and module inverse image is exact.
3. For `Z ∈ {Y, P, W}` (qcqs by step 1), clause 2 of lem-integral-ctf-equals-bc gives
   `Dctf(Z, Λ) = Dbc(Z, Λ)`, so `𝓛_Z = Loc(Dctf(Z, Λ))`. For `g ∈ {q, p₁, p₂, Δ}`,
   det-proper-base-change-unbounded-pullback makes `g^*` exact and preserving these closures;
   `g` is proper and the last paragraph of det-proper-image-localizing-proper gives the same
   for `Rg_*` with `Λ = E, Q̄_ℓ`. The restrictions are exact for the inherited triangulated
   structures (det-def-localizing-closure-existence, def-weil-triangulated-subcategory).
4. The unit is constructible with the one-stratum model `Λ(*)` (sk-def-sfb-constructible);
   `L_Z` is bounded constructible (lem-sfb-rational-p1-positive-line-constructible). Tensor
   closure is clause 2 of det-thm-sf-pf-field-tensor, and `𝓛_Z` is closed under `[2]`, so
   `T_Z` preserves `𝓛_Z`; `- ⊗ L_Z` is triangulated
   (lem-weil-pbc-ringed-projection-tensor-exact), so `T_Z` and its restriction are exact.
5. Specialize step 3 to `q, p₁, p₂, Δ` and step 4 to `Y, P, W`; `T_P q^*` is the composite
   of the exact restrictions `q^*` and `T_P`, and `Rq_*` is the restriction of step 3. -/
theorem localizingPreservationChecks_current
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] :
    ProjectiveLineLocalizingChecks l c (k := k) Y := by
  sorry

end AlgebraicGeometry.ProEtale.RationalP1
