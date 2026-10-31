/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleProjectiveLineTraceSupplement

import all WeilConjectures.AlgebraicGeometry.ProEtaleProjectiveLineTraceSupplement

/-! # Comparison of ordinary and supported projective-line decompositions

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
lem-amb-affine-space-top-trace.proof.md, first (d = 1) paragraph, lines 19--24:
the projective decomposition before open restriction; Stacks 0B65 for the mate.
(blueprint: lem-route-line-projective-decomposition-comparison)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite

/-- The comparison of the ordinary and supported projective-line decompositions:
if the supported Chern arrow `χ = projectiveChern` is the comparison image of the actual
ordinary Chern arrow `D.chern` of `D = Etale.projectiveLineTraceDatum`, then
`β_{W_e} ∘ C_T(b_q) = b^p ∘ σ_T`.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
lem-amb-affine-space-top-trace.proof.md, first d = 1 paragraph, lines 19--24;
Stacks 0B65 (categories.tex, lemma-transformation-between-functors-and-adjoints).
(blueprint: lem-route-line-projective-decomposition-comparison)

Coordinates. `line l E n r hA T` is `C_T(A_T^et(1)[2])`, and `τ_T[2] = twistDerived … 1 2`
identifies it with `A_T(1)[2]`. The recorded `projectiveB = [projectiveU, projectiveH]`
(def-pur-supported-projective-site-arrows) has first summand in these comparison
coordinates, so the node's `b^p` is `projectiveB ∘ (τ_T[2]⁻¹ ⊕ 1)` and
`b^p ∘ σ_T = projectiveB`. The right side `geoP1TwistedMap` is
`geoP1SumComparison ≫ C_T(D.decomposition.hom) ≫ geoP1PushComparison`, i.e.
`β_{W_e} ∘ C_T(b_q)` after the canonical additive identification
`C_T B ⊞ C_T A_T → C_T(B ⊞ A_T)` given by `C_T` of the two inclusions.
The hypothesis `hχ` is the node's `χ = C_P(D.chern)`.

Proof (node steps):
1. Adjoint transpose under the comparison (Stacks 0B65): for `l ⊣ R`, `p ⊣ S`, comparison
   functors `C = C_T`, `F = C_P` and the pull comparison `a : C ⋙ p ≅ l ⋙ F`, the proved
   helper `compare_adjunct` gives `C(Φ_e f) ≫ β = Φ_p(a_X ≫ F f)`, where
   `β = geoP1PushComparison` is defined as exactly this transpose. No qcqs hypothesis or
   invertibility of `β` is used.
2. The first component is the proved helper `unit_comparison`: `line` is already
   `C_T(A^et(1)[2])` and `projectiveU` is defined as the transpose of `a` followed by
   `C_P` of the actual shifted line pullback of `projectiveLineTraceTransport`, so step 1
   gives `C_T(u_e) ≫ β = projectiveU`.
3. For the Chern component apply `compare_adjunct` to `ordinaryFiniteUnitPullback.hom ≫ c`
   with `c = D.chern`; unfold `projectiveH`, rewrite `projectiveChern = C_P(c)` by `hχ`,
   and `pullbackUnit = geoP1UnitPullback` (pull comparison then `C_P` of the ordinary
   constant pullback), `Functor.map_comp` and associativity give
   `C_T(h) ≫ β = projectiveH`.
4. Rewrite `D.decomposition.hom = desc(u_e, h)` by `decomposition_hom`; the proved helper
   `compared_desc_total` (precomposition with the two inclusions, functoriality of `C_T`,
   biproduct extensionality) assembles steps 2 and 3 into
   `projectiveB = geoP1TwistedMap`.
-/
theorem projectiveLineDecompositionComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤)))
    (hI : (ProjectiveLine.infinity S).ker.IsInvertible) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hχ : projectiveChern l E n S hS hI r hA =
      (comparison (Scheme.finiteTateCoefficient l E n) (ProjectiveLine S)).map
        (Etale.projectiveLineTraceDatum (l ^ (r + 1))
          (pow_pos (Fact.out : l.Prime).pos _) _ hA S
          (by simpa only [Nat.cast_pow] using hS.pow (r + 1))).chern) :
    projectiveB l E n S hS hI r hA =
      geoP1TwistedMap (Scheme.finiteTateCoefficient l E n) (l ^ (r + 1))
        (pow_pos (Fact.out : l.Prime).pos _) hA S
        (by simpa only [Nat.cast_pow] using hS.pow (r + 1)) := by
  unfold projectiveB geoP1TwistedMap
  rw [(Etale.projectiveLineTraceDatum (l ^ (r + 1))
    (pow_pos (Fact.out : l.Prime).pos _) (Scheme.finiteTateCoefficient l E n) hA S
    (by simpa only [Nat.cast_pow] using hS.pow (r + 1))).decomposition_hom]
  apply compared_desc_total (geoP1Comparison (Scheme.finiteTateCoefficient l E n) S)
    _ _ _ _ _ (unit_comparison l E n S hS r hA)
  let A := Scheme.finiteTateCoefficient l E n
  let q := ProjectiveLine S ↘ S
  let c := (Etale.projectiveLineTraceDatum (l ^ (r + 1))
    (pow_pos (Fact.out : l.Prime).pos _) A hA S
    (by simpa only [Nat.cast_pow] using hS.pow (r + 1))).chern
  have hh := compare_adjunct (comparison A S) (comparison A (ProjectiveLine S))
    (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) q)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) q)
    (geoP1PullComparison A q) ((Etale.ordinaryFiniteUnitPullback A q).hom ≫ c)
  unfold projectiveH
  rw [hχ]
  simpa only [Etale.ordinaryFiniteP1ChernPushforward, pullbackUnit, geoP1UnitPullback,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc,
    geoP1PushComparison, comparison, geoP1Comparison, geoP1Pushforward,
    Etale.ordinaryFinitePushforward, line, unit, Functor.id_obj] using hh

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
