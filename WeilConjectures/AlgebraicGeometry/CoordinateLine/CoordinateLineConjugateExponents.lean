/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineAdjunctionMaps
import WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineConjugateExponentsLe
import WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineConjugateExponentsGe
import WeilConjectures.SmoothPurity.Supporting.CoordinateLineConjugateExponentsReverse

/-! # Exponent compatibility before the site-unit map

Source: current blueprint, sk-prop-an, coordinate-line proof
(blueprint: lem-pur-coordinate-line-conjugate-exponents).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CoordinateLine
open AffineLinePurity VectorIntegrationSite

set_option maxHeartbeats 800000 in
-- The source-comparison rewrite expands several irreducible comparison layers.
/-- Canonical Tate exponent transitions preserve the realized ordinary conjugate.
Source: current blueprint, independence of the annihilating exponent in the final
paragraph of cor-pur-affine-space-zero-section-purity.proof.md
(blueprint: lem-pur-coordinate-line-conjugate-exponents).

Proof: first take r≤r'. Root projection fixes the supported Kummer boundary and
the shifted twisted unit, so it fixes both components of the projective decomposition.
It therefore commutes with its inverse and normalized trace. Restrict by the open
counit and use projection naturality. The resulting square identifies the actual
ordinary composite counits in their canonical Tate coordinates. Transpose under
the fixed Brown adjunction; its Hom bijection is injective and the adjunct of the
actual counit is the conjugate comparison. Exact site comparison preserves this
square. Its tensor/pullback comparison commutes with the same exponent transition,
so conjugating by the sourceComparison maps gives the displayed equality.
The coefficient transition is the composite through the specified inverse-limit
Tate line, characterized by root projection; no generator or orientation is chosen.
For arbitrary r and r' apply the ordered result twice through max r r' and cancel
the common isomorphism. Proof irrelevance identifies all unit witnesses. This also
covers equal exponents, the zero ring, and the empty base. -/
theorem coordinate_line_conjugate_exponents
    (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT] [IsNoetherian T]
    (r r' : ℕ)
    (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)
    (hA' : ((P.coefficients.l ^ (r' + 1) : ℕ) : Ring P) = 0)
    (hP : IsUnit (P.coefficients.l : Γ(ProjectiveLine T, ⊤)))
    (hX : IsUnit (P.coefficients.l : Γ(AffineSpace PUnit.{u + 1} T, ⊤)))
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Ring P))))
    (Ke : Etale.DerivedCategoryModule (Ring P) T)
    (hKe : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Ring P)) T Ke)
    (eK : (VectorIntegrationSite.comparison (Ring P) T).obj Ke ≅ K.obj) :
    (tensorCoefficientIso (Ring P) T _ _
      (coefficientTwistIso P.coefficients.l P.extension (P.level - 1) T r hA hP hX ≪≫
        (coefficientTwistIso P.coefficients.l P.extension (P.level - 1) T r' hA' hP hX).symm)
      K.obj).hom ≫
    (sourceComparison P.coefficients.l P.extension (P.level - 1) T r' hA' K.obj Ke eK).inv ≫
    (VectorIntegrationSite.comparison (Ring P) (AffineSpace PUnit.{u + 1} T)).map
      ((sourceCoordinates P T r' hA' Ke).hom ≫
        (comparison (Ring P) (P.coefficients.l ^ (r' + 1)) hA' T
          (pow_pos (Fact.out : P.coefficients.l.Prime).pos _)
          (by simpa only [Nat.cast_pow] using (primeUnit P T aT).pow (r' + 1))).hom.app Ke) =
    (sourceComparison P.coefficients.l P.extension (P.level - 1) T r hA K.obj Ke eK).inv ≫
    (VectorIntegrationSite.comparison (Ring P) (AffineSpace PUnit.{u + 1} T)).map
      ((sourceCoordinates P T r hA Ke).hom ≫
        (comparison (Ring P) (P.coefficients.l ^ (r + 1)) hA T
          (pow_pos (Fact.out : P.coefficients.l.Prime).pos _)
          (by simpa only [Nat.cast_pow] using (primeUnit P T aT).pow (r + 1))).hom.app Ke) := by
  have hs := coordinate_line_source_comparison_naturality P T aT r r' hA hA' hP hX
    K Ke hKe eK
  have ho := coordinate_line_ordinary_conjugate_transport P T aT r r' hA hA' hP hX
    K Ke hKe eK
  by_cases h : r ≤ r'
  · rw [← Category.assoc, hs]
    rw [Category.assoc, ← (VectorIntegrationSite.comparison
      (Ring P) (AffineSpace PUnit.{u + 1} T)).map_comp]
    rw [ho]
  · let q := coordinate_line_ordinary_source_transition P T aT r r' hA hA' Ke
    let F := VectorIntegrationSite.comparison (Ring P) (AffineSpace PUnit.{u + 1} T)
    let u := F.map ((sourceCoordinates P T r' hA' Ke).hom ≫
      (comparison (Ring P) (P.coefficients.l ^ (r' + 1)) hA' T
        (pow_pos (Fact.out : P.coefficients.l.Prime).pos _)
        (by simpa only [Nat.cast_pow] using (primeUnit P T aT).pow (r' + 1))).hom.app Ke)
    let v := F.map ((sourceCoordinates P T r hA Ke).hom ≫
      (comparison (Ring P) (P.coefficients.l ^ (r + 1)) hA T
        (pow_pos (Fact.out : P.coefficients.l.Prime).pos _)
        (by simpa only [Nat.cast_pow] using (primeUnit P T aT).pow (r + 1))).hom.app Ke)
    have hoIso : (F.mapIso q).hom ≫ u = v := by
      simpa [q, F, u, v] using ho
    have hrev : (F.mapIso q).symm.hom ≫ v = u := by
      apply coordinate_line_reverse_from_ordered (e := F.mapIso q)
      exact hoIso
    have hback : (F.mapIso q).symm.symm.hom ≫ u = v := by
      apply coordinate_line_reverse_from_ordered (e := (F.mapIso q).symm)
      exact hrev
    have ho' : (F.mapIso q).symm.symm.hom ≫ u = v := hback
    rw [← Category.assoc, hs]
    rw [Category.assoc, ← (VectorIntegrationSite.comparison
      (Ring P) (AffineSpace PUnit.{u + 1} T)).map_comp]
    simpa [q, F, u, v] using ho'

end AlgebraicGeometry.ProEtale.CoordinateLine
