/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.CategoryTheory.NativeDerivedHomSignedExact
public import Sheaf.Algebra.Homology.ExactClosedDerivedHom

/-! # Signed shift compatibility of exact derived closed comparisons

Source: Stacks Project, Tags 08J9, 08JC and 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u c d
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite
open AlgebraicGeometry.ProEtale

namespace CategoryTheory.Functor


/-- The evaluation transpose of an exact derived monoidal functor respects the signed
contravariant source shifts. This asserts a shift square only, not exactness or thick closure.
Source: Stacks Project, Tags 08J9 and 08JC; steps 2--4 of the site comparison argument
(blueprint: lem-sf-exact-derived-hom-comparison-shift).

Proof: choose a K-injective representative I of M and a K-injective replacement
q:FI -> J. The ordinary map F Hom(E,I) -> Hom(FE,FI) -> Hom(FE,J) is natural in E.
Use a K-flat resolution of E and a K-flat resolution of Hom(E,I). On each tensor
summand, uncurrying this composite is q after pulled-back evaluation. Thus its
localization is the stated canonical closedComparison, for the transported derived
monoidal structure. For E[m], signed reindexing multiplies degree k by (-1)^(m*k).
Ordinary pullback preserves this scalar and postcomposition with q preserves it,
so both routes around the raw shift square agree on every Hom projection. Localize
and use the K-flat representative comparison to identify the raw shifts with the
adjoint mates siteHomOppositeSourceShift. Multiply both rows by the same scalar
(-1)^(n*(n+1)/2). The two supplied normalizations therefore give precisely the
CommShift square. No preservation of K-injectives by F is used. -/
theorem exactDerivedHomComparison_shift
    {C : Type c} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {D : Type d} [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D]
    [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal] (M : DerivedCategory C)
    (sC : (MonoidalClosed.internalHom.flip.obj M).CommShift ℤ)
    (sD : (MonoidalClosed.internalHom.flip.obj (F.mapDerivedCategory.obj M)).CommShift ℤ)
    (hC : letI := sC; ∀ (K : DerivedCategory C) (n : ℤ),
      ((MonoidalClosed.internalHom.flip.obj M).commShiftIso n).hom.app (op K) =
        (n * (n + 1) / 2).negOnePow • (siteHomOppositeSourceShift K n).hom.app M)
    (hD : letI := sD; ∀ (K : DerivedCategory D) (n : ℤ),
      ((MonoidalClosed.internalHom.flip.obj (F.mapDerivedCategory.obj M)).commShiftIso n).hom.app
          (op K) = (n * (n + 1) / 2).negOnePow •
            (siteHomOppositeSourceShift K n).hom.app (F.mapDerivedCategory.obj M)) :
    letI := sC
    letI := sD
    letI := exactClosedDerivedMonoidal F
    ∀ β : MonoidalClosed.internalHom.flip.obj M ⋙ F.mapDerivedCategory ⟶
      F.mapDerivedCategory.op ⋙ MonoidalClosed.internalHom.flip.obj (F.mapDerivedCategory.obj M),
      (∀ K, β.app (op K) = closedComparison F.mapDerivedCategory K M) →
        NatTrans.CommShift β ℤ := by sorry

end CategoryTheory.Functor
