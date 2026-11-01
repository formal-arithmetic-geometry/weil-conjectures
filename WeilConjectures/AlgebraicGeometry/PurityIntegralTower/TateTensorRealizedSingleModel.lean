/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityIntegralTower.TateTensorRealizedTransition
public import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroAdjoint

/-! Transport of a shifted single scalar insertion through exact coefficient presentations.

Source: Stacks 03D2, 06YY, 07A6; smooth-purity transport, normalized Tate tower, Step 4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

/-- The specified single model through comparison inverse image and realization.
Source: normalized Tate tower, exact finite single models.
(blueprint: lem-pur-tate-tensor-realized-single-model) -/
def realizedShiftModel (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ) (k : ℤ)
    {K : Etale.DerivedCategoryModule (coefficient ell (n + 1)) T}
    {M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (coefficient ell (n + 1)))}
    (e : K ≅ ((_root_.DerivedCategory.singleFunctor _ 0).obj M)⟦k⟧) :
    (derivedRealization T ell n).obj
        ((comparison (coefficient ell (n + 1)) T).obj K) ≅
      (_root_.DerivedCategory.singleFunctor _ (-k)).obj
        ((realization T ell n).obj
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} _) T).obj M)) :=
  (derivedRealization T ell n).mapIso
      ((comparison (coefficient ell (n + 1)) T).mapIso e ≪≫
        ((comparison (coefficient ell (n + 1)) T).commShiftIso k).app _ ≪≫
        (shiftFunctor _ k).mapIso
          ((Functor.mapDerivedCategorySingleFunctor
            (ProEtale.comparisonUpperStar
              (ModuleCat.{u + 1} (coefficient ell (n + 1))) T) 0).app _)) ≪≫
    ((derivedRealization T ell n).commShiftIso k).app _ ≪≫
    (shiftFunctor _ k).mapIso
      (((realization T ell n).mapDerivedCategorySingleFunctor 0).app _) ≪≫
    ((_root_.DerivedCategory.singleFunctors _).shiftIso k (-k) 0 (by omega)).app _

/-- An arbitrary ordinary semilinear map, inserted by the scalar adjunction and
shifted, retains its single model through site comparison, finite realization,
and restriction to completed coefficients. The etale objects and their models
are arbitrary; this assertion contains no roots, root powers or tensor products.

Source: Stacks 03D2, 06YY, 07A6; normalized Tate tower, exact scalar-mate transport.
(blueprint: lem-pur-tate-tensor-realized-single-model).

Proof: transpose the scalarComparisonMap using unit_mateEquiv_symm. Its adjunct
is realization of the old scalar adjunct followed by derivedRestrictionComparison.
Transpose pbcComparisonReduction in the same way; the underlying restriction
comparison is the exact descent of pbcComparisonRestrict. Naturality moves the
two model isomorphisms through these comparisons. Apply the exact/single
naturality formula to the localized restriction natural transformations and the
composition formulas to the exact functor comparisons. The scalarShiftIso is
the adjunction mate of the exact restriction's shift, so the shifted insertion
has the same adjunct as the shifted single image of the ordinary map. The
additive singleFunctors.shiftIso identifies this with the single in degree -k.
The resulting ordinary map is comparison inverse image of f, followed by
pbcComparisonRestrict.inv, realization, restrictionComparison.hom, and the
restriction-composition isomorphism. This is exactly realizedSemilinear.
Finally use injectivity of the scalar-adjunction Hom equivalences and naturality
of the exact restriction/single comparison to obtain the displayed equation.
No flatness or invertibility of f or of the scalar-extension map is required. -/
theorem realizedSemilinear_derived
    (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (b a : ℕ) (hab : a ≤ b) (k : ℤ)
    {K : Etale.DerivedCategoryModule (coefficient ell (b + 1)) T}
    {L : Etale.DerivedCategoryModule (coefficient ell (a + 1)) T}
    {M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (coefficient ell (b + 1)))}
    {N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (coefficient ell (a + 1)))}
    (eK : K ≅ ((_root_.DerivedCategory.singleFunctor _ 0).obj M)⟦k⟧)
    (eL : L ≅ ((_root_.DerivedCategory.singleFunctor _ 0).obj N)⟦k⟧)
    (g : (ordinaryScalar
      (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1)) T).obj K ⟶ L)
    (f : M ⟶ (Sheaf.restrictScalars T.smallEtaleTopology
      (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1))).obj N)
    (hg : g ≫ eL.hom =
      (ordinaryScalar (FiniteReduction.quotient ell (Nat.add_le_add_right hab 1)) T).map
          eK.hom ≫
        (scalarShiftIso (FiniteReduction.quotient ell (Nat.add_le_add_right hab 1)) T k).hom.app
          _ ≫
        (shiftFunctor _ k).map
          (SheafExactDegreeZero.scalarAdjointInsertion T.smallEtaleTopology
            (FiniteReduction.quotient ell (Nat.add_le_add_right hab 1)) f)) :
    (pbcDerivedRestrict (pbcAdicProjection T (datum.{u} ell) b)).map
        ((pbcDerivedScalarAdjunction (pbcAdicQuotient T (datum.{u} ell) b a hab)).homEquiv
          _ _ ((scalarComparison T ell b a hab).hom.app
              ((comparison (coefficient ell (b + 1)) T).obj K) ≫
            (derivedRealization T ell a).map
              ((ProEtale.pbcComparisonReduction T
                (FiniteReduction.quotient ell (Nat.add_le_add_right hab 1))).hom.app K ≫
                  (comparison (coefficient ell (a + 1)) T).map g))) ≫
      (pbcDerivedRestrictComp (pbcAdicProjection T (datum.{u} ell) b)
        (pbcAdicQuotient T (datum.{u} ell) b a hab)
        (pbcAdicProjection T (datum.{u} ell) a)
        (pbcAdicProjection_comp T (datum.{u} ell) b a hab)).hom.app _ ≫
      (pbcDerivedRestrict (pbcAdicProjection T (datum.{u} ell) a)).map
        (realizedShiftModel T ell a k eL).hom ≫
      (Functor.mapDerivedCategorySingleFunctor
        (pbcRestrict (pbcAdicProjection T (datum.{u} ell) a)) (-k)).hom.app _ =
    (pbcDerivedRestrict (pbcAdicProjection T (datum.{u} ell) b)).map
        (realizedShiftModel T ell b k eK).hom ≫
      (Functor.mapDerivedCategorySingleFunctor
        (pbcRestrict (pbcAdicProjection T (datum.{u} ell) b)) (-k)).hom.app _ ≫
      (_root_.DerivedCategory.singleFunctor _ (-k)).map
        (realizedSemilinear T ell b a hab f) := by sorry

end AlgebraicGeometry.Scheme.PurityIntegralTower
