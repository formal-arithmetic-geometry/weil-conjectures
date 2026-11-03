/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Vector.VectorPurityScalarSingle
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackIsoExistence

/-! # The scalar adjunct on a flat object in degree zero

Source: current blueprint, sk-prop-sp-rational-adjunction, passage from ordinary
Tate lines to their derived scalar comparisons
(blueprint: lem-sp-derived-flat-scalar-single).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- The specified adjunction transpose on a flat sheaf is invertible.
Source: Stacks 07A4 and the Tate-line scalar step of sk-prop-sp-rational-adjunction.
Proof: a single complex on a flat object is K-flat: its degree-zero term is flat
and all other terms vanish. The existing single-adjunct formula identifies the
map with the left-derived representative comparison on this complex, followed
by the single-complex isomorphism. That representative comparison is invertible
on K-flat complexes. This also holds for zero objects.
(blueprint: lem-sp-derived-flat-scalar-single). -/
theorem isIso_flatSingle_adjunct
    {C : Type v} {D : Type w} [Category.{u + 1} C] [Category.{u + 1} D]
    [Abelian C] [Abelian D] [IsGrothendieckAbelian.{u + 1} C]
    [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    (E : C ⥤ D) (U : D ⥤ C) [E.Additive] [U.Additive] [E.PreservesKFlatQuasiIso]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (a : E ⊣ U) {L : DerivedCategory C ⥤ DerivedCategory D}
    (ad : L ⊣ U.mapDerivedCategory) (M : C) (hM : ObjectProperty.flat M) :
    IsIso ((ad.homEquiv _ _).symm
      ((DerivedCategory.singleFunctor C 0).map (a.unit.app M) ≫
        (U.mapDerivedCategorySingleFunctor 0).inv.app (E.obj M))) := by
  let P := (CochainComplex.singleFunctor C 0).obj M
  have hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P := by
    apply CochainComplex.kFlat_of_isStrictlyLE_of_flat P 0
    intro n
    by_cases hn : n = 0
    · subst n
      exact ObjectProperty.prop_of_iso _
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).symm hM
    · exact ObjectProperty.flat_of_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M n hn)
  change IsIso (WeilConjectures.PurityFiniteSetting.purityAdjunctionSingleMap E U L
    U.mapDerivedCategory (DerivedCategory.singleFunctor C 0)
    (DerivedCategory.singleFunctor D 0) a ad (U.mapDerivedCategorySingleFunctor 0) M)
  rw [purityAdjunctionSingleMap_eq_representative]
  unfold WeilConjectures.PurityFiniteSetting.purityRepresentativeSingleMap
    WeilConjectures.PurityFiniteSetting.puritySingleFromRepresentativeMap
  have hi := AlgebraicGeometry.Etale.derivedRepresentative_isIso E U a ad P hP
  change IsIso (AlgebraicGeometry.Etale.scalarAdjunctionRepresentativeMap E U a L ad P) at hi
  infer_instance

end CategoryTheory
