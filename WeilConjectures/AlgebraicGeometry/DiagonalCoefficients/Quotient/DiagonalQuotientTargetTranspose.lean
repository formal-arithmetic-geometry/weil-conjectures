/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.FiniteRealization.DiagonalRootRouteInsertions
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerSquareData.DiagonalQuotientEndpointTranspose
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarEndpointsTranspose

/-! # The successive target endpoint under its actual adjunction
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local instance 100000] sheafIsAbelian
attribute [local instance 200000] AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
attribute [local instance 300000] CommRing.toRing
attribute [local instance 400000] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] derivedScalars quotientLine cyclicLine
  Functor.mapDerivedCategory Functor.mapDerivedCategorySingleFunctor
  DerivedCategory.singleFunctors HomotopyCategory.singleFunctors HasDerivedCategory.standard
  DerivedCategory HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.singleFunctorIsoCompQ
  CondensedRing.lowerStar Profinite.continuousMapRingSheaf
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
  UniformizerSquareData.inverse_additive

private theorem homEquiv_shift
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F : C ⥤ D} {R : D ⥤ C} [F.CommShift ℤ] [R.CommShift ℤ]
    (a : F ⊣ R) [a.CommShift ℤ] {M : C} {N : D} (f : F.obj M ⟶ N) (k : ℤ) :
    a.homEquiv _ _ ((F.commShiftIso k).hom.app M ≫ f⟦k⟧') =
      (a.homEquiv _ _ f)⟦k⟧' ≫ (R.commShiftIso k).inv.app N := by
  have h : (a.homEquiv _ _ f)⟦k⟧' =
      a.homEquiv _ _ ((F.commShiftIso k).hom.app M ≫ f⟦k⟧') ≫
        (R.commShiftIso k).hom.app N := by
    simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
    rw [a.shift_unit_app]
    simp only [Category.assoc]
    rw [Functor.commShiftIso_hom_naturality]
  exact ((R.commShiftIso k).app N).eq_comp_inv.mpr h.symm

namespace UniformizerSquareData

/-- The degree-two endpoint is the shifted degree-zero endpoint. -/
private theorem quotientTarget_shift
    {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
    {E : PadicAlgCl.FiniteIntermediateField l} {π : PadicAlgCl.integers l E} {n : ℕ}
    {A : Type (u + 1)} [CommRing A] {hA : ((l ^ (n + 1) : ℕ) : A) = 0}
    (q : UniformizerSquareData l Y E π n A hA) :
    finiteTargetMap q.eW
      (ScalarCompatibility.compositeTarget q.route.first q.route.second)
      q.lineW.endpoint.iso =
      (((ScalarCompatibility.compositeFunctor q.route.first q.route.second) ⋙
        q.eW.F.mapDerivedCategory).commShiftIso (2 : ℤ)).hom.app _ ≫
      (quotientEndpointZero q)⟦(2 : ℤ)⟧' := by
  unfold quotientEndpointZero
  exact scalarRealizedEndpoints_shift q.route.first q.route.second q.eW
    q.lineW.endpoint.iso

end UniformizerSquareData

attribute [local semireducible] UniformizerSquareData.quotientAdjunction
  UniformizerSquareData.quotientEndpoints

/-- The successive endpoint transposes to the shifted single of its ordinary root insertion. -/
theorem diagonalQuotientTargetTranspose
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E) (n : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    (q : UniformizerSquareData l Y E π n A hA) :
    q.quotientAdjunction.homEquiv _ _ q.quotientTarget =
      shiftedRootInsertion q.quotientRight q.quotientRootInsertion := by
  change (UniformizerSquareData.quotientAdjunctionAux q).homEquiv _ _
    (finiteTargetMap q.eW
      (ScalarCompatibility.compositeTarget q.route.first q.route.second)
      q.lineW.endpoint.iso) = _
  let := UniformizerSquareData.quotientAdjunction_commShift q
  exact (congrArg ((UniformizerSquareData.quotientAdjunctionAux q).homEquiv _ _)
      (UniformizerSquareData.quotientTarget_shift q)).trans
    ((homEquiv_shift (UniformizerSquareData.quotientAdjunctionAux q)
      (UniformizerSquareData.quotientEndpointZero q) (2 : ℤ)).trans
        (congrArg (fun f ↦ f⟦(2 : ℤ)⟧' ≫
          (q.quotientRight.mapDerivedCategory.commShiftIso (2 : ℤ)).inv.app _)
            (UniformizerSquareData.quotientEndpointZero_transpose q)))

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
