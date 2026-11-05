/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.ExceptionalForgetMate
public import WeilConjectures.WeilSheaf.UpperShriekGeometric
public import WeilConjectures.CategoryTheory.Adjunction.MatesHCompIsIso
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate

/-! # The proper exceptional adjunction and its canonical geometric forget square -/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits Endofunctor
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.WeilComplex

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))] [IsProper g]

local instance : IsProper (Scheme.Hom.geometricFiberMap g (comp_over g
    (Spec (CommRingCat.of k₀)))) :=
  Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsProper) g _ ‹_›

/-- The proper direct image on bounded constructible adic complexes on the geometric fibres. -/
abbrev properProjectionAdicPush :=
  ProEtale.boundedConstructibleAdicRightDerivedLowerStar
    (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
    (ringChar_algebraicClosure_ne (k₀ := k₀) (l := l))
    (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))

/-- The canonical proper direct-image comparison restricted to Weil complexes. -/
def properProjectionAdicForgetIso :
    derivedLowerStar g ⋙ forgetBoundedConstructibleAdic k₀ l Y ≅
      forgetBoundedConstructibleAdic k₀ l Z ⋙ properProjectionAdicPush k₀ l g :=
  NatIso.ofComponents
    (fun M ↦ ObjectProperty.isoMk _ ((IsoAlgebra.derivedForgetCommIso
      (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l g (comp_over g (Spec (CommRingCat.of k₀))))).app M.obj))
    (fun φ ↦ ObjectProperty.hom_ext _ ((IsoAlgebra.derivedForgetCommIso
      (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l g (comp_over g (Spec (CommRingCat.of k₀))))).hom.naturality
        φ.hom))

/-- The mate of the proper forget comparison is invertible for any choices of the exceptional
right adjoints. The proof retains the geometric counit in the Weil lifting construction. -/
theorem isIso_mateEquiv_properProjectionAdicForgetIso
    {R : WeilComplex k₀ l Y ⥤ WeilComplex k₀ l Z}
    (adj : derivedLowerStar g ⊣ R)
    {R' : (DerivedCategory.boundedConstructibleAdic l
        (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber).FullSubcategory ⥤
      (DerivedCategory.boundedConstructibleAdic l
        (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber).FullSubcategory}
    (adj' : properProjectionAdicPush k₀ l g ⊣ R') (M : WeilComplex k₀ l Y) :
    IsIso ((mateEquiv adj adj' (TwoSquare.mk _ _ _ _
      (properProjectionAdicForgetIso k₀ l g).inv)).app M) := by
  exact IsoAlgebra.isIso_mateEquiv_restrictedDerivedForget_app
    (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l g (comp_over g (Spec (CommRingCat.of k₀))))
    (DerivedCategory.boundedConstructibleAdic l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (DerivedCategory.boundedConstructibleAdic l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (fun _ hK ↦ hK.1) (fun K n hK ↦ ObjectProperty.le_shift _ n K hK)
    (WeilSheaf.boundedConstructibleAdic_frobeniusPullback_mapDerivedCategory_obj_iff
      (k₀ := k₀) (l := l) (X := Z))
    (fun K hK ↦ (WeilSheaf.boundedConstructibleAdic_frobeniusPullback_mapDerivedCategory_obj_iff
      (k₀ := k₀) (l := l) (X := Y) K).2 hK)
    (fun _ hK ↦ boundedConstructibleAdic_rightDerivedFunctor_adicLowerStar_obj
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
      (ringChar_algebraicClosure_ne (k₀ := k₀) (l := l)) _ hK)
    adj'
    (ProEtale.preservesColimit_discrete_rightDerivedFunctor_adicLowerStar (l := l)
      (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
    (objectProperty k₀ l Z) (objectProperty k₀ l Y)
    (objectProperty_iff (X := Z)) (objectProperty_iff (X := Y))
    (objectProperty_rightDerivedLowerStar g) adj M

end AlgebraicGeometry.WeilComplex
