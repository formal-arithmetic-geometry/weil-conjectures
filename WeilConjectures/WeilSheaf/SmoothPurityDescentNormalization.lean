/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.CondensedModelBaseChange

/-!
# Normalization of the descended proper-image comparison

The derived comparison used to descend a trace is fixed by its equation with the
right-derived units. This records that equation before forgetting the Weil structure.
-/

@[expose] public section

universe w₀ w w' v v' u u'

open CategoryTheory Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {A : Type*} [Category A] [Abelian A]
  {C : Type u} [Category.{v} C] [Abelian C] {F : C ⥤ C} [F.Additive] [F.IsEquivalence]
  [HasColimitsOfShape (Discrete ℤ) C] [HasExactColimitsOfShape (Discrete ℤ) C]
  {D : Type u'} [Category.{v'} D] [Abelian D] {G : D ⥤ D} [G.Additive] [G.IsEquivalence]
  {L : C ⥤ D} [L.Additive] (e : L ⋙ G ≅ F ⋙ L)
  [HasDerivedCategory.{w₀} A] [HasDerivedCategory.{w} (IsoAlgebra F)]
  [HasDerivedCategory.{w'} (IsoAlgebra G)] [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions (IsoAlgebra F)]
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions (IsoAlgebra G)]
  (T : A ⥤ IsoAlgebra F) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  {T₀ : A ⥤ C} [T₀.Additive] [T₀.PreservesKInjectiveComplexes]
  (α : T ⋙ forget F ≅ T₀)

/-- The comparison with exact precomposition respects the right-derived unit. -/
@[reassoc]
lemma rightDerivedFunctorCompMapOfNatIsoIsoOfForgetIso_hom_fac
    (K : HomotopyCategory A (.up ℤ)) :
    (T ⋙ mapOfNatIso e).rightDerivedFunctorUnit.app K ≫
      (rightDerivedFunctorCompMapOfNatIsoIsoOfForgetIso e T α).hom.app
        (DerivedCategory.Qh.obj K) =
      (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit T (mapOfNatIso e)).app K := by
  simp [rightDerivedFunctorCompMapOfNatIsoIsoOfForgetIso]

variable {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
  [Abelian.HasKInjectiveResolutions B]
  {L₀ : A ⥤ B} [L₀.Additive]
  (S : B ⥤ IsoAlgebra G) [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]

/-- The derived descent square assembled from a sheaf comparison. -/
noncomputable def traceDescentComparison (β : L₀ ⋙ S ≅ T ⋙ mapOfNatIso e) :
    T.mapDerivedCategory ⋙ (mapOfNatIso e).rightDerivedFunctor ≅
      L₀.rightDerivedFunctor ⋙ S.mapDerivedCategory :=
  (rightDerivedFunctorCompMapOfNatIsoIsoOfForgetIso e T α).symm ≪≫
    (Functor.rightDerivedFunctorNatIso β).symm ≪≫
    Functor.rightDerivedFunctorCompMapDerivedCategoryIso L₀ S

/-- Normalization of the derived descent square by the two derived units. -/
lemma traceDescentComparison_inv_fac (β : L₀ ⋙ S ≅ T ⋙ mapOfNatIso e)
    (K : HomotopyCategory A (.up ℤ)) :
    (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit L₀ S).app K ≫
      (traceDescentComparison e T α S β).inv.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory β.hom (.up ℤ)).app K) ≫
        (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit T (mapOfNatIso e)).app K := by
  simp only [traceDescentComparison, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.rightDerivedFunctorCompMapDerivedCategoryIso, Functor.rightDerivedNatIso_inv,
    Functor.rightDerivedNatTrans_app_assoc, Functor.rightDerivedFunctorNatIso,
    Functor.rightDerivedFunctorNatTrans, Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  rw [rightDerivedFunctorCompMapOfNatIsoIsoOfForgetIso_hom_fac]

end CategoryTheory.Endofunctor.IsoAlgebra

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {k : Type u} [Field k] [Finite k] {X Y : Scheme.{u}} {s : X ⟶ Spec (.of k)}
  {t : Y ⟶ Spec (.of k)} {f : X ⟶ Y} {h : f ≫ t = s}

/-- Forgetting the descended sheaf base-change map gives the ordinary base-change map. -/
lemma lowerStarGeometricFiberWeilBaseChange_app_forget
    (hc : UpperStarWeilCompatible Λ f h)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ((lowerStarGeometricFiberWeilBaseChange hc).app M).hom.f =
      (lowerStarBaseChange Λ (Scheme.Hom.isPullback_geometricFiberMap f h).flip.toCommSq).app M := by
  unfold lowerStarGeometricFiberWeilBaseChange
  rw [Endofunctor.IsoAlgebra.mateEquiv_mapOfNatIsoAdjunction_app_hom_f]
  change (mateEquiv (upperStarLowerStarAdjunction Λ f)
    (upperStarLowerStarAdjunction Λ (Scheme.Hom.geometricFiberMap f h))
    (TwoSquare.mk _ _ _ _ (geometricFiberUpperStarComparison Λ f h).inv)).natTrans.app M = _
  rw [geometricFiberUpperStarComparison, Iso.symm_inv,
    ← Adjunction.exchangeRight_eq_mateEquiv, ← lowerStarBaseChange_eq]

/-- The comparison used by the descended trace has the prescribed derived-unit equation. -/
lemma geometricFiberWeilRightDerivedLowerStarIso_inv_fac
    (hc : UpperStarWeilCompatible Λ f h)
    (K : HomotopyCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) (.up ℤ)) :
    (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit (lowerStar Λ f)
      (geometricFiberWeilLowerStar Λ t)).app K ≫
        (geometricFiberWeilRightDerivedLowerStarIso hc).inv.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory
        (lowerStarGeometricFiberWeilBaseChange hc) (.up ℤ)).app K) ≫
      (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit
        (geometricFiberWeilLowerStar Λ s) (geometricFiberMapWeilLowerStar Λ f h)).app K := by
  exact Endofunctor.IsoAlgebra.traceDescentComparison_inv_fac
    (lowerStarGeometricFiberMapCompFrobeniusIso Λ f h)
    (geometricFiberWeilLowerStar Λ s)
    (T₀ := (s.geometricFiberProj)^*⟦Λ⟧) (Iso.refl _)
    (geometricFiberWeilLowerStar Λ t) (asIso (lowerStarGeometricFiberWeilBaseChange hc)) K

end AlgebraicGeometry.ProEtale.CondensedRing
