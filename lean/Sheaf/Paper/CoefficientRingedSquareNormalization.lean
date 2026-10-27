/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Sheaf.Paper.CondensedModuleDerivedPushpull

/-! # Normalization of the coefficient ringed square

Source: Stacks Project, Cohomology on Sites, Tags 0D6D and 0D6E; blueprint
main-20261015, proper-base-change-rational.proof.md, paragraph (3)
(blueprint: lem-sfb-coefficient-ringed-square-normalization).

The path comparisons below are written in internal-module coordinates. The fixed exact
section equivalences transport these universal composition comparisons to the ringed
paths. The direct-image construction derives both edges, then uses exact restriction;
it does not define the result to be the inverse of `derivedComapLowerStarIso`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

section DerivedCompatibility

variable {A B C : Type*} [Category A] [Category B] [Category C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]

-- The two canonical exact-postcomposition isomorphisms have the same universal unit.
private theorem exact_comp_compare (F : A ⥤ B) (G : B ⥤ C)
    [F.Additive] [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    Functor.rightDerivedFunctorCompMapDerivedCategoryIsoViaRightDerived F G =
      Functor.rightDerivedFunctorCompMapDerivedCategoryIso F G := by
  apply Iso.ext
  apply Functor.rightDerived_ext (F ⋙ G).rightDerivedFunctor
    (F ⋙ G).rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
  have hc := Functor.rightDerivedNatTrans_fac (F ⋙ G).rightDerivedFunctor
    (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor)
    (F ⋙ G).rightDerivedFunctorUnit (Functor.rightDerivedFunctorCompUnit F G)
    (HomotopyCategory.quasiIso A (.up ℤ)) (𝟙 _)
  simp only [Category.id_comp] at hc
  simp only [Functor.rightDerivedFunctorCompMapDerivedCategoryIsoViaRightDerived,
    Functor.rightDerivedFunctorCompMapDerivedCategoryIso, Iso.trans_hom,
    Functor.whiskerLeft_comp, Functor.rightDerivedUnique, Functor.rightDerivedNatIso_hom,
    Iso.refl_hom]
  rw [← Category.assoc, hc, Functor.rightDerivedNatTrans_fac, Category.id_comp]
  ext K
  have h := congrArg (fun t ↦ t.app ((F.mapHomotopyCategory (.up ℤ)).obj K))
    G.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  simp only [Functor.rightDerivedFunctorCompUnit,
    Functor.rightDerivedFunctorCompMapDerivedCategoryUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.isoWhiskerLeft_hom,
    Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id, Category.assoc]
  erw [G.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality]
  erw [reassoc_of% h]

-- The quotient-to-localization comparison is the identity on a complex.
omit [Abelian.HasKInjectiveResolutions B] in
private theorem objQ_hom (F : A ⥤ B) [F.Additive]
    (I : CochainComplex A ℤ) [I.IsKInjective] :
    (F.rightDerivedFunctorObjQIso I).hom =
      inv (F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj I)) := by
  simp only [Functor.rightDerivedFunctorObjQIso, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, asIso_inv,
    DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift_hom, Quotient.lift.isLift_inv]
  repeat erw [CategoryTheory.Functor.map_id]
  repeat erw [Category.id_comp]
  repeat erw [Category.comp_id]

omit [Abelian.HasKInjectiveResolutions B] in
private theorem objQ_inv (F : A ⥤ B) [F.Additive]
    (I : CochainComplex A ℤ) [I.IsKInjective] :
    (F.rightDerivedFunctorObjQIso I).inv =
      F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj I) := by
  simp only [Functor.rightDerivedFunctorObjQIso, Iso.trans_inv, Iso.symm_inv,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_inv, asIso_hom,
    DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift_hom, Quotient.lift.isLift_inv]
  repeat erw [CategoryTheory.Functor.map_id]
  repeat erw [Category.id_comp]
  repeat erw [Category.comp_id]

omit [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B] in
private theorem factorsh_hom (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (I : CochainComplex A ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj I) =
      F.mapDerivedCategoryFactors.hom.app I := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  simp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Functor.mapHomotopyCategoryFactors,
    Quotient.lift.isLift_hom, Quotient.lift.isLift_inv]
  repeat erw [CategoryTheory.Functor.map_id]
  repeat erw [Category.id_comp]
  repeat erw [Category.comp_id]

omit [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B] in
private theorem factorsh_inv (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (I : CochainComplex A ℤ) :
    F.mapDerivedCategoryFactorsh.inv.app ((HomotopyCategory.quotient _ _).obj I) =
      F.mapDerivedCategoryFactors.inv.app I := by
  have h := congrArg (fun e ↦ e.inv)
    (Iso.ext (factorsh_hom F I) :
      F.mapDerivedCategoryFactorsh.app ((HomotopyCategory.quotient _ _).obj I) =
        F.mapDerivedCategoryFactors.app I)
  exact h

-- Composition units on homotopy objects use the identity composition bridge.
private theorem comp_unit_app (F : A ⥤ B) (G : B ⥤ C)
    [F.Additive] [G.Additive] (K : HomotopyCategory A (.up ℤ)) :
    (Functor.rightDerivedFunctorCompUnit F G).app K =
      G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app K) := by
  have hi := (Functor.mapHomotopyCategoryCompIso
    (Iso.refl (F ⋙ G)) (.up ℤ)).inv_hom_id_app K
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id] at hi
  simp [Functor.rightDerivedFunctorCompUnit, hi]

omit [Abelian.HasKInjectiveResolutions B] in
private theorem exact_comp_unit_app (F : A ⥤ B) (G : B ⥤ C)
    [F.Additive] [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (K : HomotopyCategory A (.up ℤ)) :
    (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit F G).app K =
      G.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
        G.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app K) := by
  have hi := (Functor.mapHomotopyCategoryCompIso
    (Iso.refl (F ⋙ G)) (.up ℤ)).inv_hom_id_app K
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id] at hi
  simp [Functor.rightDerivedFunctorCompMapDerivedCategoryUnit, hi]

-- These are the universal normalization equations for both composition comparisons.
private theorem comp_fac (F : A ⥤ B) (G : B ⥤ C)
    [F.Additive] [G.Additive] [F.PreservesKInjectiveComplexes]
    (K : HomotopyCategory A (.up ℤ)) :
    (F ⋙ G).rightDerivedFunctorUnit.app K ≫
      (Functor.rightDerivedFunctorCompIso F G).hom.app (DerivedCategory.Qh.obj K) =
      G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app K) := by
  simpa only [Functor.rightDerivedFunctorCompIso, Functor.rightDerivedUnique,
    Functor.rightDerivedNatIso_hom, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    comp_unit_app] using
    (Functor.rightDerivedNatTrans_app (F ⋙ G).rightDerivedFunctor
      (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor)
      (F ⋙ G).rightDerivedFunctorUnit (Functor.rightDerivedFunctorCompUnit F G)
      (HomotopyCategory.quasiIso A (.up ℤ)) (𝟙 _) K)

omit [Abelian.HasKInjectiveResolutions B] in
private theorem exact_comp_fac (F : A ⥤ B) (G : B ⥤ C)
    [F.Additive] [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (K : HomotopyCategory A (.up ℤ)) :
    (F ⋙ G).rightDerivedFunctorUnit.app K ≫
      (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F G).hom.app
        (DerivedCategory.Qh.obj K) =
      G.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
        G.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app K) := by
  simpa only [Functor.rightDerivedFunctorCompMapDerivedCategoryIso,
    Functor.rightDerivedUnique, Functor.rightDerivedNatIso_hom,
    Iso.refl_hom, NatTrans.id_app, Category.id_comp, exact_comp_unit_app] using
    (Functor.rightDerivedNatTrans_app (F ⋙ G).rightDerivedFunctor
      (F.rightDerivedFunctor ⋙ G.mapDerivedCategory)
      (F ⋙ G).rightDerivedFunctorUnit
      (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit F G)
      (HomotopyCategory.quasiIso A (.up ℤ)) (𝟙 _) K)

-- A square of additive functors normalizes on representatives by its universal units.
-- Keeping the square abstract avoids unfolding the underlying sheaf functors.
private theorem derived_bridge_formula {D : Type*} [Category D] [Abelian D]
    [HasDerivedCategory D] (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ D) (J : D ⥤ C)
    [F.Additive] [G.Additive] [H.Additive] [J.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [F.PreservesKInjectiveComplexes] (e : H ⋙ J ≅ F ⋙ G)
    (I : CochainComplex A ℤ) [I.IsKInjective] :
    (J.mapDerivedCategory.mapIso (H.rightDerivedFunctorObjQIso I) ≪≫
      J.mapDerivedCategoryFactors.app ((H.mapHomologicalComplex (.up ℤ)).obj I)).inv ≫
      ((Functor.rightDerivedFunctorCompMapDerivedCategoryIso H J).symm ≪≫
        Functor.rightDerivedFunctorNatIso e ≪≫
        Functor.rightDerivedFunctorCompIso F G ≪≫
        Functor.isoWhiskerRight F.rightDerivedFunctorIsoMapDerivedCategory
          G.rightDerivedFunctor).hom.app (DerivedCategory.Q.obj I) ≫
      (G.rightDerivedFunctor.mapIso (F.mapDerivedCategoryFactors.app I) ≪≫
        G.rightDerivedFunctorObjQIso ((F.mapHomologicalComplex (.up ℤ)).obj I)).hom =
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app I) := by
  let K := (HomotopyCategory.quotient A (.up ℤ)).obj I
  have he := Functor.rightDerivedNatTrans_app
    (H ⋙ J).rightDerivedFunctor (F ⋙ G).rightDerivedFunctor
    (H ⋙ J).rightDerivedFunctorUnit (F ⋙ G).rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso A (.up ℤ))
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory e.hom (.up ℤ))
      DerivedCategory.Qh) K
  have ht := exact_comp_fac H J K
  change _ = J.mapDerivedCategoryFactorsh.inv.app
      ((HomotopyCategory.quotient _ _).obj ((H.mapHomologicalComplex (.up ℤ)).obj I)) ≫
    J.mapDerivedCategory.map (H.rightDerivedFunctorUnit.app K) at ht
  rw [factorsh_inv, ← objQ_inv H I] at ht
  have hs := comp_fac F G K
  have hu := congrArg (fun t ↦ t.app K) F.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hu
  rw [factorsh_inv] at hu
  change (H ⋙ J).rightDerivedFunctorUnit.app K ≫
      (Functor.rightDerivedFunctorNatIso e).hom.app (DerivedCategory.Q.obj I) =
    DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app I) ≫
      (F ⋙ G).rightDerivedFunctorUnit.app K at he
  change _ = (J.mapDerivedCategory.mapIso (H.rightDerivedFunctorObjQIso I) ≪≫
    J.mapDerivedCategoryFactors.app ((H.mapHomologicalComplex (.up ℤ)).obj I)).inv at ht
  erw [← ht]
  dsimp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  simp only [Category.assoc]
  erw [Iso.hom_inv_id_app_assoc]
  erw [reassoc_of% he]
  erw [reassoc_of% hs]
  dsimp only [Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  rw [objQ_hom]
  erw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  erw [hu]
  erw [Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  erw [IsIso.hom_inv_id, Category.comp_id]

end DerivedCompatibility

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]
  [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The canonical direct-image comparison of the paths f_R phi_X and phi_Y f_S,
in the fixed internal coordinates. Compose the universal right-derived comparisons
and derive the inverse identity-on-underlying-sheaves bridge. Exact restriction is
identified with its termwise localization only after composing the two derived edges.
Thus this is the 0D6E path comparison, with its specified derived units.
Source: Stacks 0D6E (blueprint: lem-sfb-coefficient-ringed-square-normalization). -/
def coefficientRingedDirectImageComparison :=
  (Functor.isoWhiskerRight
    (Mod.comap (coefficientMap a X)).rightDerivedFunctorIsoMapDerivedCategory.symm
    (lowerStar R f).rightDerivedFunctor) ≪≫
  (Functor.rightDerivedFunctorCompIso (Mod.comap (coefficientMap a X))
    (lowerStar R f)).symm ≪≫
  Functor.rightDerivedFunctorNatIso (comapLowerStarIso a f).symm ≪≫
  Functor.rightDerivedFunctorCompMapDerivedCategoryIsoViaRightDerived
    (lowerStar S f) (Mod.comap (coefficientMap a Y))

set_option maxHeartbeats 800000 in
-- Elaborating both full internal-module derived adjunctions needs additional heartbeats.
/-- The canonical pullback path comparison, in the fixed internal coordinates.
The ringed comparison/adjunction theorem identifies this comparison with the conjugate
of the independently constructed 0D6E direct-image path comparison. Taking that
conjugate uses the specified geometric and scalar derived adjunctions. No arbitrary
pullback isomorphism, or the inverse of derivedPullIso, enters this construction.
Source: Stacks 0D6D and 0D6E
(blueprint: lem-sfb-coefficient-ringed-square-normalization). -/
def coefficientRingedPullbackComparison :=
  (conjugateIsoEquiv
    ((derivedUpperStarLowerStarAdjunction R f).comp
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)))
    ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y)).comp
      (derivedUpperStarLowerStarAdjunction S f))).symm
    (coefficientRingedDirectImageComparison a f)

/-- Resolution coordinates for G_R U_X on a K-injective S_X-complex. Restriction
preserves K-injectivity because extension is exact. Use its exact-factorization
comparison followed by the inverse right-derived unit on the restricted complex.
Source: Stacks 0D6E (blueprint: lem-sfb-coefficient-ringed-square-normalization). -/
def coefficientRingedSourceResolution
    (I : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj S X)) ℤ) [I.IsKInjective] :
    ((Mod.comap (coefficientMap a X)).mapDerivedCategory ⋙
      (lowerStar R f).rightDerivedFunctor).obj (DerivedCategory.Q.obj I) ≅
    DerivedCategory.Q.obj
      (((Mod.comap (coefficientMap a X) ⋙ lowerStar R f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) :=
  (lowerStar R f).rightDerivedFunctor.mapIso
    ((Mod.comap (coefficientMap a X)).mapDerivedCategoryFactors.app I) ≪≫
  (lowerStar R f).rightDerivedFunctorObjQIso
    (((Mod.comap (coefficientMap a X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)

/-- Resolution coordinates for U_Y G_S on a K-injective S_X-complex. Resolve I only;
no assertion that f_* I is K-injective is made. Apply exact restriction to the
canonical right-derived resolution isomorphism, then its exact factorization.
Source: Stacks 0D6E (blueprint: lem-sfb-coefficient-ringed-square-normalization). -/
def coefficientRingedTargetResolution
    (I : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj S X)) ℤ) [I.IsKInjective] :
    ((lowerStar S f).rightDerivedFunctor ⋙
      (Mod.comap (coefficientMap a Y)).mapDerivedCategory).obj (DerivedCategory.Q.obj I) ≅
    DerivedCategory.Q.obj
      (((lowerStar S f ⋙ Mod.comap (coefficientMap a Y)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) :=
  (Mod.comap (coefficientMap a Y)).mapDerivedCategory.mapIso
    ((lowerStar S f).rightDerivedFunctorObjQIso I) ≪≫
  (Mod.comap (coefficientMap a Y)).mapDerivedCategoryFactors.app
    (((lowerStar S f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

set_option maxHeartbeats 1000000 in
-- The conjugate compares two full derived composite adjunctions.
/-- The specified ringed path comparisons are the inverse specified scalar comparisons,
including both representative formulas on K-injective complexes.
Source: Stacks 0D6D and 0D6E; blueprint main-20261015 rational proper base change,
paragraph (3) (blueprint: lem-sfb-coefficient-ringed-square-normalization).

Proof:
1. Compare the two exact-postcomposition constructions by uniqueness of right
   derived functors. Their universal units agree by naturality and the unit
   equation for `rightDerivedFunctorIsoMapDerivedCategory`.
2. Expand the four factors of the direct-image comparisons. They are inverse
   factors in reverse order, so C = e.symm as natural isomorphisms.
3. The pullback comparisons are the specified conjugates of C and e along the
   same composite adjunctions. Conjugation exchanges their inverse components.
4. On a K-injective I, evaluate the universal derived bridge equation and both
   composition-unit equations. Exact restriction preserves K-injectives on the
   source. Its derived-unit comparison cancels with its exact factorization;
   the geometric right-derived unit cancels with the resolution comparison.
   This gives the formula for e without requiring f_* I to be K-injective.
5. Take inverse components of that isomorphism equality and substitute C=e.symm
   to obtain the formula for C. -/
theorem coefficient_ringed_square_normalization
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (X₀ Y₀ : Over (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) :
    (coefficientRingedDirectImageComparison a f₀.left).hom =
        (derivedComapLowerStarIso a f₀.left).inv ∧
    (coefficientRingedPullbackComparison a f₀.left).hom =
        (derivedPullIso a f₀.left).inv ∧
    ∀ (I : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X₀.left) Ab.{u + 1})
        (condensedRingObj S X₀.left)) ℤ) [I.IsKInjective],
      (coefficientRingedSourceResolution a f₀.left I).inv ≫
          (coefficientRingedDirectImageComparison a f₀.left).hom.app (DerivedCategory.Q.obj I) ≫
          (coefficientRingedTargetResolution a f₀.left I).hom =
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (comapLowerStarIso a f₀.left)
            (ComplexShape.up ℤ)).inv.app I) ∧
      (coefficientRingedTargetResolution a f₀.left I).inv ≫
          (derivedComapLowerStarIso a f₀.left).hom.app (DerivedCategory.Q.obj I) ≫
          (coefficientRingedSourceResolution a f₀.left I).hom =
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (comapLowerStarIso a f₀.left)
            (ComplexShape.up ℤ)).hom.app I) := by
  have hdirect : coefficientRingedDirectImageComparison a f₀.left =
      (derivedComapLowerStarIso a f₀.left).symm := by
    simp only [coefficientRingedDirectImageComparison, derivedComapLowerStarIso,
      exact_comp_compare]
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
      Functor.rightDerivedFunctorNatIso, Category.assoc]
  have hpull : coefficientRingedPullbackComparison a f₀.left =
      (derivedPullIso a f₀.left).symm := by
    unfold coefficientRingedPullbackComparison
    rw [hdirect]
    rfl
  refine ⟨congrArg Iso.hom hdirect, congrArg Iso.hom hpull, ?_⟩
  intro I hI
  have hformula :
      (coefficientRingedTargetResolution a f₀.left I).inv ≫
          (derivedComapLowerStarIso a f₀.left).hom.app (DerivedCategory.Q.obj I) ≫
          (coefficientRingedSourceResolution a f₀.left I).hom =
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (comapLowerStarIso a f₀.left)
            (ComplexShape.up ℤ)).hom.app I) := by
    exact derived_bridge_formula (Mod.comap (coefficientMap a X₀.left))
      (lowerStar R f₀.left) (lowerStar S f₀.left)
      (Mod.comap (coefficientMap a Y₀.left)) (comapLowerStarIso a f₀.left) I
  refine ⟨?_, hformula⟩
  rw [hdirect]
  have hiso :
      (coefficientRingedTargetResolution a f₀.left I).symm ≪≫
          (derivedComapLowerStarIso a f₀.left).app (DerivedCategory.Q.obj I) ≪≫
          coefficientRingedSourceResolution a f₀.left I =
        DerivedCategory.Q.mapIso
          ((NatIso.mapHomologicalComplex (comapLowerStarIso a f₀.left)
            (.up ℤ)).app I) := Iso.ext hformula
  simpa only [Iso.trans_inv, Iso.symm_inv, Iso.symm_hom, Iso.app_inv, Functor.mapIso_inv,
    Category.assoc] using congrArg Iso.inv hiso

end AlgebraicGeometry.ProEtale.CondensedRing
