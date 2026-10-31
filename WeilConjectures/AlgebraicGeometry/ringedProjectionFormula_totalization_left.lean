/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module


public import WeilConjectures.AlgebraicGeometry.ProjectionFormulaArrows
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.AlgebraicGeometry.RingedProjectionFormulaTotalizationLeftData
import WeilConjectures.AlgebraicGeometry.RingedProjectionFormulaMixedComparison
import WeilConjectures.AlgebraicGeometry.RingedProjectionFormulaMixedNaturality

/-! The left inverse equation for the signed totalization projection formula. -/

@[expose] public section
set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

attribute [local instance 2000] Limits.instHasColimitOfHasColimitsOfShape
  Limits.instHasLimitOfHasLimitsOfShape


set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 4096
set_option linter.unusedVariables false
set_option maxHeartbeats 3000000 in
-- The counit calculation keeps the signed total-complex representatives explicit.
set_option synthInstance.maxHeartbeats 100000 in
/-- First inverse equation for the signed totalization projection formula.
Source: proper base change, lemma 1267; this is the corresponding conjunct
of the totalization argument.
Proof: write eA, eB and eC for the specified representative isomorphisms and t for
its finite-total chain mate. Apply the inverse derived adjunction equivalence to the
forward square after composing with eB.inv. Naturality of the derived counit moves the
target representative through that counit. The canonicalAdj equation on the K-injective
target replaces it by the ordinary counit; naturality of the pullback comparison and the
ordinary adjunction then express the transpose of t by the inverse total tensor comparison
followed by the tensor of the ordinary counit. The mixed tensor comparison theorem and
naturality of the target mixed representative reduce this to the tensor of the derived
counit. The canonicalAdj equation on K and naturality with repE identify its first factor;
the inverse coefficient comparison cancels its second factor. This is precisely the
transpose defining derivedProjectionFormulaMate, proving the forward square. Compose that
square with the localization of the finite-total inverse and eC.inv. Functoriality and the
inverse equations cancel the finite-total maps and eC, giving the identity.
(blueprint: new-lem-weil-pbc-projection-formula-totalization-left) -/
theorem ringedProjectionFormula_totalization_left
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{u}} {S RI : Sheaf JD CommRingCat.{u}}
    (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (uPush : Sheaf JD (Type u) ⥤ Sheaf JC (Type u))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (uStar : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
    (hobj : ∀ M : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R), uStar.obj M = changeOfRings
        c (I.modules.obj M))
    (hmap : ∀ {M N : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)} (a : M ⟶ N), uStar.map a =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫
        eqToHom (hobj N).symm)
    [uStar.Additive]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))]
    (LF : DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ⥤ DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)))
    (epsilon : DerivedCategory.Qh ⋙ LF ⟶
      uStar.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hLF : LF.IsLeftDerivedFunctor epsilon
      (HomotopyCategory.quasiIso (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (ComplexShape.up ℤ)))
    (PR : ObjectProperty (CochainComplex (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ))
    (PS : ObjectProperty (CochainComplex (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)) ℤ))
    (hPR : ∀ P, PR P ↔ P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat)
    (hPS : ∀ P, PS P ↔ P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat)
    (TR : (DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) × (DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) ⥤ DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))
    (TS : (DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))) × (DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))) ⥤ DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)))
    (rR : (PR.ι.prod PR.ι) ⋙ Functor.uncurry.obj
        ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) _
          (SheafOfModules.monoidalCategory R)).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
      ((PR.ι ⋙ DerivedCategory.Q).prod (PR.ι ⋙ DerivedCategory.Q)) ⋙ TR)
    (rS : (PS.ι.prod PS.ι) ⋙ Functor.uncurry.obj
        ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)) _
          (SheafOfModules.monoidalCategory S)).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
      ((PS.ι ⋙ DerivedCategory.Q).prod (PS.ι ⋙ DerivedCategory.Q)) ⋙ TS)
    (k : CanonicalRingedTensorComparison R S RI uInv I c uStar hobj)
    (V : SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⥤
      SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (am :
      uStar ⊣ V)
    [V.Additive]
    (RF : DerivedCategory (SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S)) ⥤ DerivedCategory (SheafOfModules.{u} ((sheafCompose JC (forget₂
      CommRingCat.{u} RingCat.{u})).obj R)))
    (eta : V.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    (hRF : ∀ G : DerivedCategory (SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S)) ⥤ DerivedCategory (SheafOfModules.{u} ((sheafCompose JC (forget₂
      CommRingCat.{u} RingCat.{u})).obj R)),
      Function.Bijective (fun b : RF ⟶ G ↦ eta ≫ Functor.whiskerLeft DerivedCategory.Qh b))
    (computeR : ∀ K : CochainComplex (SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S)) ℤ, K.IsKInjective →
      IsIso (derivedPushforwardComplexComparison V RF eta K))
    (computeL : ∀ P : CochainComplex (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ℤ,
      P.IsAcyclicTensorKFlat → (∀ n : ℤ, (P.X n).IsFlat) →
        IsIso (derivedPullbackComplexComparison uStar LF epsilon P))
    (adjD : LF ⊣ RF)
    (canonicalAdj : ∀ K : CochainComplex (SheafOfModules.{u} ((sheafCompose JD (forget₂
      CommRingCat.{u} RingCat.{u})).obj S)) ℤ, K.IsKInjective →
      LF.map (derivedPushforwardComplexComparison V RF eta K) ≫
          adjD.counit.app (DerivedCategory.Q.obj K) =
        derivedPullbackComplexComparison uStar LF epsilon
          ((V.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
            DerivedCategory.Q.map ((am.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app K))
    (E : DerivedCategory (SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S))) (K : CochainComplex (SheafOfModules.{u} ((sheafCompose JD (forget₂
      CommRingCat.{u} RingCat.{u})).obj S)) ℤ) (hK : K.IsKInjective)
    (repE : E ≅ DerivedCategory.Q.obj K)
    (F : CochainComplex (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ℤ)
    (P : StrictPerfectCoefficientPackage ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R) F)
    (hbounded : ∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r → IsZero (F.X r)) :
    (ringedProjectionFormulaArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF
      PR PS hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj
      E K hK repE F P hbounded).1 ≫
      (ringedProjectionFormulaArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF
      PR PS hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj
      E K hK repE F P hbounded).2 = 𝟙 (TR.obj (RF.obj E, DerivedCategory.Q.obj F)) := by
  let := monoidalCategory R
  let := monoidalCategory S
  let := ringedTensorPreadditive R
  let := ringedTensorPreadditive S
  let hf := StrictPerfectCoefficientPackage.isKFlat_flat R F P hbounded
  let hfR : PR F := (hPR F).mpr hf
  let A := (V.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let pullF := (uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj F
  let B := SheafOfModules ((sheafCompose JD (forget₂ CommRingCat RingCat)).obj S)
  let J := CochainComplex.mapBifunctor K pullF
    (@CategoryTheory.MonoidalCategory.curriedTensor B _ (monoidalCategory S))
  let hfS : PS pullF := (hPS pullF).mpr
    ((ringedTopoiCanonicalDerivedTensorPullback uInv uPush adj I c uStar hobj hmap
      LF epsilon hLF PR PS hPR hPS TR TS rR rS k V am).1 F hf.1 hf.2)
  let unitData := canonicalRingedTensorComparison_unit R S RI uInv I c uStar hobj hmap k
  let j := Classical.choose unitData.exists
  have hj := Classical.choose_spec unitData.exists
  let s := tensorAdjunctionTotalInverse uStar V am k.mu k.naturality j hj K F
    hbounded P.N P.i P.p P.splitting
  let eF : LF.obj (DerivedCategory.Q.obj F) ≅ DerivedCategory.Q.obj pullF :=
    @asIso _ _ _ _ (derivedPullbackComplexComparison uStar LF epsilon F)
      (computeL F hf.1 hf.2)
  let eA : RF.obj E ≅ DerivedCategory.Q.obj A := RF.mapIso repE ≪≫
    (@asIso _ _ _ _ (derivedPushforwardComplexComparison V RF eta K)
      (computeR K hK)).symm
  let eC : TR.obj (RF.obj E, DerivedCategory.Q.obj F) ≅
      DerivedCategory.Q.obj (CochainComplex.mapBifunctor A F
        (@CategoryTheory.MonoidalCategory.curriedTensor
          (SheafOfModules ((sheafCompose JC (forget₂ CommRingCat RingCat)).obj R)) _
          (SheafOfModules.monoidalCategory R)) ) :=
    TR.mapIso (Iso.prod eA (Iso.refl (DerivedCategory.Q.obj F))) ≪≫
      mixedTensorRepresentative R PR hPR TR rR A F hfR
  have hJ : J.IsKInjective := tensorAdjunctionTotal_target_isKInjective uStar j K hK F
    hbounded P.N P.i P.p P.splitting
  let eB : RF.obj (TS.obj (E, LF.obj (DerivedCategory.Q.obj F))) ≅
      DerivedCategory.Q.obj ((V.mapHomologicalComplex (ComplexShape.up ℤ)).obj J) :=
    RF.mapIso (TS.mapIso (Iso.prod repE eF) ≪≫
      mixedTensorRepresentative S PS hPS TS rS K pullF hfS) ≪≫
        (@asIso _ _ _ _ (derivedPushforwardComplexComparison V RF eta J)
          (computeR J hJ)).symm
  let t := tensorAdjunctionTotal uStar V am k.mu k.naturality K F
  let alpha := ringedTopoiCanonicalDerivedTensorComparison uInv uPush adj I c uStar
    hobj hmap LF epsilon hLF PR PS hPR hPS TR TS rR rS k V am
  let M := SheafOfModules.{u}
    ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
  let U := uStar.mapHomologicalComplex (.up ℤ)
  let eps : DerivedCategory.Q ⋙ LF ⟶ U ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso M).inv LF ≫
      Functor.whiskerLeft (HomotopyCategory.quotient M (.up ℤ)) epsilon ≫
      Functor.whiskerRight (uStar.mapHomotopyCategoryFactors (.up ℤ)).hom DerivedCategory.Qh ≫
      Functor.whiskerLeft U (DerivedCategory.quotientCompQhIso B).hom
  have htadj : U.map t ≫ (am.mapHomologicalComplex (.up ℤ)).counit.app J =
      (k.totalIso R S RI uInv I c uStar hobj V am A F).inv ≫
        HomologicalComplex.mapBifunctorMap
          ((am.mapHomologicalComplex (.up ℤ)).counit.app K) (𝟙 pullF)
            (@CategoryTheory.MonoidalCategory.curriedTensor B _ (monoidalCategory S))
              (.up ℤ) := by
    change ((am.mapHomologicalComplex (.up ℤ)).homEquiv _ _).symm
      ((am.mapHomologicalComplex (.up ℤ)).homEquiv _ _ _) = _
    exact Equiv.symm_apply_apply _ _
  have hcJ : LF.map (derivedPushforwardComplexComparison V RF eta J) ≫
      adjD.counit.app (DerivedCategory.Q.obj J) =
    eps.app ((V.mapHomologicalComplex (.up ℤ)).obj J) ≫
      DerivedCategory.Q.map ((am.mapHomologicalComplex (.up ℤ)).counit.app J) := by
    exact canonicalAdj J hJ
  have het := eps.naturality t
  change LF.map (DerivedCategory.Q.map t) ≫
      eps.app ((V.mapHomologicalComplex (.up ℤ)).obj J) =
    eps.app (CochainComplex.mapBifunctor A F
      (@CategoryTheory.MonoidalCategory.curriedTensor M _ (monoidalCategory R))) ≫
        DerivedCategory.Q.map (U.map t) at het
  have hmix : LF.map (mixedTensorRepresentative R PR hPR TR rR A F hfR).hom ≫
      eps.app (CochainComplex.mapBifunctor A F
        (@CategoryTheory.MonoidalCategory.curriedTensor M _ (monoidalCategory R))) ≫
          DerivedCategory.Q.map (k.totalIso R S RI uInv I c uStar hobj V am A F).inv =
      alpha.hom.app (DerivedCategory.Q.obj A, DerivedCategory.Q.obj F) ≫
        TS.map (Prod.mkHom (eps.app A) (eps.app F)) ≫
          (mixedTensorRepresentative S PS hPS TS rS (U.obj A) pullF hfS).hom := by
    exact ringedTensorComparison_mixed uInv uPush adj I c uStar hobj hmap LF epsilon hLF
      PR PS hPR hPS TR TS rR rS k V am A F hfR hfS
  have hns := mixedTensorRepresentative_naturality S PS hPS TS rS
    ((am.mapHomologicalComplex (.up ℤ)).counit.app K) pullF hfS
  have hA : LF.map eA.hom ≫ eps.app A ≫
      DerivedCategory.Q.map ((am.mapHomologicalComplex (.up ℤ)).counit.app K) =
      adjD.counit.app E ≫ repE.hom := by
    have hc := canonicalAdj K hK
    have hi := congrArg (fun q ↦ LF.map
      (@inv _ _ _ _ (derivedPushforwardComplexComparison V RF eta K) (computeR K hK)) ≫ q) hc
    simp only [← LF.map_comp_assoc, IsIso.inv_hom_id, LF.map_id, Category.id_comp] at hi
    change adjD.counit.app (DerivedCategory.Q.obj K) =
      LF.map (@inv _ _ _ _ (derivedPushforwardComplexComparison V RF eta K)
        (computeR K hK)) ≫ eps.app A ≫
          DerivedCategory.Q.map ((am.mapHomologicalComplex (.up ℤ)).counit.app K) at hi
    dsimp only [eA, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_inv]
    simp only [LF.map_comp, Category.assoc]
    rw [← hi]
    exact adjD.counit_naturality repE.hom
  have htrans : LF.map (derivedProjectionFormulaMate LF RF adjD TR TS alpha E
      (DerivedCategory.Q.obj F)) ≫
        adjD.counit.app (TS.obj (E, LF.obj (DerivedCategory.Q.obj F))) =
      alpha.hom.app (RF.obj E, DerivedCategory.Q.obj F) ≫
        TS.map (Prod.mkHom (adjD.counit.app E) (𝟙 _)) := by
    have hh : derivedProjectionFormulaMate LF RF adjD TR TS alpha E
        (DerivedCategory.Q.obj F) = adjD.homEquiv _ _
          (alpha.hom.app (RF.obj E, DerivedCategory.Q.obj F) ≫
            TS.map (Prod.mkHom (adjD.counit.app E) (𝟙 _))) := by
      simp [derivedProjectionFormulaMate, Adjunction.rightAdjointProjectionMap_app_app]
    rw [hh]
    exact (adjD.homEquiv _ _).symm_apply_apply _
  have hprod : Prod.mkHom (LF.map eA.hom) (𝟙 (LF.obj (DerivedCategory.Q.obj F))) ≫
      Prod.mkHom (eps.app A) (eps.app F) ≫
        Prod.mkHom (DerivedCategory.Q.map
          ((am.mapHomologicalComplex (.up ℤ)).counit.app K)) (𝟙 _) ≫
            (Iso.prod repE eF).inv = Prod.mkHom (adjD.counit.app E) (𝟙 _) := by
    ext
    · change LF.map eA.hom ≫ eps.app A ≫ DerivedCategory.Q.map
        ((am.mapHomologicalComplex (.up ℤ)).counit.app K) ≫ repE.inv = _
      simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
        congrArg (fun q ↦ q ≫ repE.inv) hA
    · change 𝟙 _ ≫ eps.app F ≫ 𝟙 _ ≫ eF.inv = 𝟙 _
      change 𝟙 _ ≫ eF.hom ≫ 𝟙 _ ≫ eF.inv = 𝟙 _
      simp
  have hmate : derivedProjectionFormulaMate LF RF adjD TR TS alpha E
      (DerivedCategory.Q.obj F) ≫ eB.hom = eC.hom ≫ DerivedCategory.Q.map t := by
    apply (cancel_mono eB.inv).1
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    apply (adjD.homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
    dsimp only [eB, Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, asIso_hom]
    simp only [Functor.map_comp, Category.assoc]
    erw [adjD.counit_naturality (TS.map (Iso.prod repE eF).inv)]
    rw [reassoc_of% (adjD.counit_naturality
      (mixedTensorRepresentative S PS hPS TS rS K pullF hfS).inv)]
    rw [reassoc_of% hcJ]
    rw [reassoc_of% het]
    rw [← DerivedCategory.Q.map_comp_assoc, htadj, DerivedCategory.Q.map_comp]
    dsimp only [eC, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hmix]
    rw [← reassoc_of% hns]
    simp only [Iso.hom_inv_id_assoc]
    have hn := alpha.hom.naturality (Prod.mkHom eA.hom (𝟙 (DerivedCategory.Q.obj F)))
    change LF.map (TR.map (Prod.mkHom eA.hom (𝟙 _))) ≫
        alpha.hom.app (DerivedCategory.Q.obj A, DerivedCategory.Q.obj F) =
      alpha.hom.app (RF.obj E, DerivedCategory.Q.obj F) ≫
        TS.map (Prod.mkHom (LF.map eA.hom)
          (LF.map (𝟙 (DerivedCategory.Q.obj F)))) at hn
    erw [LF.map_id] at hn
    erw [reassoc_of% hn]
    simp only [← TS.map_comp]
    erw [hprod]
    exact htrans
  let arrows := ringedProjectionFormulaArrows uInv uPush adj I c uStar hobj hmap LF epsilon
    hLF PR PS hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj
    E K hK repE F P hbounded
  change arrows.1 ≫ arrows.2 = _
  dsimp only [arrows, ringedProjectionFormulaArrows]
  change derivedProjectionFormulaMate LF RF adjD TR TS alpha E (DerivedCategory.Q.obj F) ≫
      eB.hom ≫ DerivedCategory.Q.map s ≫ eC.inv = _
  have hs : DerivedCategory.Q.map t ≫ DerivedCategory.Q.map s = 𝟙 _ := by
    exact ringedProjectionFormula_left_total_inverse uInv uPush adj I c uStar hobj hmap LF
      epsilon hLF PR PS hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj
      E K hK repE F P hbounded
  have hm := congrArg (fun q ↦ q ≫ DerivedCategory.Q.map s ≫ eC.inv) hmate
  calc
    _ = eC.hom ≫ DerivedCategory.Q.map t ≫ DerivedCategory.Q.map s ≫ eC.inv := by
      simpa only [Category.assoc] using hm
    _ = 𝟙 _ := by rw [← Category.assoc (DerivedCategory.Q.map t), hs]; simp

end SheafOfModules
