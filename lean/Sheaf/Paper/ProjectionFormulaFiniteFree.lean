/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.Paper.ProjectionFormulaArrows
public import Mathlib.Algebra.Homology.Single
public import Sheaf.Algebra.Homology.KFlatCoefficientUniverse
import Sheaf.Paper.ProjectionFormulaMateRepresentative

/-!
# Finite-free projection formula

Source: Weil conjectures blueprint, proper base change, lemma 1265
(blueprint: lemma-weil-pbc-projection-formula-finite-free).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

set_option backward.isDefEq.respectTransparency false

set_option synthInstance.maxSize 2048 in
/-- For the coefficient complex R^N[a], the specified projection mate and finite-total
inverse are mutually inverse. A single complex in degree -a is R^N[a]; finite products
are the finite direct sums of module sheaves. All other parameters are exactly the
ordinary and derived ringed-topos data of definition 1264, including its chosen
K-injective representative and strict-perfect coefficient package.
Source: proper base change, lemma 1265
(blueprint: lemma-weil-pbc-projection-formula-finite-free).
Proof:
The strict-perfect package is K-flat with flat terms. The arrow API supplies the
ordinary total mate t, its isomorphism instance and inverse s, and K-injectivity of
the target tensor complex J. The representative comparison lemma identifies the
specified derived mate with eC.hom >> Q(t) >> eB.inv. The specified reverse arrow is
eB.hom >> Q(s) >> eC.inv. Cancel eB and eC in each composite, then use functoriality
of Q and the two inverse identities of t. This argument also covers rank zero. -/
theorem ringedProjectionFormula_finiteFree
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
    (hbounded : ∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r → IsZero (F.X r))
    (N : ℕ) (a : ℤ)
    (hfree : F = (HomologicalComplex.single _ (ComplexShape.up ℤ) (-a)).obj
      (∏ᶜ fun _ : Fin N ↦ SheafOfModules.unit
        ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) :
    (ringedProjectionFormulaArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF
        PR PS hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj
        E K hK repE F P hbounded).1 ≫
      (ringedProjectionFormulaArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF
        PR PS hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj
        E K hK repE F P hbounded).2 = 𝟙 _ ∧
    (ringedProjectionFormulaArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF
        PR PS hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj
        E K hK repE F P hbounded).2 ≫
      (ringedProjectionFormulaArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF
        PR PS hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj
        E K hK repE F P hbounded).1 = 𝟙 _ := by
  let := monoidalCategory R
  let := monoidalCategory S
  let := ringedTensorPreadditive R
  let := ringedTensorPreadditive S
  have _ := hRF
  have _ := hfree
  have _ := canonicalAdj
  let hf := StrictPerfectCoefficientPackage.isKFlat_flat R F P hbounded
  let hfR : PR F := (hPR F).mpr hf
  let A := (V.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let pullF := (uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj F
  let J := CochainComplex.mapBifunctor K pullF (CategoryTheory.MonoidalCategory.curriedTensor
    (SheafOfModules.{u} ((sheafCompose JD
      (forget₂ CommRingCat.{u} RingCat.{u})).obj S)))
  let hfS : PS pullF := (hPS pullF).mpr
    ((ringedTopoiCanonicalDerivedTensorPullback uInv uPush adj I c uStar
      hobj hmap LF epsilon hLF PR PS hPR hPS TR TS rR rS k V am).1 F hf.1 hf.2)
  let unitData := canonicalRingedTensorComparison_unit R S RI uInv I c uStar hobj hmap k
  let j := Classical.choose unitData.exists
  have hj := (Classical.choose_spec unitData.exists)
  let t := tensorAdjunctionTotal uStar V am k.mu k.naturality K F
  have ht : IsIso t := by
    with_unfolding_all
      exact tensorAdjunctionTotal_isIso uStar V am k.mu k.naturality j hj K F
        hbounded P.N P.i P.p P.splitting
  let s := inv t
  let eF : LF.obj (DerivedCategory.Q.obj F) ≅ DerivedCategory.Q.obj pullF :=
    @asIso _ _ _ _ (derivedPullbackComplexComparison uStar LF epsilon F)
      (computeL F hf.1 hf.2)
  have : IsIso (derivedPushforwardComplexComparison V RF eta K) := computeR K hK
  let eA : RF.obj E ≅ DerivedCategory.Q.obj A := RF.mapIso repE ≪≫
    (@asIso _ _ _ _ (derivedPushforwardComplexComparison V RF eta K) (computeR K hK)).symm
  let eC : TR.obj (RF.obj E, DerivedCategory.Q.obj F) ≅
      DerivedCategory.Q.obj (CochainComplex.mapBifunctor A F
        (CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))) :=
    TR.mapIso (Iso.prod eA (Iso.refl (DerivedCategory.Q.obj F))) ≪≫
      mixedTensorRepresentative R PR hPR TR rR A F hfR
  have hJ : J.IsKInjective := by
    with_unfolding_all
      exact tensorAdjunctionTotal_target_isKInjective uStar j K hK F
        hbounded P.N P.i P.p P.splitting
  have : IsIso (derivedPushforwardComplexComparison V RF eta J) := computeR J hJ
  let eB : RF.obj (TS.obj (E, LF.obj (DerivedCategory.Q.obj F))) ≅
      DerivedCategory.Q.obj ((V.mapHomologicalComplex (ComplexShape.up ℤ)).obj J) :=
    RF.mapIso (TS.mapIso (Iso.prod repE eF) ≪≫
      mixedTensorRepresentative S PS hPS TS rS K pullF hfS) ≪≫
        (@asIso _ _ _ _ (derivedPushforwardComplexComparison V RF eta J) (computeR J hJ)).symm
  let alpha := ringedTopoiCanonicalDerivedTensorComparison uInv uPush adj I c uStar
    hobj hmap LF epsilon hLF PR PS hPR hPS TR TS rR rS k V am
  have hs : s = inv t := rfl
  have hpi : derivedProjectionFormulaMate LF RF adjD TR TS alpha E
      (DerivedCategory.Q.obj F) = eC.hom ≫ DerivedCategory.Q.map t ≫ eB.inv := by
    exact ringedProjectionFormulaMate_representative uInv uPush adj I c uStar hobj hmap
      LF epsilon hLF PR PS hPR hPS TR TS rR rS k V am RF eta computeR computeL
      adjD canonicalAdj E K hK repE F hfR hJ
  change (derivedProjectionFormulaMate LF RF adjD TR TS alpha E
      (DerivedCategory.Q.obj F)) ≫ (eB.hom ≫ DerivedCategory.Q.map s ≫ eC.inv) = 𝟙 _ ∧
    (eB.hom ≫ DerivedCategory.Q.map s ≫ eC.inv) ≫
      (derivedProjectionFormulaMate LF RF adjD TR TS alpha E
        (DerivedCategory.Q.obj F)) = 𝟙 _
  rw [hpi, hs]
  constructor <;> simp [Category.assoc]


end SheafOfModules
