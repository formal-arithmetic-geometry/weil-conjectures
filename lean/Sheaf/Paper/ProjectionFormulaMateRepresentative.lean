/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Sheaf.Paper.ProjectionFormulaArrows
import Sheaf.Algebra.Homology.KFlatResolutionGeneral

/-! # Representatives of the derived projection mate

Source: proper base change, lemma 1265, the counit identification.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- The canonical derived projection mate is represented by the ordinary total mate.
Only the coefficient is required to be K-flat with flat terms. The target tensor complex
is assumed K-injective so that its pushforward comparison is an isomorphism. No finite
rank, boundedness, splitting, or invertibility of the ordinary total mate is assumed.

Source: the counit identification in the proof of proper base change, lemma 1265,
and its expanded K-flat/K-injective representative argument, steps 4--6; Stacks
Tags 06YS and 07A4.
(blueprint: lem-weil-pbc-projection-formula-mate-representative).

Proof:
Write Lc,Vc for the functors on complexes, beta for the pullback comparison and gamma
for the pushforward comparison. Write mR(X,F), mS(Y,Lc F) for the specified mixed tensor
representative isomorphisms, and kappa for the ordinary pullback-tensor total isomorphism.
First these mixed comparisons are natural in their first complex. Choose a functorial
K-flat resolution G(X) -> X with flat terms. Such G is constructed by the functorial
flat resolution of sheaves, reduced left resolution, and the sequential total-colimit
construction of Tag 06YS. The source library calls this resolutionFunctor, proves
kFlat_resolutionFunctor_obj, and obtains flat terms by closedUnderColimitsOfShape_flat.
For f:X -> Y, apply naturality of rR.inv to (G(f),id F) and the defining representative
squares for G(X) -> X and G(Y) -> Y. Naturality of the resolution map identifies the
outer composites. Cancel the isomorphism TR(Q(G(X) -> X),id); this gives
TR(Qf,id) >> mR(Y,F).hom = mR(X,F).hom >> Q(f tensor id). The same proof works over S.

Next resolve only X by a K-flat flat-term P -> X. For (P,F), the defining square of
alpha is available. The mixed comparisons on flat pairs are rR.inv and rS.inv, as
follows by taking the identity resolution in their defining squares. Multiply the
alpha square by these inverses to obtain
LF(mR(P,F).hom) >> beta(P tensor F) >> Q(kappa(P,F).inv) =
alpha(QP,QF) >> TS(beta P,beta F) >> mS(Lc P,Lc F).hom.
Precompose the desired version for X with LF(TR(Q(P -> X),id)). Use the defining
square for mR(X,F), naturality of beta and kappa, naturality of alpha, and the mixed
naturality just proved over S. Both sides become the displayed flat-pair square.
Cancel that precomposition, which is invertible because P -> X is a quasi-isomorphism.

Apply this square to X=Vc K and apply mixed naturality over S to the ordinary counit
Lc(Vc K) -> K. The canonicalAdj equations at K and J express the two derived counits
in terms of beta and gamma. Naturality of the derived counit at repE, together with
the inverse of gamma K, identifies LF(eA.hom) followed by beta(Vc K) and the localized
ordinary counit with counit E followed by repE.hom. Under the derived adjunction,
the adjunct of Q(t) followed by gamma J is therefore alpha followed by the derived
counit tensor the identity. This is exactly the defining adjunct of the specified
projection mate, so injectivity of the adjunction hom equivalence gives
pi >> RF(TS(repE.hom,eF.hom) >> mS(K,Lc F).hom) =
TR(eA.hom,id) >> mR(Vc K,F).hom >> Q(t) >> gamma J.
The left comparison, followed by gamma J inverse, is eB.hom; the first two right
factors are eC.hom. Cancel the invertible gamma J and the representative isomorphisms
to obtain the displayed equality. This argument includes zero complexes unchanged. -/
theorem ringedProjectionFormulaMate_representative
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
    (hfR : PR F)
    (hJ : (CochainComplex.mapBifunctor K
      ((uStar.mapHomologicalComplex (.up ℤ)).obj F)
      (@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{u}
        ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)) _
          (monoidalCategory S))).IsKInjective) :
  letI := monoidalCategory R
  letI := monoidalCategory S
  letI := ringedTensorPreadditive R
  letI := ringedTensorPreadditive S
  let hf := (hPR F).mp hfR
  let A := (V.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let pullF := (uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj F
  let J := CochainComplex.mapBifunctor K pullF (CategoryTheory.MonoidalCategory.curriedTensor
    (SheafOfModules.{u} ((sheafCompose JD
      (forget₂ CommRingCat.{u} RingCat.{u})).obj S)))
  let hfS : PS pullF := (hPS pullF).mpr
    ((ringedTopoiCanonicalDerivedTensorPullback uInv uPush adj I c uStar
      hobj hmap LF epsilon hLF PR PS hPR hPS TR TS rR rS k V am).1 F hf.1 hf.2)
  let eF : LF.obj (DerivedCategory.Q.obj F) ≅ DerivedCategory.Q.obj pullF :=
    @asIso _ _ _ _ (derivedPullbackComplexComparison uStar LF epsilon F)
      (computeL F hf.1 hf.2)
  let eA : RF.obj E ≅ DerivedCategory.Q.obj A := RF.mapIso repE ≪≫
    (@asIso _ _ _ _ (derivedPushforwardComplexComparison V RF eta K) (computeR K hK)).symm
  let eC : TR.obj (RF.obj E, DerivedCategory.Q.obj F) ≅
      DerivedCategory.Q.obj (CochainComplex.mapBifunctor A F
        (CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))) :=
    TR.mapIso (Iso.prod eA (Iso.refl (DerivedCategory.Q.obj F))) ≪≫
      mixedTensorRepresentative R PR hPR TR rR A F hfR
  let eB : RF.obj (TS.obj (E, LF.obj (DerivedCategory.Q.obj F))) ≅
      DerivedCategory.Q.obj ((V.mapHomologicalComplex (ComplexShape.up ℤ)).obj J) :=
    RF.mapIso (TS.mapIso (Iso.prod repE eF) ≪≫
      mixedTensorRepresentative S PS hPS TS rS K pullF hfS) ≪≫
        (@asIso _ _ _ _ (derivedPushforwardComplexComparison V RF eta J) (computeR J hJ)).symm
  let alpha := ringedTopoiCanonicalDerivedTensorComparison uInv uPush adj I c uStar
    hobj hmap LF epsilon hLF PR PS hPR hPS TR TS rR rS k V am
  derivedProjectionFormulaMate LF RF adjD TR TS alpha E (DerivedCategory.Q.obj F) =
    eC.hom ≫ DerivedCategory.Q.map
      (tensorAdjunctionTotal uStar V am k.mu k.naturality K F) ≫ eB.inv := by
  sorry

end SheafOfModules
