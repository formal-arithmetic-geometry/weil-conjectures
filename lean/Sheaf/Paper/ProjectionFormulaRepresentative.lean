/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.Paper.ProjectionFormulaArrows

/-!
# The canonical projection mate on mixed tensor representatives

Source: proper base change, lemma 1267, steps 9--11.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

set_option maxHeartbeats 800000 in
-- Keep the explicit derived comparison interfaces elaborating within this budget.
/-- The counit mate agrees with the ordinary total mate on the canonical mixed
representatives. The coefficient may be any K-flat complex with flat terms; only
the target tensor complex is required to be K-injective. No inverse to the total
mate, bounded support, or finite-projective splitting is assumed.

Source: proper base change, lemma 1267, steps 9--11
(blueprint: lem-weil-pbc-projection-formula-mixed-representative).

Proof: choose a K-flat flat-term resolution v of A = V(K). Tensoring v with F
is a quasi-isomorphism by the acyclic-cone test. The defining square of the mixed
representative identifies this resolution with the derived tensor source.
The defining square of the canonical derived tensor comparison identifies its
pullback with the ordinary pullback-tensor comparison on v tensor F. Naturality
of the mixed target representative applied to the ordinary counit identifies
the tensor of that counit with the localized tensor chain map. The canonicalAdj
identity identifies the derived counit on K with the ordinary counit preceded by
the left-derived comparison. Thus the two arrows have equal adjuncts after the
invertible resolving source comparison. Cancel that comparison and use injectivity
of the adjunction bijection. Finally transport the equality along repE, using
naturality of the mate, the counit, and the mixed tensor comparisons.

For the naturality assertion, choose a flat-term K-flat resolution q of the target
of a chain map f. Apply the right-fraction calculus in the homotopy category to
f and q, and then resolve the resulting source. This gives quasi-isomorphisms p,q
and a chain map g with p followed by f homotopic to g followed by q. Tensoring the
homotopy with the identity of F and localizing gives a commutative square.
The two defining mixed-representative squares and naturality of rR then give
naturality after cancelling TR(Q(p),1). For the pullback square, precompose with
LF(TR(Q(p),1)); it is invertible. Use the mixed defining square, naturality of
epsilon, and naturality of the total tensor comparison, checked on coprojections.
The result is exactly the canonical two-K-flat square for alpha at the resolving
complex and F. Cancel the precomposition. The final transposition uses
`Adjunction.map_rightAdjointProjectionMap_app_app_comp_counit` and the ordinary
adjunction identity for `tensorAdjunctionTotal`. -/
theorem ringedProjectionFormula_mixed_representative
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
    (hf : PR F)
    (hfs : PS ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj F))
    (hJ : (CochainComplex.mapBifunctor K
      ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
      (@CategoryTheory.MonoidalCategory.curriedTensor _ _
        (SheafOfModules.monoidalCategory S))).IsKInjective) :
    letI := monoidalCategory R
    letI := monoidalCategory S
    letI := ringedTensorPreadditive R
    letI := ringedTensorPreadditive S
    let A := (V.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
    let pullF := (uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj F
    let J := CochainComplex.mapBifunctor K pullF
      (CategoryTheory.MonoidalCategory.curriedTensor _)
    let eF : LF.obj (DerivedCategory.Q.obj F) ≅ DerivedCategory.Q.obj pullF :=
      @asIso _ _ _ _ (derivedPullbackComplexComparison uStar LF epsilon F)
        (computeL F ((hPR F).mp hf).1 ((hPR F).mp hf).2)
    let eA : RF.obj E ≅ DerivedCategory.Q.obj A := RF.mapIso repE ≪≫
      (@asIso _ _ _ _ (derivedPushforwardComplexComparison V RF eta K) (computeR K hK)).symm
    let eC := TR.mapIso (Iso.prod eA (Iso.refl (DerivedCategory.Q.obj F))) ≪≫
      mixedTensorRepresentative R PR hPR TR rR A F hf
    let eB := RF.mapIso (TS.mapIso (Iso.prod repE eF) ≪≫
      mixedTensorRepresentative S PS hPS TS rS K pullF hfs) ≪≫
      (@asIso _ _ _ _ (derivedPushforwardComplexComparison V RF eta J) (computeR J hJ)).symm
    let alpha := ringedTopoiCanonicalDerivedTensorComparison uInv uPush adj I c uStar
      hobj hmap LF epsilon hLF PR PS hPR hPS TR TS rR rS k V am
    derivedProjectionFormulaMate LF RF adjD TR TS alpha E (DerivedCategory.Q.obj F) ≫
      eB.hom = eC.hom ≫
        DerivedCategory.Q.map (tensorAdjunctionTotal uStar V am k.mu k.naturality K F) := by sorry

end SheafOfModules
