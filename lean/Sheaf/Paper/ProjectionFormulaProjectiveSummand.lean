/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.Paper.ProjectionFormulaArrows
import Sheaf.Paper.RingedTopoiCanonicalTensorPullback
import Sheaf.Paper.ProjectionFormulaFiniteFree

/-!
# Finite-projective summand equations

Source: Weil conjectures blueprint, proper base change, lemma 1266
(blueprint: lemma-weil-pbc-projection-formula-projective-summand).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

variable
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
    (hPR : ∀ P, PR P ↔ P.IsKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat)
    (hPS : ∀ P, PS P ↔ P.IsKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat)
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
    (computeR : ∀ K : CochainComplex (SheafOfModules.{u} ((sheafCompose JD (forget₂
      CommRingCat.{u}
      RingCat.{u})).obj S)) ℤ, K.IsKInjective →
      IsIso (derivedPushforwardComplexComparison V RF eta K))
    (computeL : ∀ P : CochainComplex (SheafOfModules.{u} ((sheafCompose JC (forget₂
      CommRingCat.{u}
      RingCat.{u})).obj R)) ℤ,
      P.IsKFlat → (∀ n : ℤ, (P.X n).IsFlat) →
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

/-- The arrows of definition 1264 for one coefficient sheaf, placed in degree zero.
The package records the displayed finite-free splitting in degree zero; its other
terms are zero. This is a specialization of the existing arrows, with the canonical
bound [0,0], and introduces no new choice of a map or inverse.
Source: proper base change, lemma 1266 and definition 1264
(blueprint: lemma-weil-pbc-projection-formula-projective-summand). -/
noncomputable def ringedProjectionFormulaSummandArrows
    (M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (P : StrictPerfectCoefficientPackage ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R) ((HomologicalComplex.single (SheafOfModules.{u} ((sheafCompose JC
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (ComplexShape.up ℤ) 0).obj M)) :=
  ringedProjectionFormulaArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF PR PS hPR hPS TR
      TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj E K hK repE
    ((HomologicalComplex.single (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) (ComplexShape.up ℤ) 0).obj M) P
    ⟨0, 0, fun r h ↦ HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M r
      (h.elim ne_of_lt ne_of_gt)⟩

/-- The two summand arrows are inverse and independent of the finite-free presentation.
Source: proper base change, lemma 1266
(blueprint: lemma-weil-pbc-projection-formula-projective-summand).
Proof: write A(X)=Rh_*E tensor X and B(X)=Rh_*(E tensor Lh^*X).
Naturality of the canonical tensor comparison gives naturality of its counit
composite. Transport through the derived adjunction to obtain
B(i) pi_M = pi_N A(i) and B(p) pi_N = pi_M A(p)
(def-weil-pbc-projection-formula-arrows;
lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
Insert these identities into rho_M=A(p) rho_N B(i). The finite-free inverse
identities (lemma-weil-pbc-projection-formula-finite-free), followed by i then p
being the identity, give both inverse equations. The forward arrow is intrinsic:
its defining adjunct uses no splitting. Repeat the inverse calculation for any
second package. Uniqueness of the inverse of the same forward arrow gives equality
of the inverse arrows, hence equality of the ordered pairs. In degree zero the
finite total is the single-term formula of definition 1264, including rank zero. -/
theorem ringedProjectionFormula_projective_summand
    (M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (P P' : StrictPerfectCoefficientPackage ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R) ((HomologicalComplex.single (SheafOfModules.{u} ((sheafCompose JC
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (ComplexShape.up ℤ) 0).obj M)) :
    (ringedProjectionFormulaSummandArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF PR PS
      hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj E K hK repE M P).2
      ≫
        (ringedProjectionFormulaSummandArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF PR
      PS hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj E K hK repE M
      P).1 = 𝟙 _ ∧
    (ringedProjectionFormulaSummandArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF PR PS
      hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj E K hK repE M P).1
      ≫
        (ringedProjectionFormulaSummandArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF PR
      PS hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj E K hK repE M
      P).2 = 𝟙 _ ∧
    ringedProjectionFormulaSummandArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF PR PS
      hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj E K hK repE M P =
      ringedProjectionFormulaSummandArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF PR PS
      hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj E K hK repE M P'
      := sorry

end SheafOfModules
