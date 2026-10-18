/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.Paper.ProjectionFormulaArrows
public import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.Algebra.Homology.KFlatResolutionGeneral
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Paper.RingedTopoiCanonicalTensorPullback
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
public import Sheaf.Algebra.Homology.KFlatCoefficientUniverse
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Paper.ProEtaleProjectionFormulaArrows
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

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
1. Use the K-injective representative K and the complexes A=h_*K, C=Tot(A tensor F),
J=Tot(K tensor h^*F), B=h_*J of def-weil-pbc-projection-formula-arrows. Since the
only coefficient degree is -a, C^n=(h_*K^{n+a})^N and B^n=h_*((K^{n+a})^N).
The coefficient differential vanishes (def-pc-tensor-complex-sheaves).
2. Pullback sends the coordinate splitting and the unit R to those of S. The ordinary
counit mate t has each coordinate equal to the corresponding projection, by
lem-weil-pbc-ringed-topoi-module-pullback-tensor and
lem-weil-pbc-termwise-adjunction-homotopy. Finite products are preserved by the right
adjoint (lem-weil-pbc-right-adjoint-preserves-limits), so q is its inverse, also for N=0.
3. Naturality gives the chain equations for t and q, with no coefficient-differential
term or extra sign. Thus they are inverse chain maps in every degree.
4. Resolve A by a K-flat complex with flat terms (lem-pc-kflat-resolution). Tensoring
with this single finite-free complex preserves quasi-isomorphisms and K-flatness
(def-pc-kflat-complex). The canonical tensor comparison of
lem-weil-pbc-ringed-topoi-derived-tensor-pullback and the representative adjunction
formula of lem-pc-pre-derived-adjoint-functors-general identify Q(t) with the specified
counit mate pi; cancel the resolution quasi-isomorphism.
5. The summand formula of def-weil-pbc-projection-formula-arrows identifies Q(q) with
rho. Localize both chain inverse identities. In diagrammatic order the first conjunct
is rho after pi, and the second is pi after rho. -/
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
        E K hK repE F P hbounded).1 = 𝟙 _ := sorry

end SheafOfModules
