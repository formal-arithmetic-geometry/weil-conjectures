/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF maintenance
-/
module

public import Sheaf.Paper.ProEtaleCanonicalTensorPullback
public import Sheaf.Paper.RingedTopoiCanonicalTensorComparisonOfUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatTelescopeClosure
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Paper.RingedTopoiDerivedPullback
import Sheaf.Paper.RingedTopoiTensorComparisonConstruction

/-!
# Canonical tensor pullback with independent site universes

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 0G7E;
Modules on Sites, Tag 03EL
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).

This is the general canonical representative interface, with a site-object universe s and an
independent site-morphism universe h. Rings and modules live in max s h, as in the
published K-flat interface. Both sites retain their actual Hom universe. The ring map is arbitrary,
  including coefficient quotients, and
the geometric morphism can be the etale-to-pro-etale comparison. The pure-tensor,
unit and signed total-complex normalizations are retained verbatim. Public imports
retain both earlier interfaces for existing callers.
-/

@[expose] public section

set_option autoImplicit false

universe s h w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules.CanonicalTensorPullbackOfUniverses

set_option backward.isDefEq.respectTransparency false

set_option synthInstance.maxSize 2048 in
set_option maxHeartbeats 800000 in
-- Elaborate the full two-variable representative square.
/-- Canonical derived comparison, uniquely characterized on K-flat flat-term representatives.
Source: Stacks 07A4 and 0G7E
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
Proof: resolve both inputs by K-flat flat-term complexes; pullback preserves that class
by 0G7E. Their total tensor is K-flat by reassociating an acyclic test tensor and applying
K-flatness twice, and has flat terms by tensor-flatness and countable flat sums.
The left-derived comparison computes pullback on these representatives. Compose it
with the inverse image of the explicit chain comparison k.totalIso and rS. The displayed
square records exactly this construction relative to rR. Naturality of the summand
comparisons handles both differentials and their signs. Two-variable tensor descent
extends the square to all derived objects and makes its extension unique. The ordinary
unit normalization is canonicalRingedTensorComparison_unit, forced by k.pure. -/
theorem ringedTopoiCanonicalDerivedTensorPullback
    {C D : Type s} [Category.{h} C] [Category.{h} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{max s h}} {S RI : Sheaf JD CommRingCat.{max s h}}
    (uInv : Sheaf JC (Type (max s h)) ⥤ Sheaf JD (Type (max s h)))
    (uPush : Sheaf JD (Type (max s h)) ⥤ Sheaf JC (Type (max s h)))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (uStar : SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R) ⥤
      SheafOfModules.{max s h}
      ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S))
    (hobj : ∀ M : SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R), uStar.obj M =
        changeOfRings
        c (I.modules.obj M))
    (hmap : ∀ {M N : SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R)} (a : M ⟶ N),
        uStar.map a =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫
        eqToHom (hobj N).symm)
    [uStar.Additive]
    [HasDerivedCategory.{w} (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R))]
    [HasDerivedCategory.{w} (SheafOfModules.{max s h}
      ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S))]
    (LF : DerivedCategory (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R)) ⥤ DerivedCategory
      (SheafOfModules.{max s h}
      ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S)))
    (epsilon : DerivedCategory.Qh ⋙ LF ⟶
      uStar.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hLF : LF.IsLeftDerivedFunctor epsilon
      (HomotopyCategory.quasiIso (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R)) (ComplexShape.up
        ℤ)))
    (PR : ObjectProperty (CochainComplex (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R)) ℤ))
    (PS : ObjectProperty (CochainComplex (SheafOfModules.{max s h}
      ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S)) ℤ))
    (hPR : ∀ P, PR P ↔ P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n))
    (hPS : ∀ P, PS P ↔ P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, IsFlatOnSite (J := JD) (R := S) (P.X n))
    (TR : (DerivedCategory (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R))) ×
        (DerivedCategory
      (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R))) ⥤
        DerivedCategory
      (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R)))
    (TS : (DerivedCategory (SheafOfModules.{max s h}
      ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S))) ×
        (DerivedCategory
      (SheafOfModules.{max s h}
      ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S))) ⥤
        DerivedCategory
      (SheafOfModules.{max s h}
      ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S)))
    (rR : (PR.ι.prod PR.ι) ⋙ Functor.uncurry.obj
        ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R)) _
          (SheafOfModules.monoidalCategory R)).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
      ((PR.ι ⋙ DerivedCategory.Q).prod (PR.ι ⋙ DerivedCategory.Q)) ⋙ TR)
    (rS : (PS.ι.prod PS.ι) ⋙ Functor.uncurry.obj
        ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{max s h}
      ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S)) _
          (SheafOfModules.monoidalCategory S)).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
      ((PS.ι ⋙ DerivedCategory.Q).prod (PS.ι ⋙ DerivedCategory.Q)) ⋙ TS)
    (k : CanonicalRingedTensorComparison R S RI uInv I c uStar hobj)
    (V : SheafOfModules.{max s h} ((sheafCompose JD (forget₂ CommRingCat.{max s h}
      RingCat.{max s h})).obj S) ⥤
      SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
        RingCat.{max s h})).obj R)) (am :
      uStar ⊣ V) :
    (∀ P : CochainComplex (SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
      RingCat.{max s h})).obj R)) ℤ,
      P.IsAcyclicTensorKFlat → (∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n)) →
        CochainComplex.IsAcyclicTensorKFlat ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ∧
          ∀ n : ℤ,
            IsFlatOnSite (J := JD) (R := S)
              (((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X n)) ∧
    ∃! alpha : TR ⋙ LF ≅ (LF.prod LF) ⋙ TS,
      ∀ (P Q : CochainComplex (SheafOfModules.{max s h} ((sheafCompose JC (forget₂
        CommRingCat.{max s h}
      RingCat.{max s h})).obj R)) ℤ) (hp : PR P) (hq : PR Q),
        ∃ (hp' : PS ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
          (hq' : PS ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)),
          LF.map (rR.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
              alpha.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
                TS.map (CategoryTheory.Prod.mkHom
                  (derivedPullbackComplexComparison uStar LF epsilon P)
                  (derivedPullbackComplexComparison uStar LF epsilon Q)) =
            derivedPullbackComplexComparison uStar LF epsilon
              (CochainComplex.mapBifunctor P Q
                (@curriedTensor (SheafOfModules.{max s h} ((sheafCompose JC (forget₂
                  CommRingCat.{max s h}
      RingCat.{max s h})).obj R)) _ (monoidalCategory R))) ≫
              (DerivedCategory.Q.mapIso
                (k.totalIso R S RI uInv I c uStar hobj V am P Q)).inv ≫
                  rS.hom.app
                    (⟨(uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj P, hp'⟩,
                      ⟨(uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q, hq'⟩) := sorry

set_option synthInstance.maxSize 2048 in
set_option maxHeartbeats 800000 in
-- Keep both tensor representative interfaces explicit.
/-- The canonical derived comparison selected by its unique representative characterization.
Source: Stacks 07A4 (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
The theorem specifies the natural isomorphism uniquely, so only its proof is postponed. -/
noncomputable def ringedTopoiCanonicalDerivedTensorComparison
    {C D : Type s} [Category.{h} C] [Category.{h} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{max s h}} {S RI : Sheaf JD CommRingCat.{max s h}}
    (uInv : Sheaf JC (Type (max s h)) ⥤ Sheaf JD (Type (max s h)))
    (uPush : Sheaf JD (Type (max s h)) ⥤ Sheaf JC (Type (max s h)))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (uStar : SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R) ⥤
      SheafOfModules.{max s h}
      ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S))
    (hobj : ∀ M : SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R), uStar.obj M =
        changeOfRings
        c (I.modules.obj M))
    (hmap : ∀ {M N : SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R)} (a : M ⟶ N),
        uStar.map a =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫
        eqToHom (hobj N).symm)
    [uStar.Additive]
    [HasDerivedCategory.{w} (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R))]
    [HasDerivedCategory.{w} (SheafOfModules.{max s h}
      ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S))]
    (LF : DerivedCategory (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R)) ⥤ DerivedCategory
      (SheafOfModules.{max s h}
      ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S)))
    (epsilon : DerivedCategory.Qh ⋙ LF ⟶
      uStar.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hLF : LF.IsLeftDerivedFunctor epsilon
      (HomotopyCategory.quasiIso (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R)) (ComplexShape.up
        ℤ)))
    (PR : ObjectProperty (CochainComplex (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R)) ℤ))
    (PS : ObjectProperty (CochainComplex (SheafOfModules.{max s h}
      ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S)) ℤ))
    (hPR : ∀ P, PR P ↔ P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n))
    (hPS : ∀ P, PS P ↔ P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, IsFlatOnSite (J := JD) (R := S) (P.X n))
    (TR : (DerivedCategory (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R))) ×
        (DerivedCategory
      (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R))) ⥤
        DerivedCategory
      (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R)))
    (TS : (DerivedCategory (SheafOfModules.{max s h}
      ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S))) ×
        (DerivedCategory
      (SheafOfModules.{max s h}
      ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S))) ⥤
        DerivedCategory
      (SheafOfModules.{max s h}
      ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S)))
    (rR : (PR.ι.prod PR.ι) ⋙ Functor.uncurry.obj
        ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R)) _
          (SheafOfModules.monoidalCategory R)).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
      ((PR.ι ⋙ DerivedCategory.Q).prod (PR.ι ⋙ DerivedCategory.Q)) ⋙ TR)
    (rS : (PS.ι.prod PS.ι) ⋙ Functor.uncurry.obj
        ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{max s h}
      ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S)) _
          (SheafOfModules.monoidalCategory S)).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
      ((PS.ι ⋙ DerivedCategory.Q).prod (PS.ι ⋙ DerivedCategory.Q)) ⋙ TS)
    (k : CanonicalRingedTensorComparison R S RI uInv I c uStar hobj)
    (V : SheafOfModules.{max s h} ((sheafCompose JD (forget₂ CommRingCat.{max s h}
      RingCat.{max s h})).obj S) ⥤
      SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
        RingCat.{max s h})).obj R)) (am :
      uStar ⊣ V) :
    TR ⋙ LF ≅ (LF.prod LF) ⋙ TS :=
  Classical.choose (ringedTopoiCanonicalDerivedTensorPullback uInv uPush adj I c uStar
    hobj hmap LF epsilon hLF PR PS hPR hPS TR TS rR rS k V am).2.exists

end SheafOfModules.CanonicalTensorPullbackOfUniverses
