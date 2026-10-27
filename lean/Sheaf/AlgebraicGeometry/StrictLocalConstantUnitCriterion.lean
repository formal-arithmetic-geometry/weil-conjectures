/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q39
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationRestriction
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Sheaf.AlgebraicGeometry.PointedEtaleStalk
public import Sheaf.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStalkFormula
import Sheaf.AlgebraicGeometry.PullbackConstantModule
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import Sheaf.AlgebraicGeometry.DerivedGeometricStalkConservative
import WeilConjectures.AlgebraicGeometry.ConstantModuleSectionCoefficients
import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison

/-! # Strict-local criterion for constant direct-image units

Source: Stacks Project, Tag 03Q9, theorem-higher-direct-images, and Tags 03PT, 03FD, 0D6J
(blueprint: lem-pur-strict-local-constant-unit-criterion).

The maps below specialize the existing adjunctions and localization comparisons. The theorem
specifies the strict-local restriction isomorphism on every pointed neighbourhood, then asserts
an equality of morphisms in the bounded below derived category, before taking cohomology.
-/

@[expose] public section

set_option autoImplicit false

universe u u'

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

open Scheme

section Coefficients

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]

/-- The degree-zero constant sheaf, using the recorded constant and single functors.
Source: Stacks 03Q9 (blueprint: lem-pur-strict-local-constant-unit-criterion). -/
noncomputable abbrev constantSheafSingle (T : Scheme.{u}) (B : A) :=
  (DerivedCategory.Plus.singleFunctor _ 0).obj ((constantSheaf T.smallEtaleTopology A).obj B)

/-- The ordinary derived unit, with its target identified by the canonical constant-pullback
isomorphism. Source: Stacks 03Q9, unit normalization
(blueprint: lem-pur-strict-local-constant-unit-criterion). -/
noncomputable def constantDerivedDirectImageUnit {Y X : Scheme.{u}} (f : Y ⟶ X) (B : A) :
    constantSheafSingle A X B ⟶
      (rightDerivedLowerStarPlus A f).obj (constantSheafSingle A Y B) :=
  (upperStarLowerStarAdjunction A f).derivedPlus.unit.app (constantSheafSingle A X B) ≫
    (rightDerivedLowerStarPlus A f).map
      (((upperStar A f).mapDerivedCategoryPlusSingleFunctor 0).hom.app _ ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map
          ((upperStarConstantSheafIso A f).hom.app B))

/-- The constants map into ordinary derived global sections, the derived unit of constants
and sections. Source: Stacks 03Q9, restriction construction
(blueprint: lem-pur-strict-local-constant-unit-criterion). -/
noncomputable def constantDerivedSectionsMap (T : Scheme.{u}) (B : A) :
    (DerivedCategory.Plus.singleFunctor A 0).obj B ⟶
      (Sheaf.Γ T.smallEtaleTopology A).rightDerivedFunctorPlus.obj
        (constantSheafSingle A T B) :=
  (constantSheafΓAdj T.smallEtaleTopology A).derivedPlus.unit.app
      ((DerivedCategory.Plus.singleFunctor A 0).obj B) ≫
    (Sheaf.Γ T.smallEtaleTopology A).rightDerivedFunctorPlus.map
      (((constantSheaf T.smallEtaleTopology A).mapDerivedCategoryPlusSingleFunctor 0).hom.app B)

end Coefficients

/-- The exact geometric stalk functor on bounded below abelian derived categories.
Source: Stacks 03PT (blueprint: lem-pur-strict-local-constant-unit-criterion). -/
noncomputable def constantUnitDerivedStalk {X : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :=
  haveI : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
    AB5OfSize_shrink.{u, u, u + 1, u + 1} _
  haveI := (Scheme.pointSmallEtale x).sheafFiber_additive (A := AddCommGrpCat.{u + 1})
  ((Scheme.pointSmallEtale x).sheafFiber (A := AddCommGrpCat.{u + 1})).mapDerivedCategoryPlus

/-- The degree-zero constant germ, transported through the exact stalk functor.
Source: Stacks 03PT and 03Q9
(blueprint: lem-pur-strict-local-constant-unit-criterion). -/
noncomputable def constantDerivedGeometricGerm {X : Scheme.{u}} (B : AddCommGrpCat.{u + 1})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj B ⟶
      (constantUnitDerivedStalk x).obj
        (constantSheafSingle AddCommGrpCat.{u + 1} X B) :=
  haveI : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
    AB5OfSize_shrink.{u, u, u + 1, u + 1} _
  haveI := (Scheme.pointSmallEtale x).sheafFiber_additive (A := AddCommGrpCat.{u + 1})
  (DerivedCategory.Plus.singleFunctor _ 0).map
      ((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj B)).app
        (Opposite.op (Scheme.Etale.mk (𝟙 X))) ≫
      (Scheme.pointSmallEtale x).toPresheafFiber (Scheme.Etale.mk (𝟙 X))
        (Over.homMk x (Category.comp_id x))
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj B).obj) ≫
    ((Scheme.pointSmallEtale x).sheafFiber.mapDerivedCategoryPlusSingleFunctor 0).inv.app _

/-- The canonical derived restriction: the specified germ restriction, exact sections on the
strict-local base, the base-change mate, Leray, and the canonical constant-pullback comparison.
The parameter `r` is specified on all representative germs in the theorem, rather than chosen
from an uncharacterized existence claim. Source: Stacks 03Q9, last proof paragraph
(blueprint: lem-pur-strict-local-constant-unit-criterion). -/
noncomputable def strictLocalConstantDerivedRestriction {Y X : Scheme.{u}} (f : Y ⟶ X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (r : (Scheme.pointSmallEtale x).sheafFiber (A := AddCommGrpCat.{u + 1}) ≅
      upperStar AddCommGrpCat.{u + 1} (Scheme.strictLocalizationToBase x) ⋙
        Sheaf.Γ (Scheme.strictLocalization x).smallEtaleTopology AddCommGrpCat.{u + 1})
    (B : AddCommGrpCat.{u + 1}) :
    (constantUnitDerivedStalk x).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
          (constantSheafSingle AddCommGrpCat.{u + 1} Y B)) ⟶
      (Sheaf.Γ (pullback f (Scheme.strictLocalizationToBase x)).smallEtaleTopology
        AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.obj
          (constantSheafSingle AddCommGrpCat.{u + 1}
            (pullback f (Scheme.strictLocalizationToBase x)) B) :=
  haveI : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
    AB5OfSize_shrink.{u, u, u + 1, u + 1} _
  haveI := (Scheme.pointSmallEtale x).sheafFiber_additive (A := AddCommGrpCat.{u + 1})
  haveI := strictHenselization_globalSections_preservesFiniteColimits x
  haveI := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
      (pullback.snd f (Scheme.strictLocalizationToBase x)))
  (Functor.mapDerivedCategoryPlusNatIso r).hom.app _ ≫
    (Functor.mapDerivedCategoryPlusCompIso
      (upperStar AddCommGrpCat.{u + 1} (Scheme.strictLocalizationToBase x))
      (Sheaf.Γ (Scheme.strictLocalization x).smallEtaleTopology AddCommGrpCat.{u + 1})).hom.app _ ≫
    (Sheaf.Γ (Scheme.strictLocalization x).smallEtaleTopology
      AddCommGrpCat.{u + 1}).mapDerivedCategoryPlus.map
      ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).derivedPlus
        (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
          (pullback.snd f (Scheme.strictLocalizationToBase x))).derivedPlus
        (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{u + 1}
          (IsPullback.of_hasPullback f (Scheme.strictLocalizationToBase x)).toCommSq).hom))
          |>.natTrans.app (constantSheafSingle AddCommGrpCat.{u + 1} Y B)) ≫
    (Sheaf.Γ (Scheme.strictLocalization x).smallEtaleTopology
      AddCommGrpCat.{u + 1}).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv.app _ ≫
    (Functor.rightDerivedFunctorPlusCompIso'
      (lowerStar AddCommGrpCat.{u + 1} (pullback.snd f (Scheme.strictLocalizationToBase x)))
      (Sheaf.Γ (Scheme.strictLocalization x).smallEtaleTopology AddCommGrpCat.{u + 1})
      (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1}
        (pullback.snd f (Scheme.strictLocalizationToBase x)))).hom.app _ ≫
    (Sheaf.Γ (pullback f (Scheme.strictLocalizationToBase x)).smallEtaleTopology
      AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map
      (((upperStar AddCommGrpCat.{u + 1}
        (pullback.fst f (Scheme.strictLocalizationToBase x))).mapDerivedCategoryPlusSingleFunctor
          0).hom.app _ ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map
          ((upperStarConstantSheafIso AddCommGrpCat.{u + 1}
            (pullback.fst f (Scheme.strictLocalizationToBase x))).hom.app B))

/-- Strict-local constants detect the ordinary derived constant-unit isomorphism, for both
abelian groups and fixed-ring modules, with equality of the actual derived stalk maps.
Source: Stacks 03Q9, 03PT, 03FD and 0D6J
(blueprint: lem-pur-strict-local-constant-unit-criterion).

Proof:
1. Finiteness of Λ supplies n > 0 killing 1 and hence B, so its constant sheaf is torsion.
Apply prop-weil-pbc-strict-henselization-stalk-formula to f and this sheaf. The canonical
constant-pullback comparison (lem-kun-pullback-constant) identifies the restricted coefficient
with B. The constant germ is invertible by lem-weil-pbc-constant-sheaf-geometric-stalk.
2. The germ restriction exists uniquely on each sheaf by its neighbourhood components;
naturality follows from this uniqueness. It is invertible by strict-local sections at the
closed geometric point. Derive it, apply the base-change mate and Leray. On an injective
resolution this is the restriction map of 03Q9. The unit sends b to the constant b on each
base-changed neighbourhood. Restriction and the constant-pullback comparison still send it
to b. Thus its composite with the constant germ is the constants map, as derived morphisms.
3. The hypothesis makes this composite invertible at every geometric point. Exactness of
stalks and lem-weil-pbc-derived-stalk-conservative imply that the abelian unit is invertible.
4. Forget scalars. lem-weil-pbc-constant-module-section-coefficients identifies the forgotten
constant sheaf; lem-weil-pbc-module-abelian-derived-direct-image-comparison identifies direct
images compatibly with units. Exact forgetting commutes with cohomology and reflects its
isomorphisms: the inverse of a bijective linear sheaf map is linear on sections. The derived
cohomology criterion lem-weil-pbc-derived-plus-iso-on-cohomology gives the module conclusion.
5. No property of X was used. If X is empty the stalk family is empty and conservativity
still applies. If B is zero all maps are isomorphisms; an empty strict-local fibre forces
B = 0 under the hypothesis at that point. -/
theorem strictLocal_constant_unit_criterion {Y X : Scheme.{u}} (f : Y ⟶ X)
    [QuasiCompact f] [QuasiSeparated f]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (B : ModuleCat.{u + 1} Λ) [Finite B]
    (h : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
      IsIso (constantDerivedSectionsMap AddCommGrpCat.{u + 1}
        (pullback f (Scheme.strictLocalizationToBase x))
          ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj B))) :
    IsIso (constantDerivedDirectImageUnit AddCommGrpCat.{u + 1} f
      ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj B)) ∧
    IsIso (constantDerivedDirectImageUnit (ModuleCat.{u + 1} Λ) f B) ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
      ∃ r : (Scheme.pointSmallEtale x).sheafFiber (A := AddCommGrpCat.{u + 1}) ≅
          upperStar AddCommGrpCat.{u + 1} (Scheme.strictLocalizationToBase x) ⋙
            Sheaf.Γ (Scheme.strictLocalization x).smallEtaleTopology AddCommGrpCat.{u + 1},
        (∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
          IsStrictHenselizationStalkRestriction x F (r.hom.app F)) ∧
        IsIso (strictLocalConstantDerivedRestriction f x r
          ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj B)) ∧
        constantDerivedGeometricGerm
            ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj B) x ≫
          (constantUnitDerivedStalk x).map
            (constantDerivedDirectImageUnit AddCommGrpCat.{u + 1} f
              ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj B)) ≫
          strictLocalConstantDerivedRestriction f x r
            ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj B) =
          constantDerivedSectionsMap AddCommGrpCat.{u + 1}
            (pullback f (Scheme.strictLocalizationToBase x))
              ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj B) := by
  sorry

end AlgebraicGeometry.Etale
