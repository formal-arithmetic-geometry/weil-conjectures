/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import WeilConjectures.SixFunctors.Finite.GlobalSections
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

import Sheaf.TraceFormula.ModuleDerivedRestrictionResolution
import WeilConjectures.SixFunctors.Finite.Exact
import Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-! # Derived sections through finite pushforward for module sheaves

Source: Stacks Project, Étale Cohomology, Tag 03QP; Derived Categories, Tag 015M;
Sites, section-pullback (blueprint: lem-trf-derived-sections-finite-pushforward-modules).

The comparison is the published finite-pushforward Leray natural isomorphism.

## Main definitions and statement

* `finitePushforwardDerivedMate`: the canonical counit mate of the composition comparison.
* `finitePushforwardSectionsUnit`: the canonical comparison from termwise to derived sections.
* `derivedSectionsFinitePushforwardModules`: exactness, injectives, normalization on every
  bounded-below injective resolution, and compatibility with arbitrary pullback.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The canonical derived mate of the inverse-image composition comparison in a square
whose vertical maps are finite. No invertibility of the mate is assumed or used.

Source: Stacks Project, Sites, section-pullback; Étale Cohomology, Tag 03QP
(blueprint: lem-trf-derived-sections-finite-pushforward-modules). -/
noncomputable def finitePushforwardDerivedMate
    (Λ : Type (u + 1)) [CommRing Λ] {Z' Z Y' Y : Scheme.{u}}
    {g : Z' ⟶ Z} {p' : Z' ⟶ Y'} {p : Z ⟶ Y} {h : Y' ⟶ Y}
    [IsFinite p] [IsFinite p'] (sq : CommSq g p' p h) :
    (lowerStar (ModuleCat.{u + 1} Λ) p).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} Λ) h).mapDerivedCategory ⟶
      (upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategory ⋙
        (lowerStar (ModuleCat.{u + 1} Λ) p').mapDerivedCategory :=
  (mateEquiv
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).mapDerivedCategoryAdjunction
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p').mapDerivedCategoryAdjunction
    (TwoSquare.mk _ _ _ _
      ((Functor.mapDerivedCategoryCompIso
          (upperStar (ModuleCat.{u + 1} Λ) h)
          (upperStar (ModuleCat.{u + 1} Λ) p')).symm ≪≫
        Functor.mapDerivedCategoryNatIso (squareUpperStarIso (ModuleCat.{u + 1} Λ) sq) ≪≫
        Functor.mapDerivedCategoryCompIso
          (upperStar (ModuleCat.{u + 1} Λ) p)
          (upperStar (ModuleCat.{u + 1} Λ) g)).hom)).natTrans

/-- The canonical map from termwise sections to right-derived sections of a complex.
On a bounded-below complex of injectives it is an isomorphism, whose inverse computes
right-derived sections. This is the derived-functor unit transported from the homotopy
category, without making any choice of a resolution.

Source: Stacks Project, Derived Categories, Tag 015M
(blueprint: lem-trf-derived-sections-finite-pushforward-modules). -/
noncomputable def finitePushforwardSectionsUnit
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})
    (L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) :
    DerivedCategory.Q.obj
        (((Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L) ⟶
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj
        (DerivedCategory.Q.obj L) :=
  (DerivedCategory.quotientCompQhIso (ModuleCat.{u + 1} Λ)).inv.app
      (((Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L) ≫
    (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj L) ≫
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).map
      ((DerivedCategory.quotientCompQhIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))).hom.app L)

/-- Finite direct image is exact, preserves injectives, and its canonical Leray comparison
commutes with the canonical restriction and base-change mate.

Source: Stacks Project, Étale Cohomology, Tag 03QP; Derived Categories, Tag 015M
(blueprint: lem-trf-derived-sections-finite-pushforward-modules).

Proof (postponed in stage 2).

1. By lemma-weil-pbc-finite-direct-image-exact, finite direct image on abelian sheaves is
exact. The module direct image has that underlying functor by
lem-weil-pbc-module-direct-image-left-exact. Scalar forgetting is faithful and preserves
kernels and cokernels by lem-weil-pbc-module-sheaves-colimits-forgetful, hence reflects
exactness. Thus the module direct image preserves finite limits and colimits.

2. Exact inverse image is left adjoint to direct image by
prop-weil-pbc-inverse-image-modules-exact, so lem-sp-right-adjoint-preserves-injectives
applies. Choose a bounded-below injective resolution using
lem-weil-pbc-module-sheaves-enough-injectives and lem-weil-pbc-dplus-injective-representative.
The comparison is a module-linear quasi-isomorphism by lem-weil-pbc-kinjective-hom-derived.
Exact direct image preserves that quasi-isomorphism and the lower bound, and its terms are
injective. The right-derived-functor units are isomorphisms on these complexes by
def-kun-rgamma-unbounded and lem-weil-pbc-right-derived-plus-injective. The termwise
identification of sections is an isomorphism of complexes with identical differentials.
This computes the published Leray comparison and gives the displayed normalization.
Uniqueness of homotopy classes into injective representatives
(lem-weil-pbc-kinjective-hom-derived) gives independence of the resolution and naturality.

3. By lem-trf-finite-radicial-basechange, the same applies to the base-changed finite map.
Exact inverse image preserves the lower bound. Choose an injective resolution of the
pulled-back complex and apply finite direct image to it; this supplies module-complex
models of all four corners, without forgetting to abelian-derived categories.

4. Use lem-weil-pbc-inverse-image-composition and its unit normalization to form the
counit mate. Naturality makes the composition comparison commute with constant scalar
endomorphisms. Sections of the constant ring sheaf are locally constant scalars
(def-weil-pbc-constant-sheaf), so the comparison, units and counits are module-linear.
Faithful scalar forgetting reflects their equations. Exact localization gives precisely
`finitePushforwardDerivedMate`, not a freely chosen transformation.

5. For a section s of p_*F, write its transpose as epsilon_p composed with p-inverse(s).
The transpose of its pullback along h followed by the mate is g-inverse of this expression,
by the mate's counit formula and the composition unit equation. This is the pullback along
g of the original section on Z. Thus taking sections of the mate after the h-unit is the
g-unit, under the two section identifications. Applying this degreewise to an injective
resolution gives an equality of module-linear chain maps, since all maps are natural.

6. Apply lem-trf-module-derived-restriction-resolution to h with source p_*L and target
the direct image of an injective resolution of g-inverse(L), and then to g with source L
and that resolution as target. It identifies the two vertical arrows with the chain maps
of step 5 followed by their resolution comparisons. The horizontal arrows are those of
step 2. Their composites are equal by step 5 and the termwise section identification.
Naturality of the mate and exactness transport this equality back from L to M. This proves
the displayed square without asserting that the mate is invertible. -/
theorem derivedSectionsFinitePushforwardModules
    (Λ : Type (u + 1)) [CommRing Λ] {Z Y : Scheme.{u}}
    (p : Z ⟶ Y) [IsFinite p]
    (M : CochainComplex (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (a : ℤ) [M.IsStrictlyGE a] :
    PreservesFiniteLimits (lowerStar (ModuleCat.{u + 1} Λ) p) ∧
    PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} Λ) p) ∧
    (lowerStar (ModuleCat.{u + 1} Λ) p).PreservesInjectiveObjects ∧
    (∀ (L : CochainComplex (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
      (b : ℤ) [L.IsStrictlyGE b] [∀ n : ℤ, Injective (L.X n)]
      (i : M ⟶ L) [QuasiIso i],
      QuasiIso (((lowerStar (ModuleCat.{u + 1} Λ) p).mapHomologicalComplex
        (ComplexShape.up ℤ)).map i) ∧
      CochainComplex.IsStrictlyGE
        (((lowerStar (ModuleCat.{u + 1} Λ) p).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L) b ∧
      (∀ n : ℤ, Injective ((lowerStar (ModuleCat.{u + 1} Λ) p).obj (L.X n))) ∧
      IsIso (finitePushforwardSectionsUnit Λ Z L) ∧
      IsIso (finitePushforwardSectionsUnit Λ Y
        (((lowerStar (ModuleCat.{u + 1} Λ) p).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L)) ∧
      finitePushforwardSectionsUnit Λ Y
          (((lowerStar (ModuleCat.{u + 1} Λ) p).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj L) ≫
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).map
          ((lowerStar (ModuleCat.{u + 1} Λ) p).mapDerivedCategoryFactors.inv.app L ≫
            (lowerStar (ModuleCat.{u + 1} Λ) p).mapDerivedCategory.map
              (inv (DerivedCategory.Q.map i))) ≫
        (mapDerivedCategoryLowerStarCompRightDerivedGlobalSectionsIso Λ p).hom.app
          (DerivedCategory.Q.obj M) ≫
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Z).map
          (DerivedCategory.Q.map i) =
      DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso
            (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ) p)
            (ComplexShape.up ℤ)).hom.app L) ≫
        finitePushforwardSectionsUnit Λ Z L) ∧
    ∀ (Y' : Scheme.{u}) (h : Y' ⟶ Y),
      (mapDerivedCategoryLowerStarCompRightDerivedGlobalSectionsIso Λ p).hom.app
          (DerivedCategory.Q.obj M) ≫
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Z).map
          ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
            (pullback.snd h p)).unit.app (DerivedCategory.Q.obj M)) ≫
        (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          (ModuleCat.{u + 1} Λ) (pullback.snd h p)).hom.app _ =
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).map
          ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).unit.app
            ((lowerStar (ModuleCat.{u + 1} Λ) p).mapDerivedCategory.obj
              (DerivedCategory.Q.obj M))) ≫
        (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          (ModuleCat.{u + 1} Λ) h).hom.app _ ≫
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y').map
          ((finitePushforwardDerivedMate Λ
            (⟨pullback.condition.symm⟩ :
              CommSq (pullback.snd h p) (pullback.fst h p) p h)).app
              (DerivedCategory.Q.obj M)) ≫
        (mapDerivedCategoryLowerStarCompRightDerivedGlobalSectionsIso
          Λ (pullback.fst h p)).hom.app _ := by
  sorry

end AlgebraicGeometry.Etale
