/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.AlgebraicGeometry.GeometricPointDerivedConstants
public import Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap
public import Sheaf.AlgebraicGeometry.PullbackConstantModule
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Unique
import Sheaf.AlgebraicGeometry.PointedEtaleStalk
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Derived sections over a geometric point, with adjunction normalization

Source: Stacks Project, sites-cohomology.tex, Tag 07A6, and etale-cohomology.tex,
Tags 04JQ and 0F0F (blueprint: lem-kun-geometric-point-derived-sections-adjunction).

The integer-module encoding and the actual stalk are those of the dependency
`GeometricPointDerivedConstants`. All derived inverse images and constants below are
termwise exact functors. The adjunctions are transported from the existing canonical
left-derived adjunctions through their canonical exact-functor identifications.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Register the additivity supplied by the normalized geometric-point equivalence.
Source: Stacks Tag 04JQ
(blueprint: lem-kun-geometric-point-derived-sections-adjunction). -/
noncomputable instance geometricPointSectionsStalkAdditive
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] : (geometricPointStalk Ω).Additive :=
  (Classical.choice (nonempty_geometricPointDerivedConstantsData Ω)).stalkAdditive

/-- The normalized constant/stalk adjunction, whose unit is the canonical constant germ.
Its counit is uniquely determined by that normalization, so this choice selects no
arbitrary map. Source: Stacks Tag 04JQ
(blueprint: lem-kun-geometric-point-derived-sections-adjunction). -/
noncomputable def geometricPointSectionsStalkAdjunction
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] :
    geometricPointConstants Ω ⊣ geometricPointStalk Ω :=
  (Classical.choice (nonempty_geometricPointDerivedConstantsData Ω)).adjunction

/-- The canonical constant-section adjunction with termwise derived constants on the left.
Source: Stacks Tag 07A6
(blueprint: lem-kun-geometric-point-derived-sections-adjunction). -/
noncomputable def geometricPointSectionsConstantAdjunction (Z : Scheme.{u}) :
    (constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).mapDerivedCategory ⊣
      rightDerivedGlobalSections (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) Z :=
  (derivedConstantGlobalSectionsAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) Z).ofNatIsoLeft
    (constantSheaf Z.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).leftDerivedFunctorIsoMapDerivedCategory

/-- The canonical derived inverse/direct-image adjunction, with the exact termwise inverse
image on the left. Source: Stacks Tag 07A6
(blueprint: lem-kun-geometric-point-derived-sections-adjunction). -/
noncomputable def geometricPointSectionsImageAdjunction
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] {Z : Scheme.{u}} (h : Z ⟶ Spec (.of Ω)) :
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).mapDerivedCategory ⊣
      (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).rightDerivedFunctor :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).ofNatIsoLeft
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).leftDerivedFunctorIsoMapDerivedCategory

/-- The canonical pullback-of-constants comparison, descended termwise.
Source: Stacks Tags 07A6 and 0F0F, and `lem-kun-pullback-constant`
(blueprint: lem-kun-geometric-point-derived-sections-adjunction). -/
noncomputable def geometricPointSectionsConstantsIso
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] {Z : Scheme.{u}} (h : Z ⟶ Spec (.of Ω)) :
    (geometricPointConstants Ω).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).mapDerivedCategory ≅
      (constantSheaf Z.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (geometricPointConstants Ω)
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h)).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h)

/-- The specified natural isomorphism of right adjoints. It is constructed by composing
constant/stalk with inverse/direct image, transporting the left adjoint through the
canonical constants comparison, and applying uniqueness of right adjoints.
Source: Stacks Tag 07A6 and the pushforward-composition proof following it
(blueprint: lem-kun-geometric-point-derived-sections-adjunction). -/
noncomputable def geometricPointDerivedSectionsIso
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] {Z : Scheme.{u}} (h : Z ⟶ Spec (.of Ω)) :
    (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).rightDerivedFunctor ⋙
        (geometricPointStalk Ω).mapDerivedCategory ≅
      rightDerivedGlobalSections (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) Z :=
  (((geometricPointSectionsStalkAdjunction Ω).mapDerivedCategoryAdjunction.comp
      (geometricPointSectionsImageAdjunction Ω h)).ofNatIsoLeft
        (geometricPointSectionsConstantsIso Ω h)).rightAdjointUniq
    (geometricPointSectionsConstantAdjunction Z)

/-- The actual global-section-to-germ map at the identity geometric point. The lift
only reindexes the same pointed-neighbourhood colimit, as in the dependency's stalk.
Source: Stacks Tags 040R and 04JQ
(blueprint: lem-kun-geometric-point-derived-sections-adjunction). -/
noncomputable def geometricPointSectionsGerm
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (G : Sheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) :
    (Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).obj G ⟶ (geometricPointStalk Ω).obj G :=
  (Sheaf.ΓNatIsoSheafSections (Spec (.of Ω)).smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
      (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale (Spec (.of Ω)))).hom.app G ≫
    ((Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{u + 1}).toPresheafFiber
      (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))
      (ULift.up (Over.homMk (𝟙 (Spec (.of Ω))) (Category.comp_id _))) G.obj

/-- The augmentation identification `H⁰(S_D Rh_* G[0]) ≅ S(h_* G)`.
It uses exactness of the stalk and the canonical zeroth-right-derived comparison.
Source: Stacks Tags 05TD and 04JQ
(blueprint: lem-kun-geometric-point-derived-sections-adjunction). -/
noncomputable def geometricPointSectionsImageH0Iso
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] {Z : Scheme.{u}} (h : Z ⟶ Spec (.of Ω))
    (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) 0).obj
        (((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).rightDerivedFunctor ⋙
          (geometricPointStalk Ω).mapDerivedCategory).obj
            ((DerivedCategory.singleFunctor _ 0).obj G)) ≅
      (geometricPointStalk Ω).obj ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).obj G) :=
  ((geometricPointStalk Ω).mapDerivedCategoryHomologyFunctorIso 0).symm.app _ ≪≫
    (geometricPointStalk Ω).mapIso
      ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h
        |>.homologyRightDerivedFunctorObjSingleFunctorIso G 0) ≪≫
        (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).rightDerivedZeroIsoSelf.app G)

/-- The canonical augmentation identification `H⁰(RΓ_Z G[0]) ≅ Γ_Z G`.
Source: Stacks Tag 05TD
(blueprint: lem-kun-geometric-point-derived-sections-adjunction). -/
noncomputable def geometricPointSectionsGlobalH0Iso (Z : Scheme.{u})
    (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) 0).obj
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) Z).obj
          ((DerivedCategory.singleFunctor _ 0).obj G)) ≅
      (Sheaf.Γ Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).obj G :=
  (Sheaf.Γ Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
    |>.homologyRightDerivedFunctorObjSingleFunctorIso G 0) ≪≫
    (Sheaf.Γ Z.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).rightDerivedZeroIsoSelf.app G

/-- The natural right-adjoint comparison has the specified counit identity and is inverse
to the global-section-to-germ map in degree zero. Source: Stacks Tag 07A6, the subsequent
pushforward-composition proof, and Tags 04JQ, 0F0F and 05TD
(blueprint: lem-kun-geometric-point-derived-sections-adjunction).

Proof:
1. Compose the normalized constant/stalk adjunction of
   `lem-kun-geometric-point-derived-constants` with the canonical derived image adjunction
   of `def-kun-projection-formula-map`. Its counit is the image counit after inverse image
   of the stalk-equivalence counit.
2. Transport its left adjoint through `lem-kun-pullback-constant`. The transported counit
   is this composite preceded by inverse to the constants comparison.
3. Compare with `def-kun-constant-projection-morphism` by `det-sp-unique-right-adjoint`.
   Its counit equation, precomposed with the constants comparison, is the first clause.
4. The ordinary constant-section and normalized constant/stalk Hom bijections identify
   Hom(A, Γ_s H) with Hom(A, SH). The composite sends a map v to ρ_H after v:
   the constant-section adjunction extends a section by restriction, and the normalized
   point unit sends a constant to its germ. This is the definition of ρ_H from
   `def-weil-pbc-geometric-stalks` and `def-weil-pbc-global-sections-functor`.
   Taking A to be the integer module shows ρ_H bijective, hence invertible.
   Its naturality follows from the germ-map naturality. Finally
   `def-weil-pbc-direct-image` identifies sections of h_*G with sections of G on Z.
5. Choose a K-injective representative by `prop-weil-pbc-kinjective-resolutions-exist`.
   The recipes of `def-kun-projection-formula-map` and `def-kun-rgamma-unbounded`, together
   with `lem-weil-pbc-termwise-adjunction-homotopy`,
   `lem-weil-pbc-right-adjoint-preserves-kinjective` and
   `lem-weil-pbc-kinjective-hom-derived`, compute all counits by ordinary evaluation.
6. In each degree inverse to the germ map takes a stalk element to its unique global
   section. The two sides of the counit identity evaluate that same section after pulling
   back to Z. Equality on constant sections extends to their sheafifications by
   `def-kun-constant-sheaf`. Uniqueness identifies this chain isomorphism with β.
7. For G[0], use `lem-weil-pbc-site-sheaves-enough-injectives`,
   `lem-weil-pbc-left-exact-injective-resolution-degree-zero` and
   `lem-weil-pbc-bounded-below-injectives-kinjective` to choose a nonnegative injective
   resolution. Left exactness of h_* and Γ (the latter by
   `lem-weil-pbc-right-adjoint-preserves-limits`) identifies degree-zero kernels with
   h_*G and Γ_Z G; exactness of the stalk identifies the remaining kernel with S(h_*G).
   Naturality of the germ map with respect to the augmentation then gives the second
   clause. This resolution is used only for the normalization; β applies to all unbounded E.
-/
theorem geometricPoint_derivedSections_adjunction
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] {Z : Scheme.{u}} (h : Z ⟶ Spec (.of Ω)) :
    (∀ E : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))),
      (geometricPointSectionsConstantsIso Ω h).hom.app
          (((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).rightDerivedFunctor ⋙
            (geometricPointStalk Ω).mapDerivedCategory).obj E) ≫
        (constantSheaf Z.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).mapDerivedCategory.map
            ((geometricPointDerivedSectionsIso Ω h).hom.app E) ≫
        (geometricPointSectionsConstantAdjunction Z).counit.app E =
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).mapDerivedCategory.map
          ((geometricPointSectionsStalkAdjunction Ω).mapDerivedCategoryAdjunction.counit.app
            ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).rightDerivedFunctor.obj E)) ≫
        (geometricPointSectionsImageAdjunction Ω h).counit.app E) ∧
    (∀ G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)),
      geometricPointSectionsGerm Ω ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).obj G) ≫
        (geometricPointSectionsImageH0Iso Ω h G).inv ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) 0).map
          ((geometricPointDerivedSectionsIso Ω h).hom.app
            ((DerivedCategory.singleFunctor _ 0).obj G)) ≫
        (geometricPointSectionsGlobalH0Iso Z G).hom =
      (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).hom.app G) := by
  sorry

end AlgebraicGeometry.Etale
