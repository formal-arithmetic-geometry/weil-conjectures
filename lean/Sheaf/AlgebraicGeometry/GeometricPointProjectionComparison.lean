/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.AlgebraicGeometry.GeometricPointDerivedConstants
public import Sheaf.AlgebraicGeometry.GeometricPointDerivedSectionsAdjunction
public import Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import Sheaf.Paper.RingedProjectionTensorComposition

/-! # Geometric-point projection comparison

Source: Stacks Project, `sites-cohomology.tex`, Tag 0B56, and
`etale-cohomology.tex`, Tags 07A4 and 0F0F
(blueprint: lem-kun-geometric-point-projection-comparison).

The theorem records the compatibility of the canonical derived projection map with
geometric-stalk evaluation and the constant-section projection map. The vertical maps
are the normalized monoidal comparison and the specified right-adjoint comparison.
-/

@[expose] public section

set_option autoImplicit false

universe u u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

/-- Integer modules in the coefficient universe fixed by the dependency equivalence.
The `ULift` is the existing integer-module encoding of ordinary abelian groups.
Source: Stacks Tag 0F0F (blueprint: lem-kun-geometric-point-projection-comparison). -/
abbrev GeometricPointIntegerModule := ModuleCat.{u + 1} (ULift.{u + 1} ℤ)
/-- The normalized strong monoidal stalk structure supplied by the point equivalence.
Source: Stacks Tags 04JQ and 0F0F
(blueprint: lem-kun-geometric-point-projection-comparison). -/
noncomputable instance geometricPointDerivedStalkMonoidal
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] :
    (geometricPointStalk Ω).mapDerivedCategory.Monoidal :=
  (Classical.choice (nonempty_geometricPointDerivedConstantsData Ω)).derivedStalkMonoidal

/-- The specified derived constant-germ unit is invertible by the point equivalence.
Source: Stacks Tags 04JQ and 0F0F
(blueprint: lem-kun-geometric-point-projection-comparison). -/
noncomputable instance geometricPointDerivedSectionsStalkUnitIsIso
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] :
    IsIso ((geometricPointSectionsStalkAdjunction Ω).mapDerivedCategoryAdjunction.unit) :=
  (Classical.choice (nonempty_geometricPointDerivedConstantsData Ω)).derivedUnitIsIso

/-- The canonical pullback-of-constants comparison, transported through the canonical
identifications of the left derived exact functors with their termwise derived functors.
Its component is the node's `γ`, expressed in the normalization of the projection maps.
Source: Stacks Tags 07A4, 07A6 and 0F0F
(blueprint: lem-kun-geometric-point-projection-comparison). -/
noncomputable def geometricPointProjectionCoefficientIso
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] {Z : Scheme.{u}}
    (h : Z ⟶ Spec (.of Ω)) :
    (geometricPointConstants Ω).mapDerivedCategory ⋙
        (upperStar GeometricPointIntegerModule h).leftDerivedFunctor ≅
      (constantSheaf Z.smallEtaleTopology GeometricPointIntegerModule).leftDerivedFunctor :=
  Functor.isoWhiskerLeft (geometricPointConstants Ω).mapDerivedCategory
      (upperStar GeometricPointIntegerModule h).leftDerivedFunctorIsoMapDerivedCategory ≪≫
    geometricPointSectionsConstantsIso Ω h ≪≫
    (constantSheaf Z.smallEtaleTopology
      GeometricPointIntegerModule).leftDerivedFunctorIsoMapDerivedCategory.symm

/-- The equation of the geometric-point projection comparison square, written with
abstract functors so that specialization does not expand tensor localization objects.
`F,H` are inverse/direct image, `S,K` are stalk/constants, and `L,R` are constants/sections.
`β,γ,unit` are the fixed right-adjoint comparison, coefficient comparison and germ unit.
`P,p` are the two projection transformations. The conclusion quantifies over every `E,M`;
its left side is the top arrow followed by the right vertical map, and its right side
is the normalized monoidal left vertical map followed by the bottom projection arrow.
This definition assumes no commutativity, invertibility or projection-formula property.
Source: Stacks Tags 0B56 and 0F0F
(blueprint: lem-kun-geometric-point-projection-comparison). -/
noncomputable def GeometricPointProjectionSquare
    {C : Type u₁} {A : Type u₂} {D : Type u₃}
    [Category.{v₁} C] [Category.{v₂} A] [Category.{v₃} D]
    [MonoidalCategory C] [MonoidalCategory A] [MonoidalCategory D]
    (F : A ⥤ C) (H : C ⥤ A) (S : A ⥤ D) [S.Monoidal]
    (K : D ⥤ A) (L : D ⥤ C) (R : C ⥤ D)
    (β : H ⋙ S ≅ R) (γ : K ⋙ F ≅ L) (unit : 𝟭 D ⟶ K ⋙ S) [IsIso unit]
    (P : H ⋙ curriedTensor A ⟶
      (Functor.postcompose₂.obj H).obj
        ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj F).obj (curriedTensor C)))
    (p : R ⋙ curriedTensor D ⟶
      (Functor.postcompose₂.obj R).obj
        ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj L).obj (curriedTensor C))) : Prop :=
  ∀ (E : C) (M : D),
    S.map ((P.app E).app (K.obj M)) ≫
        β.hom.app (E ⊗ F.obj (K.obj M)) ≫ R.map (E ◁ γ.hom.app M) =
      Functor.OplaxMonoidal.δ S (H.obj E) (K.obj M) ≫
        (S.obj (H.obj E) ◁ inv (unit.app M)) ≫
        (β.hom.app E ▷ M) ≫ (p.app E).app M

/-- The canonical geometric-point projection comparison square commutes.
Source: Stacks Tag 0B56, with the canonical-map identification in Tag 0F0F
(blueprint: lem-kun-geometric-point-projection-comparison).

Proof:
1. Compose the normalized constant/stalk adjunction with inverse/direct image. The
   constants comparison identifies its left adjoint with constant sheaves on `Z`;
   the counit equation of `lem-kun-geometric-point-derived-sections-adjunction` therefore
   identifies its right-adjoint comparison with the specified `β`.
2. For the normalized point equivalence, take the adjunct of inverse to its monoidal
   comparison followed by inverse germ. Monoidality of the unit and counit and the
   triangle identity identify this adjunct with the tensor comparison followed by the
   counit. Thus the terminal projection mate is inverse to that normalized comparison.
3. Apply `lem-sfb-ringed-projection-tensor-composition` to `h` and the terminal morphism
   of `Spec Ω`. Its canonical pullback and right-adjoint comparisons are exactly `γ,β`.
   It gives the composite-projection equation with arbitrary unbounded `E,M`.
4. Substitute step 2 and precompose by the normalized point comparison. Cancellation
   yields the displayed square. Neither horizontal projection morphism is inverted.
-/
theorem geometricPoint_projection_comparison
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] {Z : Scheme.{u}}
    (h : Z ⟶ Spec (.of Ω)) :
    GeometricPointProjectionSquare
      (upperStar GeometricPointIntegerModule h).leftDerivedFunctor
      (lowerStar GeometricPointIntegerModule h).rightDerivedFunctor
      (geometricPointStalk Ω).mapDerivedCategory
      (geometricPointConstants Ω).mapDerivedCategory
      (constantSheaf Z.smallEtaleTopology GeometricPointIntegerModule).leftDerivedFunctor
      (rightDerivedGlobalSections GeometricPointIntegerModule Z)
      (geometricPointDerivedSectionsIso Ω h)
      (geometricPointProjectionCoefficientIso Ω h)
      (geometricPointSectionsStalkAdjunction Ω).mapDerivedCategoryAdjunction.unit
      (rightDerivedLowerStarProjectionMap GeometricPointIntegerModule h)
      ((derivedConstantGlobalSectionsAdjunction
        GeometricPointIntegerModule Z).rightAdjointProjectionMap
          (constantSheaf Z.smallEtaleTopology
            GeometricPointIntegerModule).leftDerivedTensorComparison) := by
  sorry

end AlgebraicGeometry.Etale
