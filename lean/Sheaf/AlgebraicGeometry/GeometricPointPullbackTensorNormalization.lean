/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.GeometricPointDerivedSectionsAdjunction
import Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap
import Sheaf.AlgebraicGeometry.GeometricPointDerivedConstants
import Sheaf.AlgebraicGeometry.PullbackConstantModule
import Sheaf.Paper.EtaleFlatKFlatResolution
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison

/-! # Tensor normalization for pullback at a geometric point

Source: Stacks Project, Tags 07A4, 07A6 and 0F0F
(blueprint: lem-kun-geometric-point-pullback-tensor-normalization).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

/-- Tensor compatibility of an evaluation comparison, expressed without expanding the
localization objects. Source: Stacks Tag 07A4
(blueprint: lem-kun-geometric-point-pullback-tensor-normalization). -/
def PullbackStalkTensorCompatible
    {C A D : Type*} [Category* C] [Category* A] [Category* D]
    [MonoidalCategory C] [MonoidalCategory A] [MonoidalCategory D]
    (F : A ⥤ C) (S : A ⥤ D) [S.Monoidal] (L : D ⥤ C)
    (φ : (Functor.postcompose₂.obj F).obj (curriedTensor A) ⟶
      (((Functor.whiskeringLeft₂ C).obj F).obj F).obj (curriedTensor C))
    (ψ : (Functor.postcompose₂.obj L).obj (curriedTensor D) ⟶
      (((Functor.whiskeringLeft₂ C).obj L).obj L).obj (curriedTensor C))
    (σ : S ⋙ L ⟶ F) : Prop :=
  ∀ X Y, L.map (Functor.OplaxMonoidal.δ S X Y) ≫
      (ψ.app (S.obj X)).app (S.obj Y) ≫ (σ.app X ⊗ₘ σ.app Y) =
    σ.app (X ⊗ Y) ≫ (φ.app X).app Y

/-- The inverse constant comparison followed by evaluation under an adjunction.
Source: Stacks Tag 07A6
(blueprint: lem-kun-geometric-point-pullback-tensor-normalization). -/
noncomputable def pullbackStalkComparison
    {C A D : Type*} [Category* C] [Category* A] [Category* D]
    {F : A ⥤ C} {S : A ⥤ D} {K : D ⥤ A} {L : D ⥤ C}
    (a : K ⊣ S) (γ : K ⋙ F ≅ L) : S ⋙ L ⟶ F :=
  Functor.whiskerLeft S γ.inv ≫
    (Functor.associator S K F).inv ≫ Functor.whiskerRight a.counit F

/-- The pullback comparison from constant sheaves on a geometric point, evaluated at a stalk
and followed by the normalized equivalence counit. This uses only the fixed coefficient
comparison, exact-functor identifications and the specified point counit.
Source: Stacks Tags 07A4 and 07A6
(blueprint: lem-kun-geometric-point-pullback-tensor-normalization). -/
noncomputable def geometricPointPullbackStalkComparison
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] {Z : Scheme.{u}}
    (h : Z ⟶ Spec (.of Ω)) :
    (geometricPointStalk Ω).mapDerivedCategory ⋙
        (constantSheaf Z.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).leftDerivedFunctor ⟶
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).leftDerivedFunctor :=
  let F := (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h)
  let K := (geometricPointConstants Ω).mapDerivedCategory
  let γ := Functor.isoWhiskerLeft K F.leftDerivedFunctorIsoMapDerivedCategory ≪≫
    geometricPointSectionsConstantsIso Ω h ≪≫
    (constantSheaf Z.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).leftDerivedFunctorIsoMapDerivedCategory.symm
  pullbackStalkComparison
    (geometricPointSectionsStalkAdjunction Ω).mapDerivedCategoryAdjunction γ

/-- The stalk-evaluation comparison preserves the canonical derived tensor comparisons.
Source: Stacks Tags 07A4 and 07A6, with the point normalization of Tags 04JQ and 0F0F
(blueprint: lem-kun-geometric-point-pullback-tensor-normalization).

Proof:
1. On ordinary sheaves the constant pullback comparison sends a constant section to the
   same constant section. The point counit evaluates the unique global section representing
   a germ. On a tensor of two germs, evaluating their tensor gives the tensor of their
   evaluations. Thus this comparison commutes with the ordinary tensor comparisons.
2. Apply the identity degreewise to flat K-flat representatives. The total tensor maps
   use the same direct sums and signs on both sides; additivity and naturality extend the
   identity from homogeneous tensors to the total tensor complex.
3. Localize in both variables. The normalization of the descended stalk tensorator is
   precisely stalk_factors_monoidal in GeometricPointDerivedConstantsData. The other two
   tensorators are the uniquely specified leftDerivedTensorComparison. The universal
   property of the total left derived bifunctor therefore descends the identity to every
   pair of unbounded derived objects. The exact-functor identifications are the canonical
   counit-compatible identifications used in the definition above.
-/
theorem geometricPoint_pullbackStalk_tensor
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] {Z : Scheme.{u}}
    (h : Z ⟶ Spec (.of Ω)) :
    letI := (Classical.choice
      (nonempty_geometricPointDerivedConstantsData Ω)).derivedStalkMonoidal
    PullbackStalkTensorCompatible
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).leftDerivedFunctor
      (geometricPointStalk Ω).mapDerivedCategory
      (constantSheaf Z.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).leftDerivedFunctor
      (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h)
      (constantSheaf Z.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).leftDerivedTensorComparison
      (geometricPointPullbackStalkComparison Ω h) := by
  sorry

end AlgebraicGeometry.Etale
