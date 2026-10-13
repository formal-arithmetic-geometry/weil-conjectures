/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorAugmentation
public import Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHom
import Sheaf.AlgebraicGeometry.OpenRestrictionKFlatModel
import Sheaf.AlgebraicGeometry.OpenRestrictionTotalTensor
import Sheaf.AlgebraicGeometry.KFlatDerivedTensorComparison
import Sheaf.Algebra.Homology.HomComplexRestrictOpen
import Sheaf.Algebra.Homology.KInjectiveRestrictOpen
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import Sheaf.AlgebraicGeometry.DerivedTensorSymmetry
import Sheaf.Paper.DerivedInternalHomRestrictOpen

/-! # Coherent tensor-model comparisons under open restriction

Source: Stacks Project, cohomology.tex, Tags 08DJ and 08DL.
(blueprint: lem-sc-tensor-model-restriction-comparisons).
-/

@[expose] public section

set_option autoImplicit false
universe uX wD
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

set_option maxHeartbeats 1000000 in
-- Canonical representative coherence requires substantial elaboration.
/-- Coherent tensor-model and RHom object comparisons under open restriction.
Source: Stacks Project, cohomology.tex, Tags 08DJ and 08DL, and Tag 06YH.
(blueprint: lem-sc-tensor-model-restriction-comparisons).

Proof: compute tensor with the K-flat P using the natural localization tensor
comparison. Apply tensor symmetry and eA to obtain c. Restrict P, which remains
K-flat, and use the total-tensor restriction comparison and the localization
factorization of restriction to obtain d. Naturality of those comparisons and
symmetry gives the first equation. For h, resolve E by the fixed K-injective
resolution, restrict it, and identify the Hom complexes termwise; transport the
result through the over-site equivalence to U.toScheme. On each tensor summand,
restriction of the evaluation map is evaluation of the restricted local map.
This proves the second equation for chain maps into Hom(P,I). That Hom complex
is K-injective, since P is K-flat and I is K-injective. Its restriction is also
K-injective. Every morphism from Q(J) is represented by a chain map modulo
homotopy, without requiring J to be K-flat. Uncurrying respects homotopy, so the
equation holds for every derived morphism. All comparisons are defined for zero
complexes and the empty open as well. -/
theorem exists_tensorModel_restriction_comparisons
    (X : Scheme.{uX}) (U : X.Opens)
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{wD} (SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))]
    (A : schemeDerivedCategory X)
    (P : CochainComplex (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlat (R := X.sheaf) P)
    (eA : DerivedCategory.Q.obj P ≅ A) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    letI := (SheafOfModules.tensorClosed X.sheaf).1.some
    let R := ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
      Equivalence.functor
        (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)).mapDerivedCategory
    let H := fun E ↦ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.toRingedSpace.sheaf).obj (op A, E)
    let B := fun J ↦ DerivedCategory.Q.obj
      (CochainComplex.mapBifunctor P J (curriedTensor _))
    let HU := derivedInternalHom (Opens.grothendieckTopology U.toScheme.toRingedSpace)
      U.toScheme.toRingedSpace.sheaf
    ∃ (c : ∀ J, B J ≅ DerivedCategory.Q.obj J ⊗ A)
      (d : ∀ J, R.obj (B J) ≅ R.obj (DerivedCategory.Q.obj J) ⊗ R.obj A)
      (h : ∀ E, R.obj (H E) ≅ HU.obj (op (R.obj A), R.obj E)),
      (∀ J J' (u : J ⟶ J'),
        R.map (DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap (𝟙 P) u (curriedTensor _)
            (ComplexShape.up ℤ))) ≫ (d J').hom =
          (d J).hom ≫ (R.map (DerivedCategory.Q.map u) ⊗ₘ 𝟙 (R.obj A))) ∧
      (∀ J E (ξ : DerivedCategory.Q.obj J ⟶ H E),
        (d J).hom ≫ schemeDerivedTensorHomEquiv U.toScheme
          (R.obj (DerivedCategory.Q.obj J)) (R.obj A) (R.obj E)
          (R.map ξ ≫ (h E).hom) =
        R.map ((c J).hom ≫ schemeDerivedTensorHomEquiv X
          (DerivedCategory.Q.obj J) A E ξ)) := by sorry

end AlgebraicGeometry.Scheme
