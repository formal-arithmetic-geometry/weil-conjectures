/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorAugmentation
public import Sheaf.Algebra.Homology.DerivedInternalHom
import Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHom
import Sheaf.AlgebraicGeometry.DerivedInternalHomAdjunction
import Sheaf.AlgebraicGeometry.OpenRestrictionKFlatModel
import Sheaf.AlgebraicGeometry.OpenRestrictionTotalTensor
import Sheaf.AlgebraicGeometry.KFlatDerivedTensorComparison
import Sheaf.Algebra.Homology.HomComplexRestrictOpen
import Sheaf.Algebra.Homology.KInjectiveRestrictOpen
import Sheaf.Paper.DerivedInternalHomRestrictOpen

/-! # Tensor-model adjunction and restriction

Source: Stacks Project, cohomology.tex, Tags 08DJ and 08DL.
(blueprint: lem-sc-tensor-model-restriction-adjunction).
-/

@[expose] public section

set_option autoImplicit false
universe uX wD
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxSize 512 in
/-- The adjunction on a fixed K-flat first model gives global and restricted
transposition families. They commute with restriction and are natural in the
second complex, without any K-flatness requirement on that complex.

Source: Stacks Project, cohomology.tex, Tag 08DJ, equation-internal-hom and
lemma-internal-hom; Tag 08DL, lemma-restriction-RHom-to-U.
(blueprint: lem-sc-tensor-model-restriction-adjunction).

Proof:
1. Compute tensor with the fixed K-flat P by the total tensor complex, and
transport its first argument through eA. The canonical tensor-Hom adjunction,
with the tensor symmetry to order P first, gives t for every J and E.
2. Restriction is exact, preserves P's K-flatness, and commutes with direct-sum
signed total tensors. Restrict P and transport eA by restriction. The canonical
RHom restriction comparison and the same adjunction on U give r.
3. Resolve E by a K-injective complex. Its restriction is K-injective. The Hom
restriction comparison restricts each local component, and tensor evaluation
on each summand restricts the same local map. Thus r applied to the restriction
of a morphism is the restriction of t applied to that morphism. Localizing the
component equations gives the first displayed identity. Since P is K-flat and
I is K-injective, Hom(P,I) is K-injective, both globally and after restriction.
Every derived map from Q(J) into these Hom objects is therefore represented by
a chain map modulo homotopy, even for non-K-flat J. Uncurrying respects homotopy;
the component calculation consequently proves compatibility for every derived
morphism, not just for an assumed chain representative.
4. Precomposition by a chain map u in J commutes with evaluation on every
summand. The canonical adjunction is natural, as are the localization tensor
comparison and restriction comparison. Hence r sends precomposition by R(Q(u))
to precomposition by R(Q(id_P tensor u)), the second displayed identity.
The zero model and the empty open satisfy the same equations, since all the
comparisons and summand maps are defined there too. -/
theorem exists_tensorModel_restriction_adjunction
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
    ∃ (t : ∀ J E, (DerivedCategory.Q.obj J ⟶ H E) ≃ (B J ⟶ E))
      (r : ∀ J E, (R.obj (DerivedCategory.Q.obj J) ⟶ R.obj (H E)) ≃
        (R.obj (B J) ⟶ R.obj E)),
      (∀ J E (ξ : DerivedCategory.Q.obj J ⟶ H E),
        r J E (R.map ξ) = R.map (t J E ξ)) ∧
      (∀ J J' E (u : J ⟶ J')
        (s : R.obj (DerivedCategory.Q.obj J') ⟶ R.obj (H E)),
        r J E (R.map (DerivedCategory.Q.map u) ≫ s) =
          R.map (DerivedCategory.Q.map
            (HomologicalComplex.mapBifunctorMap (𝟙 P) u (curriedTensor _)
              (ComplexShape.up ℤ))) ≫ r J' E s) := by sorry

end AlgebraicGeometry.Scheme
