/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedTensorAugmentation
public import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.AlgebraicGeometry.AffinePerfectOpenRepresentCohomology
import Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import Sheaf.AlgebraicGeometry.KoszulOpenSystem

/-! # Koszul representatives of sections on an affine open

Source: Stacks Project, Tags 08DC, 08DD and 08EH.
(blueprint: lem-sc-affine-koszul-section-roof).
-/

@[expose] public section

set_option autoImplicit false

universe uX wD

open CategoryTheory CategoryTheory.Limits TopologicalSpace MonoidalCategory

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxSize 512 in
/-- A section of an arbitrary quasi-coherent derived object on a compact open of an affine scheme
is represented by a map from a K-flat perfect complex with a chain augmentation.
There is no perfect source, tensor product, or lifted morphism in this statement.

Source: Stacks Project, perfect.tex, Tags 08DC and 08DD, and the first paragraph of
Tag 08EH; cohomology.tex, Tag 06YD.
(blueprint: lem-sc-affine-koszul-section-roof).

Proof:
1. Use the canonical affine isomorphism X ≅ Spec Γ(X,O_X). Compactness of U and
   the principal-open basis give a finite family f with U the union of D(f_i).
   Transport E and the section along the exact equivalence of module sheaves and
   its induced derived equivalence. Transport the open by the same isomorphism.
2. Apply affine_perfect_open_represent_cohomology to the transported E. The
   colimit of the Hom sets is jointly surjective, so the given section is the image
   of a map ξ_e at some exponent e. The cocone formula says that restriction of
   ξ_e is the section precomposed with the restricted augmentation.
3. Take the actual associated-sheaf Koszul tail at e, transported back to X.
   Identify its degree-zero target with the tensor-unit complex via tilde(A)=O_X
   and the single-complex comparison. Compose its chain augmentation with this
   chain isomorphism. Its bounded finite free terms imply K-flatness by
   isKFlat_of_boundedAbove_flat_ringedSpace; its derived object is perfect by the
   cohomology-representation theorem. The restricted augmentation is invertible
   by that theorem. Naturality of transport gives the displayed equation.
4. If U is empty, use the empty family and the zero tail: both restricted objects
   are zero and the unique augmentation is invertible. The proof needs neither
   nonemptiness of U nor a lower bound on the cohomology of E. -/
theorem affine_koszul_section_roof
    (X : Scheme.{uX}) [IsAffine X] (U : X.Opens) (hU : IsCompact (U : Set X))
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{wD} (SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))]
    (E : schemeDerivedQCohCategory X) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    letI := (SheafOfModules.tensorClosed X.sheaf).1.some
    let T := HomologicalComplex.tensorUnit
      (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)
    let R := ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
      Equivalence.functor
        (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)).mapDerivedCategory
    ∀ s : R.obj (DerivedCategory.Q.obj T) ⟶ R.obj E.obj,
      ∃ J : CochainComplex (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) ℤ,
        CochainComplex.IsKFlat (R := X.sheaf) J ∧ IsPerfect X (DerivedCategory.Q.obj J) ∧
        ∃ (u : J ⟶ T) (ξ : DerivedCategory.Q.obj J ⟶ E.obj),
          IsIso (R.map (DerivedCategory.Q.map u)) ∧
          R.map (DerivedCategory.Q.map u) ≫ s = R.map ξ := by sorry

end AlgebraicGeometry.Scheme
