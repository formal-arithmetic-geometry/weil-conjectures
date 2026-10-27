/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O1
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.SpaceSquareZeroExtensionData
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.SpaceUniversalConormal
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-! # Flatness detected by the conormal map of first-order thickenings

Source: Stacks Project, More on Morphisms of Spaces, Tag 06BH, lemma-deform
(blueprint: lem-sfb-space-conormal-flatness-criterion).

The conormal modules and the normalization of their canonical map are the existing
ones. The map below is selected from a unique existence theorem, so its defining
property determines it completely; no arbitrary module map is assumed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The canonical conormal map of a square of first-order thickenings. Its unique
normalization is `IsSpaceConormalMap`: on local ideal tensors it is induced by the
ring map of the thickened morphism. Since the ideals have square zero, changing a
scalar lift adds a product of two elements of the target ideal, hence adds zero.
Source: Stacks Project, Tag 06BH, lemma-deform, and conormal functoriality, Tag 0607
(blueprint: lem-sfb-space-conormal-flatness-criterion). -/
def firstOrderConormalMap {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (i : X ⟶ X') (j : Y ⟶ Y')
    (hi : IsSpaceFirstOrderThickening i) (hj : IsSpaceFirstOrderThickening j)
    (h : i ≫ f' = f ≫ j) :
    (moduleTensorPullback f).obj (spaceConormal j) ⟶ spaceConormal i :=
  (space_conormal_map f f' i j hi hj h).exists.choose

/-- Flatness and the canonical Cartesian identification are equivalent to invertibility
of the canonical conormal map, without finiteness or Noetherian assumptions.
Source: Stacks Project, More on Morphisms of Spaces, Tag 06BH, lemma-deform
(blueprint: lem-sfb-space-conormal-flatness-criterion).

Proof:
1. On the common small etale sites, square-zero ideals have I/I² = I/0 = I.
   The canonical conormal map is the ideal map: both send a tensor a tensor j to
   a lift of a times f'-sharp(j). The difference between two lifts lies in I_X,
   and the image of j also lies in I_X, so their product is zero. These
   identifications respect restrictions and scalar multiplication.
2. Apply lem-sfb-space-square-zero-flatness-criterion with Z = X, Z' = X',
   J_Z = I_X and J_Y = I_Y. Its hypotheses are precisely hi, hj and hf.
   Step 1 identifies its ideal map with firstOrderConormalMap. Its Cartesian
   conclusion is invertibility of the displayed canonical sheaf pullback lift.
   This gives both implications with no finite-presentation or Noetherian input. -/
theorem space_conormal_flatness_criterion {S : Scheme.{u}}
    {X Y X' Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (i : X ⟶ X') (j : Y ⟶ Y')
    (hi : IsSpaceFirstOrderThickening i) (hj : IsSpaceFirstOrderThickening j)
    (h : i ≫ f' = f ≫ j) (hf : MapIsFlat f) :
    (MapIsFlat f' ∧
      IsIso (Limits.pullback.lift i.hom f.hom (congrArg (fun k ↦ k.hom) h))) ↔
      IsIso (firstOrderConormalMap f f' i j hi hj h) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
