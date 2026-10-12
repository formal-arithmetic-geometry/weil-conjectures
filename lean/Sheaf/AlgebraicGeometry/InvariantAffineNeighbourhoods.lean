/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import Sheaf.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree

/-!
# Invariant affine neighbourhoods for finite locally free descent

Source: Stacks Project, Groupoid Schemes, Tags 0H8K and 03JE; Algebra, Tag 00DS.
(blueprint: lem-pd-invariant-affine-neighbourhoods).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace CategoryTheory.Over.DescentDatum

/-- Every point has an affine neighbourhood invariant under transport, lying over an affine
open of the base. Source: Stacks Project, Tags 0H8K, 03JE and 00DS.
(blueprint: lem-pd-invariant-affine-neighbourhoods).

Proof: Choose an affine neighbourhood B of the image of v in Y and restrict X and V
above B. The transport defines a groupoid on V; both projections are finite locally
free because they are base changes of p. The orbit of v is therefore finite. By hV it
lies in an affine open A. Intersect with the inverse image of B and use finite prime
avoidance (00DS) to choose a principal affine neighbourhood of the orbit within A.
Apply the invariant-neighbourhood construction of 03JE to the restricted groupoid:
remove the closed saturation of the complement of A, choose a function nonzero on
the finite orbit, and take the nonvanishing locus of its norm along the finite locally
free projection. This is an invariant affine neighbourhood U of v inside A, hence
inside the inverse image of B. Invariance for the universal groupoid arrows implies
invariance for every transported T-point by naturality. The empty V case is vacuous;
no global bound on the degree of p is needed since the construction is local on B. -/
theorem exists_invariant_affine_neighbourhood
    {X Y : Scheme.{u}} {p : X ⟶ Y} [IsFinite p] [Flat p]
    [LocallyOfFinitePresentation p] [Surjective p] {V : Over X}
    (hV : ∀ s : Set V.left, s.Finite → ∃ U : V.left.Opens, IsAffineOpen U ∧ s ⊆ U)
    (D : Over.DescentDatum p V) (v : V.left) :
    ∃ U : V.left.Opens, v ∈ U ∧ IsAffineOpen U ∧
      (∃ B : Y.Opens, IsAffineOpen B ∧ U ≤ (V.hom ≫ p) ⁻¹ᵁ B) ∧
      ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p)
        (a : Over.mk f₁ ⟶ V), Set.range a.left ⊆ U →
          Set.range (D.transport f₁ f₂ h a).left ⊆ U := by
  sorry

end CategoryTheory.Over.DescentDatum
