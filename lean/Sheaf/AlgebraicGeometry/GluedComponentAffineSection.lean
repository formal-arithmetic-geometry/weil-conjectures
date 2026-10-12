/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.Ample
public import Sheaf.AlgebraicGeometry.TensorPullback
import Sheaf.AlgebraicGeometry.AmpleFinitePrincipalAffine
import Sheaf.AlgebraicGeometry.GlueComponentLineBundles
import Sheaf.AlgebraicGeometry.IsAffineOfFiniteClosedCover

/-! # An affine section around component intersections

Source: Stacks Project, Varieties, Lemma 09NX, first two paragraphs.
(blueprint: lem-sc-glued-component-affine-section).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Ample modules on the components can be powered and glued, with an affine section
neighbourhood of their intersections. This constructs the bundle but does not assert
its ampleness on the ambient scheme.

Source: Stacks Project, Varieties, Lemma 09NX, first two paragraphs; Properties,
Lemma 09NV; Varieties, Lemma 09NE; Limits, Lemma 09NL.
(blueprint: lem-sc-glued-component-affine-section).

Proof: Let T be the union of the distinct component intersections. Its inverse image
in every component is a finite set, since a closed immersion is injective. Apply
lem-sc-ample-finite-principal-affine with W equal to the whole component. This gives a
positive power of each M a and a section with affine locus containing that inverse
image. These powers remain ample: for a power k > 0 and a section t of M^n giving
an affine locus at a point, t^k is a section of (M^k)^n with the same locus. Every pairwise
intersection is a finite space of closed points, hence discrete. Apply
lem-sc-glue-component-line-bundles to these powers and their sections. It gives an invertible L
with the prescribed component restrictions
and a global section s. Pullback and the component isomorphisms preserve nonvanishing,
so its locus contains T. Its restrictions have the chosen affine loci, which form a
finite closed cover of that locus; lem-sc-closed-affine-union-affine makes it affine.
Transport s through L.tensorPow 1 isomorphic to L. The same transport preserves its
nonvanishing locus. If there are no components, X is empty and its tensor unit and zero
section have empty affine locus. -/
theorem exists_glued_component_affine_section
    (X : Scheme.{u}) [IsReduced X] (r : ℕ)
    (C : Fin r → Scheme.{u}) (i : ∀ a, C a ⟶ X)
    [∀ a, IsClosedImmersion (i a)]
    (hcover : (⋃ a, Set.range (i a)) = Set.univ)
    (T : Set X)
    (hT : T = {x | ∃ a b : Fin r, a ≠ b ∧
      x ∈ Set.range (i a) ∩ Set.range (i b)})
    (hfinite : T.Finite) (hclosed : ∀ x ∈ T, IsClosed ({x} : Set X))
    (M : ∀ a, (C a).Modules) [∀ a, (M a).IsInvertible]
    (hM : ∀ a, IsAmple (C a) (M a)) :
    ∃ (L : X.Modules) (hL : L.IsInvertible),
      (∀ a, ∃ h : ((tensorPullback (i a)).obj L).IsInvertible,
        @IsAmple (C a) ((tensorPullback (i a)).obj L) h) ∧
      ∃ s : (L.tensorPow 1).val.presheaf.obj (Opposite.op ⊤),
        ∃ U : X.Opens, T ⊆ (U : Set X) ∧ IsAffineOpen U ∧
          (U : Set X) = nonvanishingLocus (L.tensorPow 1) s := by
  sorry

end AlgebraicGeometry.Scheme.Modules
