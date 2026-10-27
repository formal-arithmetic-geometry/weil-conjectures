/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q98
-/
module

public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.Topology.Irreducible
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic

import WeilConjectures.AlgebraicGeometry.SubsetGeometricIrreducibility
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.AlgebraicGeometry.IrreducibleProductOverField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Local minimal primes and the neutral irreducible component of a group scheme

Source: Stacks Project, Groupoids, Tag 047M, lemma-group-scheme-field-geometrically-irreducible
(blueprint: lem-sfb-group-local-minimal-prime).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Every local ring of a group scheme over a field has a unique minimal prime. There is
exactly one irreducible component through the identity, and its reduced induced closed
subscheme is geometrically irreducible. No finiteness or reducedness assumption is needed.

Source: Stacks Project, Tag 047M (blueprint: lem-sfb-group-local-minimal-prime).

Proof, following the seven steps of the node:
1. Over an algebraically closed field every reduced irreducible component is geometrically
irreducible, by lem-sbc-subset-geometric-irreducibility. Give components their reduced closed
structures using lem-weil-pbc-reduced-induced-closed-subscheme; existence of components through
points is lem-sc-irreducible-components-cover.
2. The product of two components through the identity is irreducible by
lem-sc-irreducible-product-over-field. Its multiplication image is irreducible by
lem-weil-pbc-irreducible-continuous-image and lies in a component. The identity factors through
each reduced component, since its radical ideal vanishes in the identity's residue field.
The unit diagrams imply that the image contains both components, so maximality makes them equal.
3. For arbitrary k, pass to an algebraic closure. The identity has residue field k:
lem-weil-pbc-morphism-from-spec-field gives maps k → κ(e) → k with identity composite, and the
second map is injective and surjective. Thus the fibre over e after extension to Ω is Spec Ω,
a singleton, by def-pc-scheme-fibre and def-pc-fibre-product.
4. By lem-sfb-field-extension-irreducible-components, the inverse image of a component through
e is a nonempty union of components, each mapping onto that component. Each meets the singleton
fibre over e and is therefore the unique component through the extended identity. This proves
uniqueness over k. Apply lem-sbc-subset-geometric-irreducibility to this support; its reduced
closed scheme is geometrically irreducible, since closed immersions are stable under base
change (lem-weil-pbc-closed-immersion-base-change).
5. Components through a point correspond to minimal primes in its local ring. On an affine
neighbourhood use lem-weil-pbc-spec-irreducible-components-minimal-primes,
lem-weil-pbc-primes-of-localization and lem-weil-pbc-affine-open-stalk-localization.
Intersection and closure identify the components meeting the neighbourhood. In particular,
the local ring at the identity has a unique minimal prime.
6. At g use K = κ(g) and its canonical rational lift g' to G_K, furnished by
lem-weil-pbc-morphism-from-spec-field and def-pc-fibre-product. The map of local rings is flat
and local by lem-pc-field-extension-flat, lem-weil-pbc-flat-morphism-base-change and
def-weil-flat-morphism, hence faithfully flat by lem-weil-pbc-flat-local-hom-faithfully-flat.
Translation by g' (lem-sc-translation-automorphism) identifies its target with the local ring
at the identity of G_K, so the target has a unique minimal prime Q.
7. Surjectivity on spectra lifts each minimal prime P of the source. A minimal prime below a
lift exists by lem-weil-pbc-prime-contains-minimal-prime and equals Q. Its contraction is
contained in P and thus equals P. Existence in the nonzero source local ring follows by choosing
a minimal prime below its maximal ideal, proving uniqueness at every point. -/
theorem GrpObj.localMinimalPrimes_neutralComponent
    (k : Type u) [Field k] (G : Over (Spec (.of k))) [CategoryTheory.GrpObj G] :
    (∀ g : G.left, ∃! p : Ideal (G.left.presheaf.stalk g),
      p ∈ minimalPrimes (G.left.presheaf.stalk g)) ∧
    ∃ Z : TopologicalSpace.Closeds G.left,
      (Z : Set G.left) ∈ irreducibleComponents G.left ∧
      GrpObj.onePoint G ∈ (Z : Set G.left) ∧
      (∀ Z' : Set G.left, Z' ∈ irreducibleComponents G.left →
        GrpObj.onePoint G ∈ Z' → Z' = (Z : Set G.left)) ∧
      GeometricallyIrreducible ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ G.hom) := by
  sorry

end AlgebraicGeometry
