/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.FormallySmooth
public import Mathlib.RingTheory.RingHom.Smooth
import Sheaf.AlgebraicGeometry.Thickening

/-!
# Affine formal smoothness and the square-zero lifting property

Source: Stacks Project, More on Morphisms, Lemma 37.11.5 (Tag 02H4),
Algebra Definition 10.137.1 (Tag 00TI) (blueprint:
lem-weil-pbc-affine-formally-smooth-iff-ring-lifting).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- (blueprint: lem-weil-pbc-affine-formally-smooth-iff-ring-lifting)
The morphism of affine schemes induced by a ring homomorphism is formally smooth
exactly when the ring homomorphism has the square-zero lifting property, i.e. is
formally smooth in the ring-theoretic sense of Stacks Tag 00TI
(`RingHom.FormallySmooth`, equivalent to the lifting property by
`Algebra.FormallySmooth.iff_comp_surjective`).

Proof (Stacks 02H4, immediate from the definitions via the equivalence of rings
and affine schemes, Tag 01I2): morphisms `Spec B ⟶ Spec A` are `Spec` of unique
ring maps `A → B`, and `Spec h` lies over `Spec R` iff `h` is an `R`-algebra map.
For `N ⊆ D` with `N ^ 2 = 0`, `Spec (D ⧸ N) ⟶ Spec D` is a first order thickening
of affine schemes over `Spec R`; conversely every first order thickening of affine
schemes over `Spec R` is isomorphic, compatibly with the maps to `Spec R`, to one
of this form, and the lifting problems transport along such isomorphisms. Under
this dictionary the scheme lifting problem for `Spec φ` along `Spec (D ⧸ N) ⟶ Spec D`
is the ring lifting problem for `φ` along `D → D ⧸ N`, which gives both directions. -/
theorem formallySmooth_spec_iff_ringHom_formallySmooth
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) :
    FormallySmooth (Scheme.Spec.map (CommRingCat.ofHom φ).op) ↔
      RingHom.FormallySmooth φ := by
  sorry

end AlgebraicGeometry
