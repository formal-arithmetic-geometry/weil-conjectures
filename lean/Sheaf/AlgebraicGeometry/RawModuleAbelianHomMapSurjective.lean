/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.AlgebraicGeometry.RawModuleAbelianHomMap

/-! # Surjective raw scalar comparison

Source: Stacks Project, Tag 03FD, injective-resolution comparison.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- Surjective of the raw scalar comparison on underlying groups.
Source: Stacks Project, Tag 03FD, lemma-cohomology-modules-abelian-agree.
(blueprint: lem-sbc-raw-module-abelian-hom-map-surjective).

Proof: Fix an abelian derived class. Resolve A.hom^*G by injective module
sheaves. By Tag 03FD the underlying abelian terms are acyclic for evaluation on
every etale object, including V = U times_S A.left. Therefore the section complex
of this forgotten resolution computes the target derived Hom from the pulled-back
free represented abelian sheaf. Represent the given class by a section cocycle in
that complex. The very same cocycle in the module section complex defines a module
derived class, using the free represented module sections adjunction. The explicit
map forgets this cocycle without changing it: freeMap carries the identity generator
to the identity generator, while the single, shift and inverse-image comparisons
identify the same section. Consequently the image of the module class is the given
abelian class. No lifting of arbitrary abelian sheaf morphisms to module morphisms
is asserted; only sections of this module resolution are used. Degree zero, the
zero ring and empty V are included by the identical section-complex calculation. -/
theorem rawModuleAbelianHomMap_surjective
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ)
    (U : S.Etale) (A : Over W) :
    Function.Surjective (rawModuleAbelianHomMap Λ k G q U A).hom := by sorry

end AlgebraicGeometry.Etale
