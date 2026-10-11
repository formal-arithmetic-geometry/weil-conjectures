/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
import Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap

/-! # RHom base change for a perfect complex

Source: Stacks Project, more-algebra.tex, Lemma 0A6A, lemma-base-change-RHom, clause (1)
(blueprint: lem-pc-base-change-rhom-perfect).
-/

universe u₁ w₁

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- For a morphism of commutative rings, the canonical derived Hom base-change map out of
any perfect complex is an isomorphism. Perfectness of `E` is the bounded representative
`m.source` with finite projective terms (evaluated at the unique object of the shared
one-object site) and `m.sourceIso`; `K` is arbitrary. The statement holds for every
extension data `d` and every such model `m`, both of which exist
(`ringRHomBaseChangeData_exists`, `perfectRHomBaseChangeModel_exists`).

Source: Stacks Project, more-algebra.tex, Lemma 0A6A, lemma-base-change-RHom, clause (1),
and equation-base-change-RHom (blueprint: lem-pc-base-change-rhom-perfect).

Proof (the node's four steps):
1. Let `P = m.source`, the bounded finite-projective representative of `E`, and
   `Q = m.target`, the K-flat representative of `K` (lem-pc-kflat-resolution,
   def-pc-kflat-complex).
   Bounded-above projective complexes are K-projective
   (lem-sc-bounded-above-projective-kprojective), so the Hom map induced by the K-injective
   replacement of `Q` is a quasi-isomorphism. Thus `Hom(P,Q)` represents the shared
   `derivedInternalHom` (def-pur-derived-internal-hom).
2. In each degree the product defining `Hom(P,Q)` is finite. For a finite projective
   `P^i`, the canonical map `B ⊗ Hom(P^i,Q^j) → Hom(B ⊗ P^i,B ⊗ Q^j)` is an isomorphism:
   first check finite free modules, then pass to direct summands. These maps commute
   with differentials and give the chain isomorphism specified by `homMap_pure`.
3. The Hom complex is K-flat: it is `Tot(P^∨ ⊗ Q)`, with `P^∨` bounded finite projective.
   For any acyclic `F`, `Tot(F ⊗ P^∨)` is acyclic
   (lem-pc-module-bounded-flat-kflat); tensor with the K-flat `Q` and use associativity
   (def-pc-kflat-complex). Hence the derived scalar-extension counit on `Hom(P,Q)` is
   invertible (lem-pur-derived-change-of-rings).
4. The same counit computes scalar extension on `P` and `Q`. The extended `P` remains
   bounded finite projective, so the first step over `B` identifies the target RHom.
   The map `f ↦ 1 ⊗ f`, extended `B`-linearly, is exactly `b ⊗ f ↦ (c ⊗ x ↦ bc ⊗ f(x))`.
   Consequently the composite in `perfectRHomBaseChangeMap` is the source's canonical
   map, and every factor of that composite is invertible by steps 1–3. -/
theorem baseChangeRHomPerfect
    {A B : Type u₁} [CommRing A] [CommRing B] {φ : A →+* B}
    [HasDerivedCategory.{w₁} (RingSiteModules A)]
    [HasDerivedCategory.{w₁} (RingSiteModules B)]
    (d : RingRHomBaseChangeData φ) (E K : DerivedCategory (RingSiteModules A))
    (m : PerfectRHomBaseChangeModel d E K) :
    IsIso (perfectRHomBaseChangeMap d m) := by
  sorry

end CategoryTheory
