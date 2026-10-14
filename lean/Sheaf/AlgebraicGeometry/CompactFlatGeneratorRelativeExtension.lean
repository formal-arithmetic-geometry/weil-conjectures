/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.AlgebraicGeometry.FlatTelescopeStageMap

/-! # One relative compact flat generator resolution step

Source: Stacks Project Tags 03EW, 077J and the cone induction in Tag 06XX.
(blueprint: lem-sc-compact-flat-generator-relative-extension).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Extend a bounded-above generator complex along an arbitrary map into a
bounded-above complex, keeping its inclusion split in each degree.

Source: Stacks Project Tag 06XX, the induction step before the final
termwise-surjectivity addition; Tags 03EW and 077J supply generator resolutions.
This is the finite extension in the first paragraph of the original proof of
`lem-sc-flat-telescope-target-refinement`.

Proof. Use the affine-open sheaves j_! O_U. Their stalks are either zero or the
local ring, so they are flat. Adjunction identifies maps from them with sections
on U. A section of a sheaf coproduct locally comes from a finite subsum; an affine
open is quasi-compact, so finitely many such neighborhoods suffice. The union of
their finite supports gives the required factorization, with uniqueness and
gluing supplied by the monic inclusion of a subsum. Every module sheaf is covered
by a sum of these sheaves: for every local section choose an affine neighborhood
and its corresponding adjunction map. Resolve the bounded-above mapping cone of
a by these generators, downward from its upper bound, choosing generator covers
of the successive pullbacks of cycles as in the bounded resolution construction
underlying 077J. This gives a bounded-above complex Q and a quasi-isomorphism
Q -> Cone(a). Compose with Cone(a) -> L[1]. Its shifted cone gives L', with the
termwise split inclusion L -> L' and terms the direct sums of terms of L and Q.
The triangle comparison gives L' -> E. Its composite with L -> L' equals a up to
homotopy. Extend the comparison homotopy degreewise along the split inclusion,
and subtract its boundary; this makes the equality strict without changing the
homotopy class. The map is a quasi-isomorphism by comparison of the two triangles,
since the other vertical maps are the identity of L and Q -> Cone(a).
Finite direct sums of generator coproducts are reindexed by disjoint union, so
all terms of L' have the required generator description. The maximum of the
bounds, with the shift accounted for, bounds L'. There is no assumption on a:
a zero map, a zero target, and an acyclic target are covered by the same argument.
Empty coproducts represent zero terms. No projective lifting is used.
(blueprint: lem-sc-compact-flat-generator-relative-extension). -/
theorem exists_compact_flat_generator_relative_extension (Y : Scheme.{u})
    (L E : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (a : L ⟶ E)
    (hL : ∃ z : ℤ, ∀ i : ℤ, z < i → IsZero (L.X i))
    (hE : ∃ z : ℤ, ∀ i : ℤ, z < i → IsZero (E.X i))
    (hgen : ∀ i : ℤ, ∃ (I : Type u)
        (G : I → SheafOfModules.{u} (moduleRings Y.toRingedSpace)),
        Nonempty (L.X i ≅ ∐ G) ∧
        (∀ j : I, SheafOfModules.IsFlat (G j)) ∧
        ∀ (j : I) (K : Type u)
          (H : K → SheafOfModules.{u} (moduleRings Y.toRingedSpace))
          (f : G j ⟶ ∐ H),
          ∃ (S : Finset K) (g : G j ⟶ ∐ (fun k : {k // k ∈ S} ↦ H k.1)),
            g ≫ Sigma.desc (fun k : {k // k ∈ S} ↦ Sigma.ι H k.1) = f) :
    ∃ (L' : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
      (l : L ⟶ L') (v : L' ⟶ E),
      (∃ z : ℤ, ∀ i : ℤ, z < i → IsZero (L'.X i)) ∧
      QuasiIso v ∧ (l ≫ v = a) ∧ (∀ i : ℤ, IsSplitMono (l.f i)) ∧
    ∀ i : ℤ, ∃ (I : Type u)
        (G : I → SheafOfModules.{u} (moduleRings Y.toRingedSpace)),
        Nonempty (L'.X i ≅ ∐ G) ∧
        (∀ j : I, SheafOfModules.IsFlat (G j)) ∧
        ∀ (j : I) (K : Type u)
          (H : K → SheafOfModules.{u} (moduleRings Y.toRingedSpace))
          (f : G j ⟶ ∐ H),
          ∃ (S : Finset K) (g : G j ⟶ ∐ (fun k : {k // k ∈ S} ↦ H k.1)),
            g ≫ Sigma.desc (fun k : {k // k ∈ S} ↦ Sigma.ι H k.1) = f := by sorry

end AlgebraicGeometry
