/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Sheaf.RingTheory.ExcellentRing

/-!
# Catenarity from an affine open cover

Source: Stacks Project, Properties, Tag 02IX (lemma-catenary-local), implication (4) implies (3).
(blueprint: lem-trf-catenary-affine-open-cover)

## Main statement

* `isCatenaryRing_of_affine_openCover` transfers catenarity of the coordinate rings of
  an affine open cover to every affine open of the scheme.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Let `S` be a scheme covered by affine open subschemes `U i`. If every coordinate ring
`Γ(S, U i)` is catenary, then the coordinate ring of every affine open subscheme of `S`
is catenary. This is Stacks Project, Properties, Tag 02IX (lemma-catenary-local),
implication (4) implies (3) (blueprint: lem-trf-catenary-affine-open-cover).

Proof:
1. For an affine open `T` of `S`, choose an affine presentation and identify its coordinate
   ring with `Γ(S, T)` using the global-sections isomorphism for an affine spectrum.
2. The prime/irreducible-closed correspondence identifies prime intervals with intervals of
   irreducible closed subsets, reversing order; finite chain bounds and equality of saturated
   chain lengths are therefore preserved.
3. For an affine open `V` and primes `p ≤ q` of `Γ(S, V)`, choose the point corresponding to
   `q` and a cover member `U i` containing it. With `W = V ∩ U i`, the open-subspace
   correspondence identifies the whole irreducible-closed interval in `V` with the interval
   in `W`, and then with the corresponding interval in `U i` by closure.
4. Catenarity of `Γ(S, U i)` transfers across these interval bijections and then back across
   the prime/irreducible-closed correspondence to the arbitrary prime interval of `Γ(S, V)`.
   The empty scheme (and hence an empty cover) is vacuous because its affine coordinate ring
   is the zero ring with no prime ideals. -/
theorem isCatenaryRing_of_affine_openCover (S : Scheme.{u}) (I : Type u)
    (U : I → S.Opens) (hU : iSup U = ⊤)
    (hUi : ∀ i : I, IsAffineOpen (U i))
    (hcat : ∀ i : I, IsCatenaryRing Γ(S, U i)) :
    ∀ (V : S.Opens), IsAffineOpen V → IsCatenaryRing Γ(S, V) := by
  sorry

end AlgebraicGeometry
