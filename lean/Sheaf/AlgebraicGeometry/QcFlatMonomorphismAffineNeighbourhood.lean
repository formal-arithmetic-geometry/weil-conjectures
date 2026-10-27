module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # An affine neighbourhood of the image of a quasi-compact flat monomorphism

Source: Raynaud, Un critère d'effectivité de descente, §1, Proposition 1.5(i), printed p.3.
(blueprint: lem-sfb-qc-flat-monomorphism-affine-neighbourhood)

The neighbourhood is an open subscheme of the target; the induced morphism to it is affine.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A quasi-compact flat monomorphism is affine over an open neighbourhood of its image.
The factorization is the canonical lift through the inclusion of that open subscheme.

Source: Raynaud, Un critère d'effectivité de descente, §1, Proposition 1.5(i), printed p.3.
(blueprint: lem-sfb-qc-flat-monomorphism-affine-neighbourhood)

Proof plan:
1. By lem-sfb-qc-flat-monomorphism-ringed-image, identify X with the induced ringed subspace
   on its image E. For x in X, choose an affine target chart A containing f(x) and an affine
   open V of its preimage containing x (def-pc-scheme). The subspace topology supplies an
   open W in A whose inverse image is V.
2. The affine scheme A is separated: its morphism to Spec Z is affine by
   lem-weil-pbc-morphism-affine-schemes-affine, hence separated by
   lem-weil-pbc-affine-morphism-permanence. The diagonal of W is the base change of that
   of A (the open inclusion is monic by def-weil-open-immersion), so it is closed by
   lem-weil-pbc-closed-immersion-base-change. Thus W is separated
   (def-weil-proper-morphism). By lem-weil-pbc-affine-source-separated-target-affine-morphism,
   V to W is affine, giving affine inverse images of affine opens (pqf-def-affine-morphism).
3. Take U to be the union of these W. It contains the image, so f factors canonically
   through U (def-weil-open-immersion). Affine charts of the W cover U with affine inverse
   images; pqf-lem-affine-local-target proves the factorization affine. For empty X take
   empty U, and use the empty affine cover.
-/
theorem Flat.exists_open_neighbourhood_isAffineHom_of_mono
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [Flat f] [Mono f] :
    ∃ (U : S.Opens) (hU : Set.range f ⊆ Set.range U.ι),
      IsAffineHom (IsOpenImmersion.lift U.ι f hU) := by
  sorry

end AlgebraicGeometry
