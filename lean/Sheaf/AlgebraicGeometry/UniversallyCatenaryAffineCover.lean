/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Universal catenarity on affine opens

Source: Stacks Project, Morphisms, Lemma 29.17.1, Tag 02J9 (blueprint:
lem-trf-universally-catenary-affine-cover).
-/

@[expose] public section

set_option autoImplicit false

universe u

open AlgebraicGeometry

namespace AlgebraicGeometry

/-- Universal catenarity passes from an affine open cover to every affine open.

Source: Stacks Project, Morphisms, Tag 02J9, implication (4) implies (3).
(blueprint: lem-trf-universally-catenary-affine-cover).

Proof: Fix an affine open `V` and a finite-type algebra over its ring of sections.
The associated affine morphism is locally of finite type. Refine its source by
affine opens mapping into the given cover; the affine-pair criterion gives finite
type coordinate maps, so universal catenarity of the cover rings gives catenarity
on the source charts. Apply the catenary affine-cover criterion
`lem-trf-catenary-affine-open-cover` to obtain catenarity of the arbitrary finite-type
algebra, and use the definition of universal catenarity. Local Noetherianity gives
Noetherianity of the ring of sections on `V`.
-/
theorem universallyCatenary_of_affineOpenCover
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    {I : Type u} (U : I → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)
    (hcat : ∀ i, IsUniversallyCatenary Γ(X, U i)) :
    ∀ V : X.Opens, IsAffineOpen V → IsUniversallyCatenary Γ(X, V) := by
  sorry

end AlgebraicGeometry
