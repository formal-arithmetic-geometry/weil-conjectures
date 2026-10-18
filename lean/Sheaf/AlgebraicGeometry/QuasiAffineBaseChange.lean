/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.AlgebraicGeometry.RelativeSpecBaseChange

/-!
# Base change of quasi-affine morphisms

Source: Stacks Project, Morphisms, Tag 01SO, lemma-base-change-quasi-affine
(blueprint: lem-trf-quasi-affine-base-change).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option autoImplicit false

/-- Arbitrary base change preserves quasi-affineness (Stacks Project, Morphisms, Tag 01SO,
lemma-base-change-quasi-affine) (blueprint: lem-trf-quasi-affine-base-change).

Proof plan:
1. By `lem-trf-quasi-affine-relative-spec-embedding` (Tag 01SM), factor `f` as a
   quasi-compact open immersion into the relative spectrum of a quasi-coherent algebra.
2. The fibre-product universal property identifies the induced map between the two base
   changes as the pullback of that immersion. It is open by
   `lem-weil-pbc-open-immersion-base-change` and quasi-compact by clause (3) of
   `lem-weil-pbc-qcqs-morphism-permanence`; neither requires a condition on `g`.
3. By `lem-weil-pbc-relative-spec-base-change`, the base-changed relative spectrum is
   canonically isomorphic over `S'` to the relative spectrum of the pulled-back algebra.
   Transporting the immersion along this isomorphism preserves openness and quasi-compactness.
4. The converse of `lem-trf-quasi-affine-relative-spec-embedding` gives quasi-affineness
   of the projection to `S'`. No finite-presentation assumption enters these steps. -/
theorem isQuasiAffineHom_baseChange {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (hf : IsQuasiAffineHom f) :
    IsQuasiAffineHom (pullback.snd f g) := by
  sorry

end AlgebraicGeometry
