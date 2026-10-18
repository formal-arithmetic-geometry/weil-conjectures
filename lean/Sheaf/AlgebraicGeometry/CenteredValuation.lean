/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Centred valuations on integral scheme components

Source: Temkin, *Stable modification of relative curves*, Proposition 3.2.6
(blueprint: def-trf-centred-valuation).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

/-- A valuation subring of the function field of the component with generic point `η`, with
 a morphism whose restriction along the canonical inclusion in that field is exactly the
 specified generic-point morphism. The caller supplies that `η` is a component's generic point
 of a reduced scheme; its residue field is then canonically that component's function field.
 Source: Temkin, §3.2, definition of `Val_K(S)` preceding Corollary 3.2.5, p. 16
 (blueprint: def-trf-centred-valuation).
-/
def IsCenteredValuation {Z : Scheme.{u}} (η : Z) (V : ValuationSubring (Z.residueField η))
    (v : Spec (.of V) ⟶ Z) : Prop :=
  Spec.map (CommRingCat.ofHom V.toSubring.subtype) ≫ v = Z.fromSpecResidueField η

end AlgebraicGeometry
