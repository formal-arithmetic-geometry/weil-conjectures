/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Sheaf.Paper.StrictEtaleIsomorphicStageProjectionInterfaces

/-!
# Compact-support projection from strict étale transports

Source: Zheng, Construction 5.15 and Lemma 5.22
(blueprint: lem-pur-strict-etale-isomorphic-stage-projection).

This is the geometric mate assembly after exact coefficient transports have been
constructed.  It leaves coefficient transport construction to a separate node.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

/-- Assemble normalized compact-support and quotient projection data from exact
finite-level transports.

Proof: tensor-unit normalization gives the inverse-image coefficient squares;
transposing them along the recorded open and proper adjunctions gives the mate
fields of the compact-support transport.  The quotient tensor interchange has
the same composite ring map on both sides, so its normalized derived square is
canonical.  Whiskering the open and proper faces and using associativity yields
the evaluation and quotient cubes in `StrictEtaleTransportProjection`.
Source: Zheng, Construction 5.15 and Lemma 5.22
(blueprint: lem-pur-strict-etale-projection-from-equivalences).
-/
theorem nonempty_strictEtaleTransportProjection_of_equivalences
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (SA : StrictEtaleCompactSupport O ell c) (SB : StrictEtaleCompactSupport O' mu c)
    (TX : StrictEtaleCoefficientTransport a X SA.PX SB.PX)
    (TY : StrictEtaleCoefficientTransport a Y SA.PY SB.PY)
    (TZ : StrictEtaleCoefficientTransport a c.Z SA.PZ SB.PZ)
    (_hTX : ∀ n, (TX.level n).derived.IsEquivalence)
    (_hTY : ∀ n, (TY.level n).derived.IsEquivalence)
    (_hTZ : ∀ n, (TZ.level n).derived.IsEquivalence) :
    Nonempty (StrictEtaleTransportProjection a c SA SB TX TY TZ) := by
  sorry

end AlgebraicGeometry
