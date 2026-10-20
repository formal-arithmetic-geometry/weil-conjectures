/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q111
-/
module

public import Sheaf.Paper.OrientedNearbyCycles
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.AlgebraicGeometry.FiniteTypeTorsionUniversalStar
import Sheaf.Paper.OrientedNearbyStrictLocalDescription
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection

/-!
# Conditional Künneth formula for oriented nearby cycles

Source: Zheng, Künneth formula for nearby cycles, Theorem A.3(1) with
`Y₁ = Y₂ = B`, pp. 2--3 (local PDF WANTED); the torsion finite-type sufficient
condition for (*) preceding Remark A.2, p. 1 (blueprint: lem-trf-good-oriented-nearby-kunneth).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.OrientedNearbyCycles

/--
Under finite-type and invertible-exponent hypotheses, the specified oriented
Künneth comparison is an isomorphism for bounded Ψ-good inputs.  This is the
conditional assertion of Zheng, Theorem A.3(1), with both base schemes equal
to `B`; it makes no assertion that a pair is Ψ-good.

Proof: apply the universal finite-type torsion condition (*) to the two legs and
their fibre product, then use the strict-local description of oriented nearby
cycles.  At each geometric point, the local comparison factors through two
localized base-change isomorphisms and two projection-formula isomorphisms.
The counit calculation identifies this composite with the specified Künneth
comparison.  Joint conservativity of the strict-local restrictions then gives
`IsIso` globally.  The cited statement dependencies provide these local
comparison, projection, and conservativity results.
(blueprint: lem-trf-good-oriented-nearby-kunneth)
-/
theorem isIso_kunneth_of_isPsiGood
    {T₁ T₂ B : Scheme.{u}} (f₁ : T₁ ⟶ B) (f₂ : T₂ ⟶ B)
    [LocallyOfFiniteType f₁] [QuasiCompact f₁]
    [LocallyOfFiniteType f₂] [QuasiCompact f₂]
    (Λ : Type v) [CommRing Λ] [Finite Λ]
    [HasInvertibleExponent Λ B]
    (L₁ : EtaleDerived T₁ Λ) (L₂ : EtaleDerived T₂ Λ)
    (hL₁ : IsBounded (etaleDatum T₁) (Coeff Λ) L₁)
    (hL₂ : IsBounded (etaleDatum T₂) (Coeff Λ) L₂)
    (hgood₁ : IsPsiGood f₁ Λ L₁) (hgood₂ : IsPsiGood f₂ Λ L₂) :
    IsIso (kunneth f₁ f₂ Λ L₁ L₂) := by
  sorry

end AlgebraicGeometry.OrientedNearbyCycles
