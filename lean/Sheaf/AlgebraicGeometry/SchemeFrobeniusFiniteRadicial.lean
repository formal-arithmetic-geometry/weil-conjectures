/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.AlgebraicGeometry.RelativeFrobeniusGeometricFiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Sheaf.AlgebraicGeometry.RelativeFrobeniusIntegralUniversalHomeomorphism
import Mathlib.FieldTheory.Finite.Basic
import Sheaf.AlgebraicGeometry.RelativeFrobeniusFinite
import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

/-!
# Finiteness and radiciality of the scalar-extended scheme Frobenius

Source: Stacks Project, Tags 0CCD, 0CCB, and 0CCG in `varieties.tex`;
Tags 01WL, 0472, and 01S4 in `morphisms.tex`
(blueprint: lem-trf-scheme-frobenius-finite-radicial).

The scalar-extended q-power Frobenius of a finite-type scheme over the fixed
finite field is finite and radicial.  Radiciality is rendered by Mathlib's
`UniversallyInjective`, equivalent to the residue-field formulation in Tag 01S4.
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.FiniteFieldDatum

/-- The scalar-extended q-power Frobenius is finite and radicial.
Source: Stacks Project, Tags 0CCD, 0CCB, and 0CCG in `varieties.tex`,
and Tags 01WL, 0472, and 01S4 in `morphisms.tex`
(blueprint: lem-trf-scheme-frobenius-finite-radicial).

Proof:
1. Set S = Spec k₀. The datum gives a prime p, a positive a, and q = p^a.
   `model_characteristic` supplies characteristic p. Apply
   `lem-trf-relative-frobenius-finite` to the locally finite type structure
   morphism with n = a to obtain finiteness of its a-fold relative Frobenius.
2. Put Yᵢ = X₀ ×_{S,F_S^i} S. Associativity of fibre products identifies the
   one-step Frobenius twist of Yᵢ with Yᵢ₊₁. Each relative Frobenius
   Yᵢ → Yᵢ₊₁ is a universal homeomorphism by
   `lem-trf-relative-frobenius-universal-homeomorphism`, hence radicial by
   `def-weil-radicial-morphism`. Their composite is radicial by
   `lem-trf-finite-radicial-basechange`. Inductively its projections are the
   i-th absolute Frobenius and the structure morphism: absolute Frobenius is
   natural since ring maps preserve p-th powers. Pullback uniqueness thus
   identifies the a-fold composite with the a-fold relative Frobenius.
   `FiniteField.pow_card` and q = p^a imply F_S^a = id. The final twist is
   canonically X₀ and the first projection of the relative Frobenius becomes
   its q-power absolute Frobenius, proving that model map finite and radicial.
3. `relativeFrobenius` is exactly the scalar extension of that model map.
   By `lem-trf-finite-radicial-basechange`, finite morphisms and universally
   injective morphisms remain so under this base change to k. No separatedness
   or reducedness is used.
-/
theorem relativeFrobenius_isFinite_isRadicial
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    IsFinite (D.relativeFrobenius X₀) ∧
      UniversallyInjective (D.relativeFrobenius X₀) := by
  sorry

end WeilConjectures.FiniteFieldDatum
