/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil SHEAF project
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Valuation probes with a prescribed generic field

Source: Stacks Project, Tag 01J8, parts (1)-(2), with the given field-point morphism;
Tag 00IA supplies the dominating valuation subring
(blueprint: lem-sfb-scheme-specialization-prescribed-field-probe).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A field-valued point extends over a valuation subring of the same field centered at
any specialization of its image. The canonical `IsFractionRing A K` instance for
`A : ValuationSubring K` expresses that its fraction field is exactly `K`.

Source: Stacks Project, Tag 01J8, parts (1)-(2), and Tag 00IA
(blueprint: lem-sfb-scheme-specialization-prescribed-field-probe).

Proof:
1. Choose an affine open `U = Spec R` containing `y`. Since the image of the unique
   point of `Spec K` specializes to `y`, it also lies in `U`; factor the given morphism
   through `U`. Write that morphism as `Spec φ` for `φ : R →+* K`. If `p` represents `y`
   and `q = ker φ` represents the general point, the basic-open test gives `q ≤ p`.
2. Put `S = φ(R)` and let `P` be the image of `p` in `S`. Its inverse image is `p`,
   so it is prime. Embed the local domain `S_P` in `K` by fractions. Its maximal ideal
   contracts to `P`, and hence to `p` in `R`, using
   `def-weil-pbc-localization-at-prime`.
3. Apply `lemma-nagata-local-domain-valuation-dominates`, namely
   `LocalSubring.exists_le_valuationSubring`, to this local subring of `K`. The resulting
   valuation subring `A` dominates it. Consequently the maximal ideal of `A` contracts
   to `p` under the resulting map `R →+* A`.
4. Define `v` by the spectrum of that ring map followed by `U → Y`. Contraction sends
   the closed point to `y`. The composite `R → A → K` is the original `φ`, so
   contravariant functoriality of `Spec` gives equality with the given morphism `u`,
   including its prescribed field map. -/
theorem Scheme.exists_valuationSubring_of_specializes_fieldPoint
    {Y : Scheme.{u}} {K : Type u} [Field K] (u : Spec (CommRingCat.of K) ⟶ Y)
    (y : Y) (h : u (IsLocalRing.closedPoint K) ⤳ y) :
    ∃ (A : ValuationSubring K) (v : Spec (CommRingCat.of A) ⟶ Y),
      v (IsLocalRing.closedPoint A) = y ∧
      Spec.map (CommRingCat.ofHom A.subtype) ≫ v = u := by
  sorry

end AlgebraicGeometry
