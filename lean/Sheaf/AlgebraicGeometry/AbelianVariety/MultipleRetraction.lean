/-
Copyright (c) 2026 Weil SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil SHEAF contributors
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.CategoryTheory.Monoidal.Grp

import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Rigidity
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Retraction of an abelian inclusion up to multiplication

Source: Milne, Algebraic Groups (iAG2017), Proposition 8.23, printed pp.152-153,
and the translation normalization in the proof of Theorem 8.24, using 8.19.
(blueprint: lem-sfb-abelian-inclusion-multiple-retraction)

Multiplication by a natural number `n` on `B` is the power `𝟙 B ^ n` in the
pointwise group of morphisms, as in `AlgebraicGeometry.torsionSubgroupScheme`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonObj

namespace AlgebraicGeometry

/-- A closed immersion of abelian varieties admits a homomorphism back whose
restriction is multiplication by a positive integer.

Source: Milne, Algebraic Groups (iAG2017), Proposition 8.23 and the proof of
Theorem 8.24, printed pp.152-153, with ambient group `A` and subgroup `B`.
(blueprint: lem-sfb-abelian-inclusion-multiple-retraction)

Proof plan:
1. By `lem-sc-abelian-variety-characterization`, `def-sc-abelian-variety` and
   `lem-sc-av-commutative`, both varieties are smooth, proper, connected,
   geometrically integral commutative group schemes. Apply
   `lem-sfb-smooth-commutative-subgroup-quotient` to obtain the smooth quotient
   `p : A → Q` and its torsor identity. Over the generic point of a nonempty
   affine open of `Q`, its fibre is a torsor under the base change of `B`.
2. By `lem-sfb-abelian-field-extension` this base change is an abelian variety.
   Apply `lem-sfb-commutative-torsor-positive-weight` to obtain a positive
   integer `n` and an equivariant morphism from the generic fibre to `B`.
   Positivity comes from the degree in Milne's Lemma 8.22; no characteristic
   is excluded and `n` need not be invertible in the ground field.
3. Use `thm-pd-spreading-out` parts (2) and (3) and
   `lem-weil-pbc-qcqs-morphism-permanence` to spread the morphism and its
   equivariance identity to a nonempty principal open of the quotient.
   Principal opens indexed by nonzero elements have generic-point limit.
   Their inverse images in the integral variety `A` are dense opens.
4. Apply `lem-sfb-weil-extension-to-abelian-variety` to extend to a morphism
   `φ : A → B`. The identity `φ(a + i(b)) = φ(a) + n b` holds globally by
   `lem-chow-agree-on-dense-open`: its source `A × B` is integral by
   `lem-sfb-abelian-finite-product` and
   `lem-sc-abelian-variety-characterization`. The open where it is known is
   nonempty, hence scheme-theoretically dense; the target is separated.
5. Set `r(a) = φ(a) - φ(0)` using `def-sc-group-scheme`. Then `r(0) = 0`.
   Pull back the preceding identity along `b ↦ (0,b)` to get `r ∘ i = [n]`
   as scheme morphisms, with multiplication as in `def-sc-mult-n`.
6. Apply `lem-sc-rigidity` to the morphism
   `d(x,y) = r(x+y) - r(x) - r(y)` on `A × A`. It vanishes on `A × {0}`,
   so factors through the second projection. Its restriction to `{0} × A`
   is also zero, so it is identically zero. Thus `r` preserves the group law
   and the identity, giving `IsMonHom r` and the stated equality. -/
theorem IsAbelianVariety.exists_multiple_retraction
    {k : Type u} [Field k] (A B : Over (Spec (.of k)))
    [GrpObj A] [IsAbelianVariety A] [GrpObj B] [IsAbelianVariety B]
    (i : B ⟶ A) [IsMonHom i] [IsClosedImmersion i.left] :
    ∃ (n : ℕ), 0 < n ∧ ∃ (r : A ⟶ B), IsMonHom r ∧ i ≫ r = 𝟙 B ^ n := by
  sorry

end AlgebraicGeometry
