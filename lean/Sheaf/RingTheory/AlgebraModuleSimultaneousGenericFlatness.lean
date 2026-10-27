/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic

import Mathlib.Algebra.TrivSqZeroExt.Basic
import WeilConjectures.RingTheory.GenericFlatness

/-! # Simultaneous generic flatness of an algebra and a finite module

Source: Stacks Project, Algebra, Tag 051T, `lemma-generic-flatness`, conclusion (a),
as applied in Tag 0573, `lemma-scheme-theoretically-dense-generic-fibre`.
(blueprint: lem-trf-algebra-module-simultaneous-generic-flatness)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Module

/-- Over an arbitrary domain, a finite type algebra and a finite module over it become
simultaneously flat over the original base after inverting one nonzero base element.
The module action in the second conjunct is restriction of scalars along `algebraMap A B`;
it is the action induced by the canonical maps `A → B → B[1/a]`.

Source: Stacks Project, Algebra, Tag 051T, `lemma-generic-flatness`, conclusion (a);
Tag 0573, `lemma-scheme-theoretically-dense-generic-fibre`, third proof paragraph.
(blueprint: lem-trf-algebra-module-simultaneous-generic-flatness)

Proof:
1. Choose finite algebra generators `bᵢ` of `B` and module generators `mⱼ` of `M`.
   The square-zero algebra `C = TrivSqZeroExt B M` is finite type over `A`: its generators
   are `(bᵢ, 0)` and `(0, mⱼ)`, since every `(b, m)` is a polynomial in these elements.
   This uses def-sc-trivial-square-zero-extension and the two finite-generation definitions.
2. Apply lem-sbc-finite-type-algebra-generic-flatness to `A → C`. Obtain `a ≠ 0` such
   that `F = C[1/(algebraMap A B a, 0)]` is flat over `A`.
3. Write `s = algebraMap A B a` and `t = (s, 0)`. The inclusions
   `b/s^e ↦ (b, 0)/t^e` and `m/s^e ↦ (0, m)/t^e`, together with projections
   `(b, m)/t^e ↦ b/s^e` and `(b, m)/t^e ↦ m/s^e`, make the two localizations
   `A`-module retracts of `F`. These maps are well-defined: a fraction equality in `F`
   says that for some `k`, both `s^k * (s^e' * b - s^e * b') = 0` and
   `s^k • (s^e' • m - s^e • m') = 0`. Projecting gives the required fraction equalities;
   inclusions have a zero second or first coordinate. Fraction addition gives additivity,
   and multiplication by `(algebraMap A B x, 0)` gives `A`-linearity. Both projection-inclusion
   composites are the identity, as is checked on fractions.
4. Apply lem-weil-pbc-flat-module-retract (`Module.Flat.of_retract`) to each retract.
   The common `a` gives both flatness assertions, with the stipulated scalar actions.
   No Noetherianity or finite presentation is used. -/
theorem exists_nonzero_flat_localizationAway_algebra_module
    (A : Type u) (B : Type v) (M : Type w)
    [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module B M] [Module.Finite B M]
    (hB : (algebraMap A B).FiniteType) :
    ∃ a : A, a ≠ 0 ∧
      ((algebraMap B (Localization.Away (algebraMap A B a))).comp (algebraMap A B)).Flat ∧
      @Module.Flat A (LocalizedModule.Away (algebraMap A B a) M) _ _
        (Module.compHom _ (algebraMap A B)) := by
  sorry

end Module
