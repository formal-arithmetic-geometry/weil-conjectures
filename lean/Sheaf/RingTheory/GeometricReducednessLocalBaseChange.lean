/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q118
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Nilpotent.Defs

import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.FieldTheory.CommonExtensionFields
import Sheaf.RingTheory.PowerGeneratedSpectrumHomeomorphism
import Sheaf.RingTheory.GeometricReducednessFiniteInseparableTest

/-!
# Geometric reducedness of local rings after extending the base field

Source: Stacks Project, Varieties, Tags 0384 and 035W
(blueprint: lem-trf-geometric-reducedness-local-base-change).
-/

@[expose] public section

set_option autoImplicit false

universe u v w t

open scoped TensorProduct

namespace Algebra

/-- The local rings at corresponding primes before and after any field extension are
geometrically reduced simultaneously. Both sides quantify over every extension field;
no finiteness, Noetherian, algebraicity, or closed-point assumption is made.
The right-factor action on `R ⊗[k] L` is explicitly supplied by `rightAlgebra` and then
inherited by its localization. The identity application only supplies this fixed instance.
The test-field universe dominates the universes of both fields and of the algebra;
`t` allows an arbitrary further enlargement.

Source: Stacks Project, Varieties, Tag 0384 (geometrically reduced upstairs), expressed
on local rings by Tag 035W (blueprint: lem-trf-geometric-reducedness-local-base-change).

Proof plan:
1. For an extension `H/L`, localization base change and tensor cancellation identify
   `B ⊗[L] H` as a further localization of `A ⊗[k] H`, where `A = R_p` and
   `B = (R ⊗[k] L)_q`. Thus reducedness of the latter implies that of the former:
   if a fraction has zero power, a denominator annihilates a power of its numerator,
   so reducedness annihilates the numerator after another denominator multiplication.
   Use lem-weil-pbc-localization-base-change and lem-weil-pbc-tensor-cancel-base-change.
2. Conversely fix a finite purely inseparable extension `E/k` and put `C = A ⊗[k] E`.
   Field-extension base change is faithfully flat, hence injective. In characteristic
   `p > 0`, the generators `1 ⊗ e` have positive `p`-power in `A` and are annihilated
   by a positive power of `p`. Apply lem-pur-power-generated-spectrum-homeomorphism
   to see that `Spec C → Spec A` is a homeomorphism. In characteristic zero `E = k`.
   Consequently `C` is local with a unique maximal ideal over the maximal ideal of `A`.
   This uses def-weil-pbc-finite-purely-inseparable-extension and
   lem-weil-pbc-field-extension-base-change-faithfully-flat, together with
   lem-weil-pbc-faithfully-flat-universally-injective.
3. By lem-weil-common-extension-fields choose compatible embeddings of `E` and `L`
   into a common field `F`. Tensor cancellation identifies `(R ⊗[k] L) ⊗[L] F`
   with `T = R ⊗[k] F`. The map from `R ⊗[k] L` is faithfully flat by
   lem-weil-pbc-field-extension-base-change-faithfully-flat. Choose a prime `Q` above
   `q` using lem-weil-pbc-faithfully-flat-surjective-spectrum, and put `D = T_Q`.
   Its contraction to `R` is `p`.
4. The upstairs condition makes `B ⊗[L] F` reduced. Tensor cancellation and
   localization base change identify `D` as its further localization, so `D` is reduced
   by step 1's fraction calculation.
5. Contract `Q` to a prime `P` of `R ⊗[k] E`. Localization base change and tensor
   cancellation identify `C` with localization away from `R \ p`. The prime induced
   by `P` in `C` lies over the maximal ideal of `A`, so step 2 makes it the maximal
   ideal of `C`. All elements outside `P` are therefore units in `C`, giving
   `(R ⊗[k] E)_P ≅ C` by mutually inverse fraction maps.
6. Field-extension base change for `F/E` is faithfully flat, hence flat by
   def-weil-pbc-faithfully-flat-ring-map. Tensor cancellation and
   lem-weil-pbc-flat-local-ring-maps give a flat local homomorphism `C → D`.
   It is faithfully flat by lem-weil-pbc-flat-local-hom-faithfully-flat.
7. By lem-weil-pbc-faithfully-flat-universally-injective this map is injective.
   A nilpotent element of `C` maps to zero in the reduced ring `D`, so is zero.
   Thus `A ⊗[k] E` is reduced for every finite purely inseparable `E/k`, including `k`.
8. Apply lem-trf-geometric-reducedness-finite-inseparable-test to `A` to obtain
   reducedness after every extension of `k`, completing the equivalence. -/
theorem isReduced_localization_tensorProduct_iff (k : Type u) (L : Type v) (R : Type w)
    [Field k] [Field L] [CommRing R] [Algebra k L] [Algebra k R]
    (q : Ideal (R ⊗[k] L)) [q.IsPrime] :
    (∀ (E : Type (max u v w t)) [Field E] [Algebra k E],
      IsReduced (Localization.AtPrime
        (q.comap (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] L).toRingHom) ⊗[k] E)) ↔
    @_root_.id (∀ [Algebra L (R ⊗[k] L)], Prop)
      (fun [Algebra L (R ⊗[k] L)] ↦
        ∀ (H : Type (max u v w t)) [Field H] [Algebra L H],
          IsReduced (Localization.AtPrime q ⊗[L] H))
      (Algebra.TensorProduct.rightAlgebra (R := k) (A := R) (B := L)) := by
  sorry

end Algebra
