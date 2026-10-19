/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Irreducible
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.FieldTheory.CommonExtensionFields
import Sheaf.FieldTheory.SepClosedAlgebrasTensorIrreducible

/-!
# Testing geometric irreducibility on finite separable extensions

Source: Stacks Project, Algebra, Tag 037K, `lemma-geometrically-irreducible`,
equivalence of (1) and (2)
(blueprint: lem-zl-geometric-irreducibility-finite-separable-test).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace Algebra

/-- For an arbitrary commutative algebra over a field, irreducibility of its spectrum after
all field extensions is equivalent to irreducibility after all finite separable extensions.
The tensor-product ring has `(r ⊗ a) * (s ⊗ b) = (r * s) ⊗ (a * b)` and unit `1 ⊗ 1`.
`IrreducibleSpace` includes nonemptiness. No reducedness or finite generation is assumed.

Source: Stacks Project, Algebra, Tag 037K, equivalence (1) and (2)
(blueprint: lem-zl-geometric-irreducibility-finite-separable-test).

Proof:
1. Specializing the universal condition to finite separable extensions proves the forward
   implication.
2. For fields `k ⊆ E ⊆ F`, tensor balancing gives mutually inverse ring isomorphisms
   `(R ⊗[k] E) ⊗[E] F ≃ R ⊗[k] F`, sending `(r ⊗ e) ⊗ f` to `r ⊗ (e * f)`
   and `r ⊗ f` to `(r ⊗ 1) ⊗ f`. Multiplication and units agree by
   `lem-weil-pbc-algebra-tensor-pushout-universal-property`. Scalar extension is injective:
   apply `lem-weil-pbc-field-extension-base-change-faithfully-flat` and the zero-ideal case
   of `lem-weil-pbc-faithfully-flat-ideal-contraction`. Similarly `R ⊗[k] k ≃ R`.
3. Assuming the finite separable tests, choose a separable closure `ks/k`
   (`def-pd-separable-closure`). The test at `E = k` makes `Spec R` irreducible and hence
   `R` nonzero by `lem-zl-spectrum-irreducible-nilradical-prime`. Injectivity in step 2
   makes `A = R ⊗[k] ks` nonzero, so its nilradical is proper.
4. If `x * y` in `A` is nilpotent, express `x` and `y` as finite sums of pure tensors
   (`def-weil-pbc-module-tensor-product`). All coefficients lie in one finite separable
   subextension `E/k` of `ks/k`. Lift to `xE,yE` in `R ⊗[k] E`; injectivity in step 2
   detects the nilpotence equation there. The finite separable test and
   `lem-zl-spectrum-irreducible-nilradical-prime` imply that `xE` or `yE` is nilpotent.
   Thus `x` or `y` is nilpotent, the nilradical of `A` is prime, and `Spec A` is irreducible.
5. For any extension `L/k`, use `lem-weil-common-extension-fields` to embed `L` and `ks`
   compatibly over `k` into a field `M`. The spectrum of `M` is irreducible, since its
   nilradical is the proper prime zero ideal. Apply
   `lem-zl-sepclosed-algebras-tensor-irreducible` over the separably closed field `ks`
   to `A` and `M`. It makes `Spec (A ⊗[ks] M)` irreducible; step 2 identifies this
   tensor product with `C = R ⊗[k] M`.
6. Step 2 gives an injective unital map `B = R ⊗[k] L → C`. Injectivity reflects
   nilpotence, so the nilradical of `B` is the inverse image of the nilradical of `C`.
   The latter is proper prime by `lem-zl-spectrum-irreducible-nilradical-prime`.
   Its inverse image is proper prime, and the same criterion makes `Spec B` irreducible.
   This proves the condition for every `L/k`.
-/
theorem irreducibleSpace_tensorProduct_iff_finite_separable
    (k : Type u) (R : Type v) [Field k] [CommRing R] [Algebra k R] :
    (∀ (L : Type (max u v w)) [Field L] [Algebra k L],
      IrreducibleSpace (AlgebraicGeometry.Spec (CommRingCat.of (R ⊗[k] L)))) ↔
    (∀ (E : Type (max u v w)) [Field E] [Algebra k E] [FiniteDimensional k E]
      [Algebra.IsSeparable k E],
      IrreducibleSpace (AlgebraicGeometry.Spec (CommRingCat.of (R ⊗[k] E)))) := by
  sorry

end Algebra
