/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.AlgebraicGeometry.Fiber
import Sheaf.AlgebraicGeometry.Dimension
import Sheaf.AlgebraicGeometry.Variety

/-!
# Dimension under field extension and base change

Source: blueprint `sec-picard-framework/sk-thm-picard-rr/lem-pc-dim-base-change.md`,
node order 733; Stacks Project, Tag 00P3 (blueprint: lem-pc-dim-base-change).
-/

universe u v w z

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- Dimension is unchanged by scalar extension, and curves remain one-dimensional.
Source: blueprint `sec-picard-framework/sk-thm-picard-rr/lem-pc-dim-base-change.md`,
node order 733; Stacks Project, Tags 00P3 and 04MU (blueprint: lem-pc-dim-base-change).

Proof:
1. Apply `lem-weil-pbc-dimension-preserved-field-extension` (00P3) to `A`: Noether
   normalization gives a finite injective polynomial algebra map, which remains finite
   and injective after the flat extension to `K`; integral extensions preserve dimension.
   By `def-weil-pbc-krull-dimension-ring`, spectrum dimension is ring dimension. Swap
   the tensor factors using the ring isomorphism; prime ideals and inclusions correspond.
2. By `def-pc-curve`, `X` is integral, nonempty, separated and of finite type, with
   dimension one. By `def-weil-finite-type-morphism`, choose a finite affine open cover
   by spectra of finite type algebras (`def-weil-pbc-finite-type-algebra`). Its inverse
   images cover the pullback (`def-pc-base-change`); `lem-weil-pbc-open-fibre-product`
   (01JR) and `lem-weil-pbc-fibre-product-affine-spectra` (01JQ) identify them with the
   spectra of the scalar extensions. Some chart is nonzero; step 1 shows its scalar
   extension has nonnegative dimension and is nonzero, so the pullback is nonempty.
3. Apply `lem-pc-dimension-affine-open-cover` (04MU) to both nonempty schemes. Their
   dimensions are the maxima of the chart dimensions, which agree by step 1, hence one.
-/
theorem dim_base_change :
    (∀ (k : Type u) (K : Type v) (A : Type w) [Field k] [Field K] [CommRing A]
      [Algebra k K] [Algebra k A] [Algebra.FiniteType k A],
      ringKrullDim (A ⊗[k] K) = ringKrullDim A) ∧
    (∀ (k K : Type z) [Field k] [Field K] [Algebra k K]
      {X : Scheme.{z}} (f : X ⟶ Spec (.of k)) [f.IsCurveOverField],
      Scheme.dim (Limits.pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))) = 1) := by
  sorry

end AlgebraicGeometry
