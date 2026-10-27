/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.AlgebraicGeometry.FiniteLocallyFreePrincipalBasisCover
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.Basic

/-! # Constant degrees multiply for finite locally free morphisms

Source: Stacks Project, Tags 02KA, 02KB and 02KC (Morphisms), and Tag 02M9 (Algebra).
(blueprint: lem-sfb-finite-locally-free-degree-composition)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The composite of finite locally free morphisms of constant degrees `r` and `s` is
finite locally free of degree `r * s`, including zero degrees and empty schemes.

Source: Stacks Project, Tags 02KA, 02KB, 02KC and 02M9.
(blueprint: lem-sfb-finite-locally-free-degree-composition)

Proof: By `lem-trf-finite-locally-free-composition`, the composite is finite locally free.
Fix a point `z` of the base and an affine neighbourhood `Spec A`. Its inverse images in
`Y` and `X` are affine, say `Spec B₀` and `Spec C₀`, by
`def-weil-finite-integral-morphism`. Put `K = κ(z)`, `B = B₀ ⊗[A] K` and
`C = C₀ ⊗[A] K`. By `lem-weil-pbc-fibre-product-affine-spectra`, these give the fibres,
and the degree hypothesis on `g` says `dim_K B = s`.

Use `lem-a1-finite-locally-free-principal-basis-cover` for the affine restriction of `f`.
Its principal generators of the unit ideal remain such after extension to `B`.
The tensor associativity comparison `C = C₀ ⊗[B₀] B` sends
`c ⊗ (b ⊗ k)` to `cb ⊗ k` and has inverse `c ⊗ k ↦ c ⊗ (1 ⊗ k)`.
Localizing and extending each chart basis gives a principal free cover of `C` over `B`
of rank `r`; this uses `def-weil-module-base-change` and
`def-weil-pbc-module-localization-away` and their universal properties.

By `lem-weil-pbc-finite-dim-algebra-artinian` and `lem-sfb-artinian-spectrum-finite`,
`B` is Artinian and semilocal. The cover therefore gives a `B`-basis of `C` with `r`
elements by `lem-sfb-semilocal-constant-rank-basis`, without any reducedness assumption.
Choose a `K`-basis of `B` with `s` elements. Products of the two bases give a `K`-basis
of `C` with `r * s` elements: expansion in the `B`-basis followed by expansion of each
coefficient in the `K`-basis proves both spanning and uniqueness. This computes the
fibre degree by `def-weil-vector-space-dimension`, `def-weil-pbc-free-module` and
`def-pc-finite-locally-free`. If `B = 0`, then `C = 0`; if `r = 0`, the empty basis
also forces `C = 0`. These cover degree zero and empty sources. For an empty base
there are no points at which a fibre degree must be checked. -/
theorem Scheme.Hom.isFiniteLocallyFreeOfDegree_comp {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) (r s : ℕ)
    [f.IsFiniteLocallyFreeOfDegree r] [g.IsFiniteLocallyFreeOfDegree s] :
    (f ≫ g).IsFiniteLocallyFreeOfDegree (r * s) := by
  sorry

end AlgebraicGeometry
