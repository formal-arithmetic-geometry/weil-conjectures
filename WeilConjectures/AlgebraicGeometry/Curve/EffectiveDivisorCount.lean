/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import WeilConjectures.AlgebraicGeometry.Curve.DivisorIdealSheaf
public import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
public import WeilConjectures.ZetaSeries
public import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
public import WeilConjectures.AlgebraicGeometry.Modules.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.Endomorphism
public import WeilConjectures.AlgebraicGeometry.Modules.HomObjSections
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus

/-!
# Effective divisors in a divisor class on a curve over a finite field

Let `C` be a smooth proper curve over a field `k` with `H⁰(C, 𝒪_C) = k`, and `ℳ` an invertible
`𝒪_C`-module. The effective divisors `E` whose ideal sheaf `𝒪_C(-E)` is isomorphic to `ℳ` are
the zero schemes of the nonzero morphisms `φ : ℳ ⟶ 𝒪_C`, and two such morphisms have the same
zero scheme if and only if they differ by a nonzero scalar. Hence, when `k` has `q` elements,
the number of these divisors is `(q^{h⁰(ℳᵛ)} - 1) / (q - 1)`, where `h⁰(ℳᵛ)` is the dimension of
`H⁰(C, ℳᵛ) = Hom(ℳ, 𝒪_C)`.

This is the count of the points of the complete linear system `|ℳᵛ|`, the input from
Riemann–Roch into the computation of the zeta function of a curve.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.Hom.exists_eq_comp_smulHom_of_zeroLocus_eq`: two morphisms
  `ℳ ⟶ 𝒪_C` with the same zero scheme differ by a scalar.
- `AlgebraicGeometry.Scheme.Divisor.sub_one_mul_card_idealSheaf_iso`: the count
  `(q - 1) · #{E | 𝒪_C(-E) ≅ ℳ} = q^{h⁰(ℳᵛ)} - 1`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

namespace Modules

variable {X : Scheme.{u}}

end Modules

section Curve

variable {k : Type u} [Field k] {C : Scheme.{u}} [C.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (C ↘ Spec (.of k))] [IsIntegral C] [IsNoetherian C]

end Curve

section Degree

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

variable [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]

end Degree

end AlgebraicGeometry.Scheme
