/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Weights

@[expose] public section

/-!
# Cohomology and the Euler series of a Weil representation

For an abelian sheaf `A` on the small étale site of a scheme `C`, ordinary étale cohomology
`Hⁱ(C, A) = RⁱΓ(C, A)` is Mathlib's `CategoryTheory.Sheaf.H` at the Grothendieck topology
`C.smallEtaleTopology`, and cohomology with proper support `H_cⁱ(C, A)` is
`AlgebraicGeometry.Etale.compactlySupportedCohomology`, with scoped notation `H_c(f)[A](i)`.
Neither is redefined here.

What is new in this file is the *Euler series* of a lisse Weil representation `ρ` on a curve
`p : C ⟶ Spec K` over a finite field, relative to an embedding `ι : ℚ̄_ℓ →+* ℂ`:

`L_ι(C₀, ρ, T) = ∏_{x ∈ |C₀|} ι P_x(ρ, T ^ e_x)⁻¹ ∈ 1 + T ℂ⟦X⟧`,

a product over the closed points of `C₀`, where `P_x(ρ, T)` is the local polynomial
`AlgebraicGeometry.WeilGroup.localPolynomial` and `e_x = p.degreeOver x` is the residue degree.
The product is locally finite: only finitely many factors contribute to a fixed coefficient,
since there are only finitely many closed points of bounded degree
(`AlgebraicGeometry.Scheme.Hom.finite_setOf_degreeOver_le`). Accordingly it is taken in the
product topology on `ℂ⟦X⟧`, for which `open scoped PowerSeries.WithPiTopology` supplies the
instances.

## Main definitions

- `AlgebraicGeometry.WeilGroup.eulerSeries` : the Euler series `L_ι(C₀, ρ, T)`.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} {p : C ⟶ Spec (.of K)}

namespace WeilGroup

variable (W : WeilGroup p) (l : ℕ) [Fact l.Prime] {V : Type*} [AddCommGroup V]
  [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V]
  (ρ : Representation (PadicAlgCl l) W.carrier V) (ι : PadicAlgCl l →+* ℂ)

open scoped PowerSeries.WithPiTopology in
/-- Blueprint `sk-d-real-cohom`: Cohomology and the Euler series.

The Euler series `L_ι(C₀, ρ, T) = ∏_{x ∈ |C₀|} ι P_x(ρ, T ^ e_x)⁻¹` of a Weil representation
`ρ`, the locally finite product over the closed points `x` of the curve of the inverses of the
local polynomials `P_x(ρ, T)` of `AlgebraicGeometry.WeilGroup.localPolynomial`, transported to
`ℂ` along `ι` and substituted into `T ^ e_x` for the residue degree `e_x = p.degreeOver x`.

Each factor is a formal power series with constant term `1`, so the product lies in
`1 + T ℂ⟦X⟧`; it is taken in the product topology on `ℂ⟦X⟧`, in which it converges because
only finitely many closed points have degree below any given bound. -/
noncomputable def eulerSeries : PowerSeries ℂ :=
  ∏' x : C.finitePoints,
    ((((W.localPolynomial l ρ x.1).map ι).comp (Polynomial.X ^ p.degreeOver x.1) :
      Polynomial ℂ) : PowerSeries ℂ)⁻¹

end WeilGroup

end AlgebraicGeometry
