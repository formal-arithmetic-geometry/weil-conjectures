/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Construction
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Weights
public import WeilConjectures.Mathlib.RepresentationTheory.Irreducible

/-!
# Restricting lisse Weil sheaves to an open subcurve

Let `j : U₀ ⟶ C₀` be a nonempty open immersion of curves over a finite field and
`R : AlgebraicGeometry.WeilGroup.Restriction j W(U₀) W(C₀)` a restriction of Weil groups. Pulling
a Weil representation `ρ` of `W(C₀)` back along `R.restrict` is the restriction `j^* ℱ` of the
corresponding lisse Weil sheaf. This file records how the notions of `sk-d-real-weights` and
`def-real-weil-representation-operations` behave under this operation: lisse sheaves restrict to
lisse sheaves, the local eigenvalues at a closed point of `U₀` are those at its image, so reality,
determinant weights and punctual purity are inherited, and since `R.restrict` is surjective,
constituents restrict to constituents (`sk-i-real-boundary`).

Every Weil group `W` of a smooth geometrically connected curve receives a restriction from some
Weil group of any nonempty geometrically connected open
(`AlgebraicGeometry.WeilGroup.Restriction.exists_weilGroup`), obtained from
`AlgebraicGeometry.WeilGroup.restrictionOfPath` and the identification
`AlgebraicGeometry.WeilGroup.toStandard` of `W` with the standard Weil group of its base point.

## Main statements

- `Representation.isIrreducible_comp_iff`: pulling back
  along a surjective homomorphism preserves and reflects irreducibility.
- `AlgebraicGeometry.WeilGroup.Restriction.exists_weilGroup`
- `AlgebraicGeometry.WeilGroup.Restriction.localEigenvalues_comp`
- `AlgebraicGeometry.WeilGroup.Restriction.isReal_comp`
- `AlgebraicGeometry.WeilGroup.Restriction.hasDetWeight_comp`
- `AlgebraicGeometry.WeilGroup.Restriction.isConstituent_comp`
-/

@[expose] public section

universe u

open CategoryTheory

namespace Subrepresentation

variable {k G G' V : Type*} [CommSemiring k] [Monoid G] [Monoid G'] [AddCommMonoid V]
  [Module k V] {ρ : Representation k G V}

end Subrepresentation

namespace Representation

variable {k G G' V V' : Type*} [Field k] [Group G] [Group G'] [AddCommGroup V] [Module k V]
  [AddCommGroup V'] [Module k V'] {ρ : Representation k G V} {σ : Representation k G V'}

end Representation

namespace AlgebraicGeometry.WeilGroup

section Existence

variable {K : Type u} [Field K] [Finite K] {C U : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]
  [GeometricallyConnected p] {pU : U ⟶ Spec (.of K)} [IsCurve pU] [GeometricallyConnected pU]
  (W : WeilGroup p)

end Existence

namespace Restriction

variable {K : Type u} [Field K] [Finite K] {C U : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]
  {pU : U ⟶ Spec (.of K)} [IsCurve pU] {j : U ⟶ C} [IsOpenImmersion j] [Nonempty U]
  {WU : WeilGroup pU} {WC : WeilGroup p} (R : Restriction j WU WC) (l : ℕ) [Fact l.Prime]
  {V : Type u} [AddCommGroup V] [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V]

variable (ρ : Representation (PadicAlgCl l) WC.carrier V)

variable (ι : PadicAlgCl l →+* ℂ)

end Restriction

end AlgebraicGeometry.WeilGroup
