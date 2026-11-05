/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.SliceUnramifiedRoots
public import WeilConjectures.TraceFormula.Specialization.SliceTraitAlgebraic
public import WeilConjectures.RingTheory.Valuation.FrobeniusLiftApprox
public import WeilConjectures.RingTheory.Valuation.GaussResidue
public import WeilConjectures.FieldTheory.FrobeniusClosedBasisSubfield

/-!

# Lifts of Frobenius-closed bases in the slice compositum

Let `D` be the strict-localization slice trait over a strictly henselian trait `R` with residue
characteristic `p`, and `L = Ω(R') ⊆ Ω'` its compositum. Every element `α ∈ L` lies, together with
the coordinate `x`, in a discretely valued subfield `D₀ ⊆ L` whose residue field `E` is a finite
separable extension of `k(x̄)`, `k` the (algebraically closed) residue field of `Ω`. The abstract
package `ValuationSubring.exists_frobeniusLift_package` applied to lifts of a Frobenius-closed
`k`-basis of `E` (`FrobeniusClosedBasis.exists_of_subfield`) then gives the approximation package
used in the proof of the relative separable closedness of the slice composita
(`AlgebraicGeometry.SliceTrait.exists_frobeniusLift_package`).

The field `D₀ = K₀(x, a₁, …, aₙ)` is generated over the discrete subfield `K₀ ⊆ Ω` with full
residue field by the coordinate and finitely many elements of `R'`. It is discretely valued
since it lies in the unramified radical extension `B` of `Frac R'`
(`AlgebraicGeometry.SliceTrait.exists_unramified_subfields`), its residue field is separable over
`k(x̄)` for the same reason, and finite over `k(x̄)` by the Gauss valuation on `K₀(x)`
(`ValuationSubring.residue_mem_adjoin_of_mem_adjoin`), since `R'` is algebraic over `R[x]`.

-/

@[expose] public section

universe u

open IsLocalRing IntermediateField

namespace AlgebraicGeometry.SliceTrait

attribute [local instance] algebraR algebraΩ algebraBaseΩ algebraRΩ

section General

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsStrictlyHenselianLocalRing R] {Ω : Type u} [Field Ω] [Algebra R Ω]
  {κ : Type u} [Field κ] {b : R →+* κ} (D : SliceTrait (algebraMap R Ω) b)

attribute [local instance] algebraFracΩ algebraFrac algebraValuationSubring
  algebraBaseValuationSubring

end General

section StrictLocalization

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsStrictlyHenselianLocalRing R] {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {a : R →+* Ω}
  (ha : Function.Injective a) (halg : letI := a.toAlgebra; Algebra.IsAlgebraic R Ω)
  {κ : Type u} [Field κ] [IsSepClosed κ] {b : R →+* κ} (hb : RingHom.ker b = maximalIdeal R)

attribute [local instance] algebraValuationSubring algebraBaseValuationSubring

local notation "𝒟" => sliceTraitOfStrictLocalization (a₁ := a) (b₁ := b) ha halg hb

end StrictLocalization

end AlgebraicGeometry.SliceTrait
