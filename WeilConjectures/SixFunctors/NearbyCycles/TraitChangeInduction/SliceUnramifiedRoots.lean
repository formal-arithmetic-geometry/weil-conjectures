/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.SliceGaloisFields
public import WeilConjectures.TraceFormula.Specialization.SliceTraitCoordResidue
public import WeilConjectures.RingTheory.Valuation.DiscreteSubfieldFullResidue
public import WeilConjectures.RingTheory.Valuation.UnramifiedCompositum
public import WeilConjectures.FieldTheory.PowIndependentSeparable

/-!

# Unramified radical subfields of the slice compositum

Let `D` be a slice trait over a strictly henselian trait `R₁ = R` with geometric generic point
`Ω₁ = Ω` and residue characteristic `p`, such that the residue field of `R' = D.R` is separable
algebraic over `κ(x̄)` for an element `x ∈ R'` with residue transcendental over the residue field
`κ` of `R`. Adjoining to `Frac R` compatible `p ^ n`-th roots `θ i n` of lifts of a `p`-basis of
`κ` gives a discretely valued subfield `K₀ ⊆ Ω` with the full residue field
(`IsDiscreteValuationRing.exists_discrete_subfield_full_residue`). We show
(`AlgebraicGeometry.SliceTrait.exists_unramified_subfields`) that the field
`B = Frac(R')(θ i n : i, n) ⊆ Ω'`, which contains `K₀` and `R'`, is still discretely valued with
the value group of `R'`, and that the residues of its integral elements are sums of products of
residues of `R'` and of residues of elements of `Ω`: the `p`-basis of `κ` stays `p`-independent in
the residue field of `R'` (`Field.PowIndependent.map_of_isSeparable`), so that adjoining the
`θ i n` to `Frac R'` is unramified (`ValuationSubring.unramified_adjoin_roots`).

-/

@[expose] public section

universe u

open IsLocalRing IntermediateField

namespace AlgebraicGeometry.SliceTrait

attribute [local instance] algebraR algebraΩ algebraBaseΩ algebraRΩ

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsStrictlyHenselianLocalRing R] {Ω : Type u} [Field Ω] [Algebra R Ω]
  {κ : Type u} [Field κ] {b : R →+* κ} (D : SliceTrait (algebraMap R Ω) b)

attribute [local instance] algebraFracΩ algebraFrac algebraValuationSubring
  algebraBaseValuationSubring FractionRing.liftAlgebra

end AlgebraicGeometry.SliceTrait
