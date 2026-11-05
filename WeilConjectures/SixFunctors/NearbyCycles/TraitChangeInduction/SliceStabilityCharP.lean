/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.SliceGaloisFields
public import WeilConjectures.TraceFormula.Specialization.SliceTraitValuation
public import WeilConjectures.RingTheory.Valuation.ArtinSchreierNormalForm
public import WeilConjectures.RingTheory.Valuation.GaloisResidueRoot
public import WeilConjectures.TraceFormula.Specialization.SliceTraitAlgebraic
public import WeilConjectures.TraceFormula.Specialization.SliceTraitCoordResidue
public import WeilConjectures.RingTheory.DiscreteValuationRing.CompletionStrictlyHenselian
public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.SliceFrobeniusLift

/-!

# Relative separable closedness of the slice composita, equal characteristic

Let `D₁ ⟶ D₂` be a morphism of strict-localization slice traits over a change of traits
`R₁ ⟶ R₂`, with composita `Lᵢ = Ωᵢ(Sᵢ(x))`. In characteristic `p > 0`, an Artin–Schreier
equation over `L₁` which has a root in `L₂` has a root in `L₁`
(`SliceTrait.Hom.exists_artinSchreier_root_of_charP`). This is the stability theorem of Ohm and
Kuhlmann for `L₁ = Ω₁(x)^{sh}` in the case needed (F.-V. Kuhlmann, *Elimination of
ramification I*, Trans. AMS 362 (2010), Prop. 4.14), via the abstract normal form
`exists_artinSchreier_root_of_approx`.

The inputs are:
* the approximation of the elements of `L₁` by combinations of lifts of a Frobenius-closed basis
  of a residue function field (`SliceTrait.exists_frobeniusLift_approx`);
* the residue `x̄` of the coordinate is not a `p`-th power in the residue field of `L₂`
  (`SliceTrait.valuation_coord_sub_pow_eq_one`);
* Hensel's lemma for Artin–Schreier equations over `L₁` (`SliceTrait.exists_artinSchreier_root`).

-/

@[expose] public section

universe u

open IsLocalRing IntermediateField

namespace AlgebraicGeometry.SliceTrait

attribute [local instance] algebraR algebraΩ algebraBaseΩ algebraRΩ

section StrictLocalization

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsStrictlyHenselianLocalRing R] {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {a : R →+* Ω}
  (ha : Function.Injective a) (halg : letI := a.toAlgebra; Algebra.IsAlgebraic R Ω)
  {κ : Type u} [Field κ] [IsSepClosed κ] {b : R →+* κ} (hb : RingHom.ker b = maximalIdeal R)

local notation "𝒟" => sliceTraitOfStrictLocalization (a₁ := a) (b₁ := b) ha halg hb

end StrictLocalization

section General

variable {R : Type u} [CommRing R] [IsLocalRing R] {Ω : Type u} [Field Ω] [Algebra R Ω]
  {κ : Type u} [Field κ] {b : R →+* κ} (D : SliceTrait (algebraMap R Ω) b)

end General

section StrictLocalization

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsStrictlyHenselianLocalRing R] {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {a : R →+* Ω}
  (ha : Function.Injective a) (halg : letI := a.toAlgebra; Algebra.IsAlgebraic R Ω)
  {κ : Type u} [Field κ] [IsSepClosed κ] {b : R →+* κ} (hb : RingHom.ker b = maximalIdeal R)

local notation "𝒟" => sliceTraitOfStrictLocalization (a₁ := a) (b₁ := b) ha halg hb

end StrictLocalization

end AlgebraicGeometry.SliceTrait

namespace AlgebraicGeometry.SliceTrait.Hom

attribute [local instance] algebraR algebraΩ algebraBaseΩ algebraRΩ

variable {R₁ R₂ : Type u} [CommRing R₁] [IsDomain R₁] [IsDiscreteValuationRing R₁]
  [IsStrictlyHenselianLocalRing R₁] [CommRing R₂] [IsDomain R₂] [IsDiscreteValuationRing R₂]
  [IsStrictlyHenselianLocalRing R₂] {ι : R₁ →+* R₂} {Ω₁ Ω₂ : Type u} [Field Ω₁] [Field Ω₂]
  [IsAlgClosed Ω₁] [IsAlgClosed Ω₂] {c : Ω₁ →+* Ω₂} {a₁ : R₁ →+* Ω₁} {a₂ : R₂ →+* Ω₂}
  (ha₁ : Function.Injective a₁) (halg₁ : letI := a₁.toAlgebra; Algebra.IsAlgebraic R₁ Ω₁)
  (ha₂ : Function.Injective a₂) (halg₂ : letI := a₂.toAlgebra; Algebra.IsAlgebraic R₂ Ω₂)
  {κ : Type u} [Field κ] [IsSepClosed κ] {b₁ : R₁ →+* κ} {b₂ : R₂ →+* κ}
  (hb₁ : RingHom.ker b₁ = maximalIdeal R₁) (hb₂ : RingHom.ker b₂ = maximalIdeal R₂)

local notation "𝒟₁" => sliceTraitOfStrictLocalization (a₁ := a₁) (b₁ := b₁) ha₁ halg₁ hb₁
local notation "𝒟₂" => sliceTraitOfStrictLocalization (a₁ := a₂) (b₁ := b₂) ha₂ halg₂ hb₂

end AlgebraicGeometry.SliceTrait.Hom
