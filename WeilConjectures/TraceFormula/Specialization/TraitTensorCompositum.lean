/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra
public import WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisCompositum

/-!

# The compositum of the geometric generic points of two traits

Let `R₁ ⟶ R` be a ring map, `Ω₁` a field over `R₁` and `Ω` an algebraically closed field over
`R` and `Ω₁`, compatibly over `R₁` (typically: `R₁ ⟶ R` a map of traits and `Ω₁`, `Ω` their
geometric generic points). Put `T = Ω₁ ⊗_{R₁} R`.

* `Spec T` is the fibre product `Spec Ω₁ ×_{Spec R₁} Spec R`
  (`AlgebraicGeometry.isPullback_traitTensor`).
* The product map `T ⟶ Ω` (`AlgebraicGeometry.traitTensorLift`) takes values in the compositum
  `L = Ω₁(R) ⊆ Ω` (`AlgebraicGeometry.traitTensorCompositum`); when `Spec T` has at most one point,
  `T ⟶ L` is surjective (`AlgebraicGeometry.surjective_traitTensorToCompositum`), so `L` is the
  residue field of the point of `Spec T`.
* Consequently `ρ : Spec Ω ⟶ Spec T` factors as `Spec Ω ⟶ Spec L^sep ⟶ Spec L ⟶ Spec T`
  (`AlgebraicGeometry.traitTensorSepPoint_comp_traitTensorCompositumGalois_comp`) with
  `L^sep` the separable closure of `L` in `Ω`: the first factor is a universal homeomorphism
  (`Ω / L^sep` is purely inseparable), the middle one is the spectrum of the Galois extension
  `L^sep / L` and the last one is a closed immersion and a universal homeomorphism when `Spec T` is
  a point (`AlgebraicGeometry.isUniversalHomeomorphism_traitTensorCompositumPoint`).

This generalises `AlgebraicGeometry.traitGenericSpecMap_factor` (the case `R₁ = k'⟦t⟧`,
`R = K⟦t⟧`).

-/

@[expose] public section

universe u

open CategoryTheory Limits IntermediateField

open scoped TensorProduct

namespace AlgebraicGeometry

variable (R₁ R Ω₁ Ω : Type u) [CommRing R₁] [CommRing R] [Algebra R₁ R] [Field Ω₁]
  [Algebra R₁ Ω₁] [Field Ω] [Algebra R Ω] [Algebra Ω₁ Ω] [Algebra R₁ Ω]
  [IsScalarTower R₁ R Ω] [IsScalarTower R₁ Ω₁ Ω]

end AlgebraicGeometry
