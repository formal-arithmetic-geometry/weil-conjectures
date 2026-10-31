/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ScalarFibreComponentData

/-! # Objectwise scalar fibre maps before naturality and coherence -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry.Scheme.AdicFibreComparison
open ContinuousRational AlgebraicGeometry.ProEtale

variable {k : Type u} [Field k] (l : ℕ) [Fact l.Prime] [Fact (IsUnit (l : k))]
  (R : ContinuousRational.Family.{u} l)

/-- Objectwise normalized scalar maps are natural in every rational heart morphism.
Source: BS 6.8.4(4), 6.8.14--6.8.15.
(blueprint: lem-per-scalar-fibre-naturality).

Proof: Choose a common adapted stratification and pointed affine etale lattice chart
for the source and target. Full faithfulness of lisse rationalization expresses the
restricted map as an integral map divided by a uniformizer power. The finite stalk
scalar comparison is natural on that integral map, since its two composites send a
tensor of a germ to the germ of the same tensor section. Compose with every quotient
projection, then use joint monicity of limit projections and the reduction-cone
equation to obtain integral naturality. The fractions formula for normalized fibres
multiplies both routes by the same inverse uniformizer power after scalar inclusion,
so integral naturality gives naturality for the original rational morphism. Equal
fraction representatives differ by a uniformizer-power-annihilated map; this difference
vanishes on localization. Changing charts or lattices is handled by applying the same
calculation to their fractional comparison maps on a common refinement. The universal
local normalization of d therefore gives the equation in the original point functors.
Zero fibres and zero lattices require no cancellation of a nonzero vector. -/
theorem scalar_fibre_naturality (ω : Fibres (k := k) l R)
    (d : ScalarFibreComponents l R ω)
    (A B : Type u) [Field A] [Field B] [Algebra ℚ_[l] A] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
    (i : A →ₐ[ℚ_[l]] B) (X : FiniteTypeBase k)
    (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme)
    (F G : NormalizedFibre.Heart l A (base l X)) (f : F ⟶ G) :
    ((ω B X).point κ x).functor.map ((heartScalar l A B i X).map f) ≫
        (d.component A B i X κ x G).hom =
      (d.component A B i X κ x F).hom ≫
        (ModuleCat.extendScalars i.toRingHom).map (((ω A X).point κ x).functor.map f) := by
  sorry

end AlgebraicGeometry.Scheme.AdicFibreComparison
