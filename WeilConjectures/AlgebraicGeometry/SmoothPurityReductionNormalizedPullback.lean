/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionMonoidalData
import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionPullbackOrdinaryNormalization
import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionPullbackDerivedNormalization

/-! # Normalized geometric inverse image for integral reduction

Source: Stacks 03EL, 0G7E, 0D6D; blueprint integral direct-image proof (3).
(blueprint: lem-sp-reduction-normalized-pullback-tower).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- The integral and sequence inverse images, together with their normalized reduction
comparison, can be constructed without choosing monoidal tensor data at either endpoint.
Source: Stacks 03EL, 0G7E, 0D6D; geometric-tensor-square proof steps 1 and 2.
(blueprint: lem-sp-reduction-normalized-pullback-tower).

Proof: pull the condensed integral coefficient ring from the point through the geometric
inverse image of the pro-etale base-change functor. Pull each constant quotient ring in
exactly the same way. The resulting ring identifications fix constants and commute with
the actual completion projections, by functoriality of inverse image on those projections.
On the product sequence site use the sheafified left Kan extension of the product of the
identity on the index and scheme base change. Lift it to modules using these coefficient
identifications. Its additivity and exactness follow from exactness of geometric inverse
image, since the coefficient identifications are isomorphisms. Restriction to a sequence
level gives the level inverse image: the Kan-unit section generator is carried to itself.
The two composite module pullbacks from integral modules to target sequence modules have
the same scalar maps. Ringed inverse-image composition gives their ordinary isomorphism;
its formula takes a pulled-back generator to the tensor with the same pulled-back quotient
coefficient. This verifies the ordinary-section equation before localization. Apply the
normalized derived composition and geometric two-isomorphism comparisons to this square.
Compute them on flat-term K-flat representatives, whose pullbacks remain flat-term K-flat.
Their representative comparison is the localization of the preceding ordinary map, so it
satisfies exactly the displayed counit equation in `SpPullbackDerived`. These constructions
supply all six normalization fields of `SpReductionPullbackTower`. They are valid for the
empty scheme and for identity maps, and do not require flat quotient ring maps. -/
theorem sp_reduction_normalized_pullback_tower
    (hl : ∀ x : T, IsUnit (l : T.residueField x))
    (D : SpCoefficientTowersAbelian l E T) (r : SpReductionTower l E T D)
    {T' : Scheme.{u}} (hl' : ∀ x : T', IsUnit (l : T'.residueField x)) (g : T' ⟶ T)
    (D' : SpCoefficientTowersAbelian l E T') (r' : SpReductionTower l E T' D') :
    Nonempty (SpReductionPullbackTower l E T D r g D' r') := by
  classical
  obtain ⟨p⟩ := sp_reduction_pullback_ordinary_normalization l E T hl D r hl' g D' r'
  obtain ⟨ν, hν⟩ :=
    sp_reduction_pullback_derived_normalization l E T hl D r hl' g D' r' p
  let q := SpReductionPullbackCore.toData l E T D r g D' r' p.core ν
  exact ⟨{
    toSpReductionPullbackData := q
    constant := p.constant ν
    projection := p.projection ν
    system_ring := p.system_ring ν
    evaluation_section := p.evaluation_section ν
    ordinary_section := p.ordinary_section ν
    derived := hν }⟩

end AlgebraicGeometry.ProEtale
