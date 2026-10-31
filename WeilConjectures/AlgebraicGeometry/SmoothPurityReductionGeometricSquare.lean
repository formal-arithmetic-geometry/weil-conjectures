/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionMonoidalData
import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionNormalizedPullback
import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionPullbackCoherence

/-! # The geometric square for normalized reduction comparisons

Source: Stacks 03EL, 0G7E, 0D6D; blueprint integral direct-image proof (3)
(blueprint: lem-sp-reduction-geometric-tensor-square).
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

/-- The geometric reduction square is compatible with any specified normalized
monoidal reduction comparisons at its two ends.
Source: Stacks 0D6D, 07A4, 0G7E; original node steps 6--8
(blueprint: lem-sp-reduction-geometric-tensor-square).

Proof: pull back the condensed integral ring from the point and each constant
quotient ring. Functoriality gives the integral coefficient identification and
the quotient identifications, fixing constant sections and commuting with the
actual completion projections. Apply geometric inverse image on the sequence
site; its underlying functor is the sheafified Kan extension of the product
base-change functor. Its module lift is additive and exact because the coefficient
identification is an isomorphism. Vertical evaluation of this lift is the level
inverse image: its map on Kan-extension generators is the identity section map.
Both paths from the integral site to the target sequence site send a module
generator to the same pulled-back tensor with the same coefficient. The ring maps
agree by the completion-projection equation. Ordinary ringed pullback composition
therefore supplies the comparison normalized by `ordinary_section`.
Apply the normalized derived composition and geometric 2-isomorphism comparisons
to this commuting square. On flat-term K-flat representatives, pullback preserves
the representative class and the comparison is the localization of that ordinary
section formula. This proves `SpPullbackDerived` with the prescribed counits.
Use the canonical normalized tensor pullback models for the integral and sequence
inverse images. The tensor and unit diagrams for the composition comparison give
the two coherence equations. They agree with the already specified monoidal
reduction data because its derived square and chain summands fix the same balancing
map on every K-flat pair. Two-variable localization uniqueness identifies those
comparisons on whole derived systems; it does not use faithfulness of evaluation.
All these constructions respect quotient transitions before localization. The
identity scheme map, empty schemes and nonflat quotient maps obey the same formulas. -/
theorem sp_reduction_geometric_tensor_square
    (hl : ∀ x : T, IsUnit (l : T.residueField x))
    (D : SpCoefficientTowersAbelian l E T) (r : SpReductionTower l E T D)
    (M : SpReductionMonoidalTower l E T D r)
    {T' : Scheme.{u}} (hl' : ∀ x : T', IsUnit (l : T'.residueField x)) (g : T' ⟶ T)
    (D' : SpCoefficientTowersAbelian l E T') (r' : SpReductionTower l E T' D')
    (M' : SpReductionMonoidalTower l E T' D' r') :
    ∃ p : SpReductionPullbackTower l E T D r g D' r',
      Nonempty (SpReductionPullbackCoherence l E T D r M g D' r' M' p) := by
  obtain ⟨p⟩ := sp_reduction_normalized_pullback_tower l E T hl D r hl' g D' r'
  exact ⟨p, sp_reduction_pullback_model_coherence l E T D r M g D' r' M' p⟩

end AlgebraicGeometry.ProEtale
