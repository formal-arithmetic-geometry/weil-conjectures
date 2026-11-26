/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralReconstruction.ExceptionalIntegralReconstructionInterfaces
import WeilConjectures.SixFunctors.ExceptionalIntegralReconstruction.ExceptionalIntegralNormalizationPreservation
import WeilConjectures.SixFunctors.ExceptionalIntegralReconstruction.ExceptionalIntegralUniformBounds
import WeilConjectures.SixFunctors.ExceptionalIntegralReconstruction.ExceptionalIntegralCoordinateOrigin
import WeilConjectures.SixFunctors.ExceptionalIntegralReconstruction.ExceptionalIntegralOriginAdjunctionRestriction

/-!
# Normalized exceptional system adjunction

The specified exceptional system adjunction restricts to normalized finite-Tor systems.

## Implementation details

Both outputs satisfy `LevelBounds` because the finite exceptional operations give common
cohomological and Tor interval enlargements, identified with the evaluated system functors by the
site evaluation comparisons. Normalization is preserved by
`exceptionalIntegralNormalizationPreservation`. The origin adjunction of `s.transport` is then
restricted along the full normalized subcategories, after conjugating by the two coordinate
equivalences.

## References

* [Zheng, Section 5, Lemma 5.22 and Proposition 5.24]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

attribute [local semireducible] AlgebraicGeometry.exceptionalProSystemDerived
  AlgebraicGeometry.exceptionalProLevelDerived AlgebraicGeometry.strictEtaleLevelDerived

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralReconstruction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The specified system adjunction restricts to an adjunction between the normalized
finite-Tor systems on `X` and `Y`. -/
theorem exceptionalIntegralNormalizedAdjunction
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (rX : Reconstruction l E X) (s : Systems l E c) :
    Nonempty (SystemAdjunction l E c s) := by
  obtain ⟨hnL, hnR⟩ := exceptionalIntegralNormalizationPreservation l E D hl c s rX
  obtain ⟨hbL, hbR⟩ := exceptionalIntegralUniformBounds l E D hl c s
  exact exceptionalIntegralOriginAdjunctionRestriction l E c s
    (fun N hN ↦ ⟨hnL N hN, hbL N hN⟩)
    (fun N hN ↦ ⟨hnR N hN, hbR N hN⟩)
    (fun N hN ↦ exceptionalIntegralCoordinateOrigin l E X s.ordinary.PX s.siteX N hN.2)
    (fun N hN ↦ exceptionalIntegralCoordinateOrigin l E Y s.ordinary.PY s.siteY N hN.2)

end WeilConjectures.ExceptionalIntegralReconstruction
