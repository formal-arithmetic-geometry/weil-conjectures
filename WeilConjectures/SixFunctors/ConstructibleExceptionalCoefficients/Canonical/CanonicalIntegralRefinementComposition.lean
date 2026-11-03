/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Canonical.CanonicalIntegralRefinement
import WeilConjectures.SixFunctors.IntegralSystemRealization.Refinement.IntegralRefinementCompositionPastingProjection
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Normalized.NormalizedIntegralRefinementBridge
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing

/-! # Composition of canonical integral refinements -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard Padic

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Composition of the supplied integral refinements in canonical category types.
Source: the composition component of normalized integral refinement pasting.
(blueprint: lem-sf-canonical-integral-refinement-composition).
Proof: choose the uniquely normalized natural open comparisons. The one-refinement
normalization bridge supplies their forward comparison equation. Compatibility is
R.integralLeft_normalized after cancelling the compact-support realization. Extract
the common Tor interval to obtain all eighteen diagram-domain witnesses. Apply the
composition projection of integral normalized refinement pasting to these premises. -/
theorem canonicalIntegralRefinementComposition
    (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Over (Spec (.of D.k))} (f : X ⟶ Y)
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [LocallyOfFiniteType (X.left ↘ Spec (.of D.k))]
    [QuasiCompact (X.left ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y.left ↘ Spec (.of D.k))]
    [QuasiCompact (Y.left ↘ Spec (.of D.k))]
    [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (R : CoefficientConstructionRing.{u, v} l Ω D hl (f := f.left))
    (F : CoefficientConstructionFields.{u, v} l Ω D hl R)
    (M : CoefficientConstructionCommon.{u, v} l Ω D hl R F)
    (N : CoefficientConstructionRefinements.{u, v} l Ω D hl R F M)
    (E : FieldStage.{max u v} l) :
    ∀ {a b c : Compactification f.left} (r : a.Refinement b) (t : b.Refinement c),
      canonicalIntegralRefinement l Ω D hl R F M N E (r.comp t) =
        canonicalIntegralRefinement l Ω D hl R F M N E r ≪≫
          canonicalIntegralRefinement l Ω D hl R F M N E t := by
  classical
  obtain ⟨o, ⟨S⟩⟩ := IntegralSystemRealization.integralCompactificationSystemRealization
    l E.carrier D hl
  have h := IntegralSystemRealization.integralRefinementCompositionPastingProjection
    l E.carrier D hl o S f
    (canonicalIntegralRefinementPastingData l Ω D hl f R F M N E)
    (normalized_integral_refinement_bridge l Ω D hl f R F M N E)
  unfold canonicalIntegralRefinementPastingData at h
  with_reducible exact h

end WeilConjectures.ConstructibleExceptionalCoefficients

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The canonical refinement maps compose under the specified derived direct-image
compositor, for every unbounded complex.
Source: latest blueprint, det-sf-comp-coherence-refinement, clause (3).
(blueprint: lem-sfb-canonical-refinement-composition).
Proof: apply the open adjunction's injective hom equivalence to both maps. Postcompose
with the two invertible restriction comparisons. Restriction-mate pasting identifies
the composite comparison, and naturality and the three unit normalization equations
identify both restrictions. This is the composition calculation already proved in
CompactificationRefinementLocalizing; no localizing membership or density is needed
for this calculation. -/
theorem canonicalIntegralRefinementComposition
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d e : Compactification.BoundaryCompactification f} (r : d ⟶ c) (s : e ⟶ d)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    localizingRefinementMap Λ (s ≫ r) K ≫
        (refinementDerivedLowerStarComp Λ s.hom.hom.hom r.hom.hom.hom).hom.app
          ((openImmersionLowerShriek Λ e.obj.obj.i).mapDerivedCategory.obj K) =
      localizingRefinementMap Λ r K ≫
        (lowerStar Λ r.hom.hom.hom).rightDerivedFunctor.map
          (localizingRefinementMap Λ s K) := by
  exact localizingRefinementMap_comp Λ r s K

end AlgebraicGeometry.ProEtale.CondensedRing
