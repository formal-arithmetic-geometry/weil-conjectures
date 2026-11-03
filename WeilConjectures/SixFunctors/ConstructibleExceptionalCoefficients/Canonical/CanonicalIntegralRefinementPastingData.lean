/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Canonical.CanonicalIntegralRefinement
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Canonical.CanonicalIntegralLeftRealization
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Refinement.IntegralRefinementPastingData
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Canonical.CanonicalIntegralLeftCompatibility
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Ring.RingOpenRefinement

/-! # Canonical data for integral refinement pasting -/

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

include Ω in
/-- Retain the natural integral open comparison and its canonical transpose.
Source: `exists_ring_open_refinement`.
(blueprint: lem-sf-normalized-integral-open-exists).
Proof: specialize the ring-stage existence theorem to the integral stage and
retain its natural isomorphism and normalized transpose. -/
theorem normalizedIntegralOpen_exists
    (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (E : FieldStage.{max u v} l) (c d : Compactification f) (r : c.Refinement d) :
    ∃ ε : (finiteTorConstructibleIntegral l E.carrier X).ι ⋙
        IntegralSystemRealization.ringedOpen l E.carrier d.i ≅
      (finiteTorConstructibleIntegral l E.carrier X).ι ⋙
        (IntegralSystemRealization.ringedOpen l E.carrier c.i ⋙
          IntegralSystemRealization.ringedPush l E.carrier r.hom),
      ∀ K : finiteTorConstructibleIntegralCategory l E.carrier X,
        (IntegralSystemRealization.ringedOpenAdj l E.carrier d.i).homEquiv _ _ (ε.hom.app K) ≫
            PurCompactSupport.refinementRestriction (PurCompactSupport.completed l E.carrier)
              r (PurCompactSupport.completedPull_comp l E.carrier c.i r.hom) K.obj =
          (IntegralSystemRealization.ringedOpenAdj l E.carrier c.i).unit.app K.obj := by
  obtain ⟨hi, hg, ε, hε, _⟩ := exists_ring_open_refinement.{u, v} l Ω D hl r (.integral E)
  exact ⟨ε, hε⟩

/-- The canonical functors and normalized open comparisons used by integral pasting.
Source: `exists_ring_open_refinement` and `R.integralLeft_normalized`.
(blueprint: def-sf-canonical-integral-refinement-pasting-data).
The open comparison is determined by its transpose: the refinement restriction is
invertible, so the adjunction Hom bijection determines each component uniquely.
The operation, left realization and refinement are exactly the supplied data. -/
def canonicalIntegralRefinementPastingData
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
    IntegralSystemRealization.IntegralRefinementPastingData l E.carrier D hl f := by
  classical
  let e {c d : Compactification f.left} (r : c.Refinement d) :=
    (normalizedIntegralOpen_exists.{u, v} l Ω D hl E c d r).choose
  have he (c d : Compactification f.left) (r : c.Refinement d) :=
    (normalizedIntegralOpen_exists.{u, v} l Ω D hl E c d r).choose_spec
  exact {
    F := fun c ↦ canonicalIntegralOperation l Ω D hl R E c
    r := fun c ↦ canonicalIntegralLeft l Ω D hl R E c
    ρ := fun r ↦ canonicalIntegralRefinement l Ω D hl R F M N E r
    e := fun r ↦ e r
    compatible := canonicalIntegralLeft_compatible.{u, v} l Ω D hl R E
    transpose := he }

end WeilConjectures.ConstructibleExceptionalCoefficients
