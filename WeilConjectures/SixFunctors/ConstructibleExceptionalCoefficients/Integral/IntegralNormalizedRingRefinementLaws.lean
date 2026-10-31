/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientConstructionData
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Integral.IntegralNormalizedRingRefinementIdentity
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Integral.IntegralNormalizedRingRefinementComposition

/-! # Integral normalized refinement laws

Source: integral normalized refinement pasting and its relative compactification
system argument (blueprint: lem-sf-integral-normalized-refinement-laws).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] HasDerivedCategory.standard

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The identity and composition laws for one completed integral coefficient stage.
Source: integral normalized refinement pasting, relative compactification system
realization and refinement-diagram admissibility
(blueprint: lem-sf-integral-normalized-refinement-laws).

Proof: choose the normalized open comparisons supplied by the integral coefficient
construction. Their open-adjunction transpose uniquely identifies the comparisons
used by the normalized input. The supplied integral-left realization gives the
compatible compact-support realization. Uniform finite-Tor intervals provide every
word in the identity and binary-refinement diagrams. Applying integral normalized
refinement pasting and taking its identity and composition clauses proves these two
laws for the actual left refinement isomorphisms. This theorem fixes the integral
stage, so it is strictly one case of the RingStage statement. Relative separatedness
of f is the only separatedness used; zero objects and empty opens are included.
(blueprint: lem-sf-integral-normalized-refinement-laws). -/
theorem integral_normalized_ring_refinement_laws
    (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : CoefficientConstructionRing.{u, v} l Ω D hl (f := f))
    (F : CoefficientConstructionFields.{u, v} l Ω D hl R)
    (M : CoefficientConstructionCommon.{u, v} l Ω D hl R F)
    (N : CoefficientConstructionRefinements.{u, v} l Ω D hl R F M)
    (E : FieldStage.{max u v} l) :
    (∀ c : Compactification f, (N.refinement (.id c) (.integral E)).left = Iso.refl _) ∧
    (∀ {a b c : Compactification f} (r : a.Refinement b) (t : b.Refinement c),
      (N.refinement (r.comp t) (.integral E)).left =
        (N.refinement r (.integral E)).left ≪≫
          (N.refinement t (.integral E)).left) := by
  constructor
  · exact integral_normalized_ring_refinement_identity l Ω D hl R F M N E
  · exact integral_normalized_ring_refinement_composition l Ω D hl R F M N E

end WeilConjectures.ConstructibleExceptionalCoefficients
