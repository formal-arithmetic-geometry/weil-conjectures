/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ConstructibleExceptionalCoefficientConstructionData

/-! # Integral refinement composition after coefficient inclusion

This is the objectwise comparison produced by the normalized integral pasting
argument.  The main composition statement obtains it by faithfulness of the
integral coefficient inclusion.
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

/--
Source: the binary refinement diagram in integral normalized refinement pasting
(blueprint: lem-sf-integral-normalized-ring-refinement-composition-after-inclusion).

The normalized pasting and realization argument proves this equality after the
fully faithful integral coefficient inclusion.  It is strictly objectwise and
therefore is the lower-level statement used to recover equality of the original
refinement isomorphisms.
-/
theorem integral_normalized_ring_refinement_composition_after_inclusion
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
    ∀ {a b c : Compactification f} (r : a.Refinement b) (t : b.Refinement c)
      (K : C.{u, v} l Ω X (.integral E)),
      (RingStage.inclusion.{u, v} l Ω Y (.integral E)).map
          ((N.refinement (r.comp t) (.integral E)).left.hom.app K) =
        (RingStage.inclusion.{u, v} l Ω Y (.integral E)).map
          (((N.refinement r (.integral E)).left ≪≫
            (N.refinement t (.integral E)).left).hom.app K) := by
  sorry

end WeilConjectures.ConstructibleExceptionalCoefficients
