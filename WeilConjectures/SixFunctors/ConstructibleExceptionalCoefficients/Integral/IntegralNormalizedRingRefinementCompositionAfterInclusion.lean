/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientConstructionData
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Canonical.CanonicalIntegralRefinementComposition

/-! # Integral refinement composition after coefficient inclusion

This is the objectwise comparison produced by the normalized integral pasting
argument.  The main composition statement obtains it by faithfulness of the
integral coefficient inclusion.
-/

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
  intro a b c r t K
  let XB := X.asOver (Spec (.of D.k))
  let YB := Y.asOver (Spec (.of D.k))
  let fB : XB ⟶ YB := f.asOver (Spec (.of D.k))
  let : LocallyOfFiniteType XB.hom :=
    inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (.of D.k)))
  let : QuasiCompact XB.hom := inferInstanceAs (QuasiCompact (X ↘ Spec (.of D.k)))
  let : LocallyOfFiniteType YB.hom :=
    inferInstanceAs (LocallyOfFiniteType (Y ↘ Spec (.of D.k)))
  let : QuasiCompact YB.hom := inferInstanceAs (QuasiCompact (Y ↘ Spec (.of D.k)))
  let : IsSeparated fB.left := inferInstanceAs (IsSeparated f)
  let : LocallyOfFiniteType fB.left := inferInstanceAs (LocallyOfFiniteType f)
  let : QuasiCompact fB.left := inferInstanceAs (QuasiCompact f)
  let : LocallyOfFiniteType (XB.left ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (.of D.k)))
  let : QuasiCompact (XB.left ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact (X ↘ Spec (.of D.k)))
  let : LocallyOfFiniteType (YB.left ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType (Y ↘ Spec (.of D.k)))
  let : QuasiCompact (YB.left ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact (Y ↘ Spec (.of D.k)))
  have hc := canonicalIntegralRefinementComposition l Ω D hl fB R F M N E r t
  unfold canonicalIntegralRefinement canonicalIntegralOperation at hc
  exact congrArg (RingStage.inclusion.{u, v} l Ω Y (.integral E)).map
    (congr_app (congrArg Iso.hom hc) K)

end WeilConjectures.ConstructibleExceptionalCoefficients
