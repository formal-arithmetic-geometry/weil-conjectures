/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import Mathlib.Algebra.Category.ModuleCat.AB

/-!
# The geometric comparison from the pro-etale to the etale site

The inclusion is the existing `Scheme.toProEt`, identity on schemes and arrows.
Its continuity and finite-limit preservation are the existing instances
`Scheme.isContinuous_toProEt` and `Scheme.preservesFiniteLimits_toProEt`.
The comparison adjunction below uses restriction and the left Kan extension followed by
sheafification, rather than a chosen abstract left adjoint, for any coefficient category
with the needed colimits and sheafification. For abelian coefficients its inverse image is
definitionally `ProEtale.comparisonUpperStar`; for sets it is the geometric morphism from
the pro-etale to the etale topos.

## References

* Stacks Project, Tag 099R; Sites, Tags 00WX, 00X6 and 00YV.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

section

variable (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
variable [∀ X : Scheme.{u}, HasWeakSheafify X.smallEtaleTopology D]
variable [∀ X : Scheme.{u}, HasWeakSheafify (Scheme.ProEt.topology X) D]

/-- The comparison inverse image, constructed by left Kan extension along `toProEt X`
followed by sheafification. It is definitionally `comparisonUpperStar` for abelian
coefficients (Stacks, Tags 099R, 00WX and 0B65). -/
noncomputable abbrev comparisonCoefficientPullback (X : Scheme.{u}) :=
  Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt X) D
    X.smallEtaleTopology (Scheme.ProEt.topology X)

/-- The canonical comparison adjunction for the common coefficient category: the inverse
image `comparisonCoefficientPullback` is left adjoint to restriction along `toProEt X`
(Stacks, Tags 099R, 00WX and 0B65). -/
noncomputable abbrev comparisonCoefficientAdjunction (X : Scheme.{u}) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Scheme.toProEt X) D
    X.smallEtaleTopology (Scheme.ProEt.topology X)

end

/-- For sets, the inverse image `comparisonCoefficientPullback` preserves finite limits, so
the comparison adjunction is the geometric morphism from the pro-etale to the etale topos
(Stacks, Tags 099R, 00X6 and 00WJ). -/
theorem preservesFiniteLimits_comparisonCoefficientPullback_type (T : Scheme.{u}) :
    PreservesFiniteLimits (comparisonCoefficientPullback (Type (u + 1)) T) := by
  have hlan : PreservesFiniteLimits
      ((Scheme.toProEt T).op.lan : (T.Etaleᵒᵖ ⥤ Type (u + 1)) ⥤
        (T.ProEtᵒᵖ ⥤ Type (u + 1))) := by
    apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u + 1}
    intro J _ _
    apply preservesLimitsOfShape_of_evaluation
      ((Scheme.toProEt T).op.lan : (T.Etaleᵒᵖ ⥤ Type (u + 1)) ⥤
        (T.ProEtᵒᵖ ⥤ Type (u + 1))) J
    intro K
    have : IsFiltered (CostructuredArrow (Scheme.toProEt T).op K) :=
      IsFiltered.of_equivalence
        (structuredArrowOpEquivalence (Scheme.toProEt T) (Opposite.unop K))
    exact preservesLimitsOfShape_of_natIso
      (Functor.lanEvaluationIsoColim' (Scheme.toProEt T).op K).symm
  let _ := hlan
  apply Functor.sheafPullbackConstruction.instPreservesFiniteLimitsSheafSheafPullback
    (Scheme.toProEt T) (Type (u + 1)) T.smallEtaleTopology (Scheme.ProEt.topology T)


end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Scheme

section

open CategoryTheory CategoryTheory.Limits

/-- The set-valued comparison adjunction, with inverse image given by left Kan extension
followed by sheafification and direct image by restriction along `toProEt T`
(Stacks, Tags 099R and 00WX). -/
noncomputable def proEtaleSiteComparison (T : Scheme.{u}) :
    Functor.sheafPullbackConstruction.sheafPullback (toProEt T)
      (Type (u + 1)) T.smallEtaleTopology (ProEt.topology T) ⊣
    (toProEt T).sheafPushforwardContinuous
      (Type (u + 1)) T.smallEtaleTopology (ProEt.topology T) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (toProEt T)
    (Type (u + 1)) T.smallEtaleTopology (ProEt.topology T)

end

end AlgebraicGeometry.Scheme
