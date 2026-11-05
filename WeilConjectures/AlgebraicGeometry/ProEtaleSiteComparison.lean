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

Source: Stacks Project, Tag 099R, opening paragraph; Sites, Tags 00WX, 00X6 and 00YV.

The inclusion is the existing `Scheme.toProEt`, identity on schemes and arrows.
Its continuity and finite-limit preservation are the existing instances
`Scheme.isContinuous_toProEt` and `Scheme.preservesFiniteLimits_toProEt`.
The comparison adjunction below uses restriction and the left Kan extension followed by
sheafification, rather than a chosen abstract left adjoint, for any coefficient category
with the needed colimits and sheafification. For abelian coefficients its inverse image is
definitionally `ProEtale.comparisonUpperStar`; for sets it is the geometric morphism from
the pro-etale to the etale topos.
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
followed by sheafification. The Kan extension at `W` is the colimit over
`CostructuredArrow (toProEt X).op (op W)`, which is the opposite of the category of pairs
`(U, W ⟶ u(U))` of Tag 00WX. It is definitionally `comparisonUpperStar` for abelian
coefficients.
Source: blueprint, lem-weil-pbc-comparison-pullback, proof steps 1--4;
Stacks, Tags 099R, 00WX and 0B65. -/
noncomputable abbrev comparisonCoefficientPullback (X : Scheme.{u}) :=
  Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt X) D
    X.smallEtaleTopology (Scheme.ProEt.topology X)

/-- The canonical comparison adjunction for the common coefficient category: the inverse
image `comparisonCoefficientPullback` is left adjoint to restriction along `toProEt X`.
Source: blueprint, lem-weil-pbc-comparison-pullback, proof steps 1--4;
Stacks, Tags 099R, 00WX and 0B65. -/
noncomputable abbrev comparisonCoefficientAdjunction (X : Scheme.{u}) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Scheme.toProEt X) D
    X.smallEtaleTopology (Scheme.ProEt.topology X)

end

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Scheme

section

open CategoryTheory CategoryTheory.Limits

/-- The set-valued comparison adjunction, with inverse image given by left Kan extension
followed by sheafification and direct image by restriction along `toProEt T`.
The Kan extension at `W` is the colimit over `CostructuredArrow (toProEt T).op (op W)`,
which is the opposite of the category of pairs `(U, W ⟶ u(U))` of Tag 00WX.
Source: Stacks Project, Tags 099R and 00WX
(blueprint: def-weil-pbc-site-comparison-morphism). -/
noncomputable def proEtaleSiteComparison (T : Scheme.{u}) :
    Functor.sheafPullbackConstruction.sheafPullback (toProEt T)
      (Type (u + 1)) T.smallEtaleTopology (ProEt.topology T) ⊣
    (toProEt T).sheafPushforwardContinuous
      (Type (u + 1)) T.smallEtaleTopology (ProEt.topology T) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (toProEt T)
    (Type (u + 1)) T.smallEtaleTopology (ProEt.topology T)

end

end AlgebraicGeometry.Scheme
