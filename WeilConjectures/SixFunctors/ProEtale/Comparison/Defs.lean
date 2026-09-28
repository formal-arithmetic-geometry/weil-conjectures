/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous

/-!

# The comparison functors between the small étale and pro-étale sites

For a scheme `X`, the inclusion `ν = AlgebraicGeometry.Scheme.toProEt X : X.Etale ⥤ X.ProEt`
of the small étale site into the small pro-étale site is continuous, so composition with it
defines the restriction `ν_*` from pro-étale to étale sheaves. Its left adjoint `ν^*` is the
left Kan extension on presheaves followed by sheafification. Since `ν` is representably flat,
`ν^*` is exact.

This is a port, for a general Grothendieck abelian coefficient category, of the definitions
`ProEt.sheafPushforward`, `ProEt.sheafPullback` and `ProEt.sheafAdjunction` of the file
`Comparator/Definitions.lean` of the `proetale` package, which are stated there for `Ab`.

## Main definitions

- `AlgebraicGeometry.ProEtale.comparisonLowerStar`: the restriction functor
  `ν_* : Sh(X_proét, A) ⥤ Sh(X_ét, A)`, with scoped notation `ν_*(X)[A]`.
- `AlgebraicGeometry.ProEtale.comparisonUpperStar`: its left adjoint
  `ν^* : Sh(X_ét, A) ⥤ Sh(X_proét, A)`, with scoped notation `ν^*(X)[A]`.
- `AlgebraicGeometry.ProEtale.comparisonAdjunction`: the adjunction `ν^* ⊣ ν_*`.

## Main results

- `AlgebraicGeometry.ProEtale.preservesFiniteLimits_comparisonUpperStar` and
  `AlgebraicGeometry.ProEtale.preservesHomology_comparisonUpperStar`: `ν^*` is exact. Left
  exactness comes from the flatness of `ν`, through
  `CategoryTheory.preservesFiniteLimits_op_lan_of_flat`, and from the left exactness of
  sheafification.

## Implementation notes

As for `AlgebraicGeometry.ProEtale.upperStar`, the coefficient category `A` is Grothendieck
abelian with `Hom`-types in the universe `u + 1`, and sheafification on the small pro-étale
site is `CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable (X : Scheme.{u})

/-- The restriction functor `ν_* : Sh(X_proét, A) ⥤ Sh(X_ét, A)` along the inclusion
`AlgebraicGeometry.Scheme.toProEt X` of the small étale site into the small pro-étale site,
given objectwise by `(ν_* G)(U) = G(U)` for `U` étale over `X`. -/
noncomputable def comparisonLowerStar :
    Sheaf (Scheme.ProEt.topology X) A ⥤ Sheaf X.smallEtaleTopology A :=
  (Scheme.toProEt X).sheafPushforwardContinuous A X.smallEtaleTopology (Scheme.ProEt.topology X)

@[inherit_doc comparisonLowerStar]
scoped notation "ν_*(" X ")[" A "]" => comparisonLowerStar A X

/-- All pointwise left Kan extensions of `A`-valued presheaves along the opposite of the
inclusion of the small étale site into the small pro-étale site exist: the indexing comma
categories are essentially `u + 1`-small. -/
instance hasPointwiseLeftKanExtension_op_toProEt (F : X.Etaleᵒᵖ ⥤ A) :
    (Scheme.toProEt X).op.HasPointwiseLeftKanExtension F := by
  intro V
  -- the indexing comma category has objects in `Type (u + 1)` and `Hom`-types in `Type u`
  have : HasColimitsOfShape (CostructuredArrow (Scheme.toProEt X).op V) A :=
    hasColimitsOfShape_of_essentiallySmall.{u + 1} _ _
  infer_instance

/-- The left Kan extension along the opposite of the inclusion of the small étale site into
the small pro-étale site is left exact, the inclusion being representably flat. -/
instance preservesFiniteLimits_op_lan_toProEt :
    PreservesFiniteLimits ((Scheme.toProEt X).op.lan : (X.Etaleᵒᵖ ⥤ A) ⥤ X.ProEtᵒᵖ ⥤ A) :=
  inferInstance

/-- The comparison functor `ν^* : Sh(X_ét, A) ⥤ Sh(X_proét, A)`: left Kan extension of
presheaves along the inclusion `AlgebraicGeometry.Scheme.toProEt X` of the small étale site
into the small pro-étale site, followed by sheafification. It is left adjoint to
`ProEtale.comparisonLowerStar`. -/
noncomputable def comparisonUpperStar :
    Sheaf X.smallEtaleTopology A ⥤ Sheaf (Scheme.ProEt.topology X) A :=
  Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt X) A X.smallEtaleTopology
    (Scheme.ProEt.topology X)

@[inherit_doc comparisonUpperStar]
scoped notation "ν^*(" X ")[" A "]" => comparisonUpperStar A X

/-- The adjunction `ν^* ⊣ ν_*` between étale and pro-étale sheaves. -/
noncomputable def comparisonAdjunction : ν^*(X)[A] ⊣ ν_*(X)[A] :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Scheme.toProEt X) A
    X.smallEtaleTopology (Scheme.ProEt.topology X)

/-- `ν_*` is a right adjoint. -/
instance : ν_*(X)[A].IsRightAdjoint :=
  (comparisonAdjunction A X).isRightAdjoint

/-- `ν^*` is a left adjoint. -/
instance : ν^*(X)[A].IsLeftAdjoint :=
  (comparisonAdjunction A X).isLeftAdjoint

/-- The restriction `ν_*` is left exact: finite limits of sheaves are computed on the
underlying presheaves. -/
instance preservesFiniteLimits_comparisonLowerStar : PreservesFiniteLimits ν_*(X)[A] :=
  inferInstanceAs (PreservesFiniteLimits ((Scheme.toProEt X).sheafPushforwardContinuous A
    X.smallEtaleTopology (Scheme.ProEt.topology X)))

/-- The comparison functor `ν^*` is left exact: it is the composite of the inclusion of
sheaves into presheaves, the left Kan extension along the opposite of the representably flat
functor `AlgebraicGeometry.Scheme.toProEt X`, and sheafification, all of which are left
exact. -/
instance preservesFiniteLimits_comparisonUpperStar : PreservesFiniteLimits ν^*(X)[A] := by
  unfold comparisonUpperStar Functor.sheafPullbackConstruction.sheafPullback
  infer_instance

/-- The comparison functor `ν^*` is right exact, being a left adjoint. -/
instance preservesFiniteColimits_comparisonUpperStar : PreservesFiniteColimits ν^*(X)[A] :=
  inferInstance

/-- The restriction `ν_*` is additive: it acts on morphisms by whiskering, which is
compatible with the objectwise addition. -/
instance additive_comparisonLowerStar : ν_*(X)[A].Additive where

/-- The comparison functor `ν^*` is additive, being a left adjoint. -/
instance additive_comparisonUpperStar : ν^*(X)[A].Additive :=
  (comparisonAdjunction A X).left_adjoint_additive

/-- The comparison functor `ν^*` preserves homology, being exact. -/
instance preservesHomology_comparisonUpperStar : ν^*(X)[A].PreservesHomology := by
  have : PreservesColimitsOfSize.{0, 0} ν^*(X)[A] :=
    (comparisonAdjunction A X).leftAdjoint_preservesColimits
  -- the two fields of `PreservesHomology` are `autoParam`s, found by instance synthesis
  exact {}

end AlgebraicGeometry.ProEtale
