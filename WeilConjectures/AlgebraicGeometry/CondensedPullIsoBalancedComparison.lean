/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Monoidal.Mon
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
public import WeilConjectures.Algebra.Homology.ScalarPullback.KFlatScalarComparisonNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import all WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarRestrictionMateNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate

/-! # The derived (Pull) comparison and balanced scalar pullback

Source: current blueprint, sec-six-functors-basics/sk-thm-sfb-proper-base-change/
det-def-sfb-coefficient-comparisons.proof.md, paragraphs "Pushforward and pullback"
and "Derived (Pull) and (Push)"
(blueprint: lem-weil-condensed-pull-iso-balanced-comparison).

The existing `PullNormalized` predicate specifies the balanced comparison through
its universal computation counits on the ordinary unbounded derived categories.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.QuotientChange

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']

/-- The inverse of the specified derived (Pull), with the existing named scalar and
geometric functors exposed as its endpoints. The body only unfolds these wrappers;
it is exactly `(CondensedRing.derivedPullIso a f).symm`, including its adjunction data.
Source: current blueprint, det-def-sfb-coefficient-comparisons.proof.md,
"Derived (Pull) and (Push)"
(blueprint: lem-weil-condensed-pull-iso-balanced-comparison). -/
@[irreducible] def inverseConjugatePullComparison (a : Λ ⟶ Λ') [IsMonHom a]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X := by
  unfold D L CondensedRing.moduleObjectDerivedPullback
  exact (CondensedRing.derivedPullIso a f).symm

set_option allowUnsafeReducibility true in
attribute [local reducible] D L

/-- The balanced K-flat scalar/pullback comparison is the inverse of derived (Pull),
as an equality of natural isomorphisms on the entire ordinary unbounded category.
Here `normalized` specifies the balanced map of the node: its universal computation
counit equation is the termwise pure-tensor map on flat-term K-flat representatives.

Source: current blueprint, det-def-sfb-coefficient-comparisons.proof.md,
"Pushforward and pullback" and "Derived (Pull) and (Push)"
(blueprint: lem-weil-condensed-pull-iso-balanced-comparison).

Proof:
1. By lem-sfb-internal-scalar-restriction-mate-normalization (the proved normalization
step `normalized_inverse`), `PullNormalized` forces `b⁻¹` to be the inverse scalar-adjunction
mate of the inverse exact restriction/pullback comparison, for the specified derived
scalar adjunctions; this holds on every unbounded object by left-derived extensionality
from the universal computation counits.
2. By `CondensedRing.mateEquiv_derivedPullIso_hom` (def-sfb-derived-pull-iso, proved by
iterated conjugation from def-sfb-derived-comap-lower-star-iso), the scalar mate of
`derivedPullIso.hom` is `derivedComapLeftDerivedUpperStarIso.hom`. Unfolding the two
restriction/pullback constructions (def-sfb-derived-comap-upper-star-iso), this is the
same exact-localization comparison as the one of step 1.
3. Applying the inverse mate equivalence (def-weil-pbc-adjunction-mate) to step 2 gives
`b⁻¹ = derivedPullIso.hom`, which is the inverse arrow of `inverseConjugatePullComparison`;
extensionality of isomorphisms on inverse arrows concludes. -/
theorem condensed_pull_iso_balanced_comparison (a : Λ ⟶ Λ') [IsMonHom a]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (b : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X) (normalized : PullNormalized a f b) :
    b = inverseConjugatePullComparison a f := by
  have hn := normalized_inverse a f b normalized
  have h := CondensedRing.mateEquiv_derivedPullIso_hom a f
  have he : (CondensedRing.derivedComapLeftDerivedUpperStarIso a f).hom =
      (normalizationRestrictionPull a f).inv := by
    simp only [CondensedRing.derivedComapLeftDerivedUpperStarIso,
      normalizationRestrictionPull, id_eq,
      CondensedRing.derivedComapUpperStarIso,
      CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory,
      Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_hom, Functor.mapDerivedCategoryNatIso_symm,
      Category.assoc]
  rw [he] at h
  have hi : b.inv = (CondensedRing.derivedPullIso a f).hom := by
    rw [hn]
    let e := mateEquiv (G := L Λ f) (H := L Λ' f)
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y))
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
    exact congrArg TwoSquare.natTrans ((e.symm_apply_eq).mpr h.symm)
  apply Iso.ext_inv
  unfold inverseConjugatePullComparison
  exact hi

end AlgebraicGeometry.ProEtale.QuotientChange
