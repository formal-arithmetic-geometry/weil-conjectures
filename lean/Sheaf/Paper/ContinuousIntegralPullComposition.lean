/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.Paper.ContinuousIntegralComparisons
import Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse
import Sheaf.Paper.ContinuousIntegralScalarExact

/-! # Composition coherence of the specified integral pull comparisons -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
  [NormedAlgebra ℚ_[ℓ] E] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-- The specified scalar-extension/pullback comparison respects composition.
Source: Bhatt--Scholze, Remark 6.8.15, and the canonical constructions
`comapLowerStarIso`, `derivedComapLowerStarIso`, `derivedPullIso`, and
`leftDerivedUpperStarComp` in ChangeOfCoefficients.lean and Derived/UpperLowerStar.lean.
(blueprint: lem-weil-pbc-continuous-integral-pull-composition).

Proof. Write T for integral scalar extension and α for its pull comparison. Before deriving,
the restriction-of-scalars/pushforward comparison has identity underlying sheaf components.
For h followed by j its composition square commutes, since the underlying components of
both coefficient pushforward composition isomorphisms are the same sheaf pushforward
composition isomorphism. All three pushforwards and scalar restrictions preserve K-injective
complexes: their left adjoints are exact. Derive the composition square using the canonical
composition units. On K-injective complexes those units are isomorphisms; cancel them and
use the underived square. Every derived object has a K-injective representative, so the
derived square commutes on all objects. The exact-restriction identification R(Res) ≅ D(Res)
is the unique comparison with its specified unit, and hence preserves that square.
Conjugate the derived square through the scalar and pullback adjunctions. Conjugation
reverses vertical composition, interchanges left and right whiskering, and sends the
associator to the reversed associator. Thus its two paths give the α_h, α_j composite and
α_(h≫j). The pullback composition comparison used here is the specified one: the underived
comparison is conjugate to pushforward composition, and the right-derived composition
conjugation theorem identifies its conjugate with the left-derived comparison obtained
from the exact levelwise functors. Finally restrict along the fully faithful bounded
constructible inclusions. Their composition comparison is the lift of that same derived
comparison, so equality of the ambient isomorphisms gives the displayed equality. -/
theorem integralConstructiblePullIso_comp
    {T U : Scheme.{u}} [T.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] (h : T ⟶ U) [h.IsOver (Spec (.of k))]
    {V : Scheme.{u}} [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))] (j : U ⟶ V) [j.IsOver (Spec (.of k))]
    (K : integralConstructible ℓ E V) :
    (integralScalarConstructible ℓ E T).mapIso
        ((boundedConstructibleUpperStarComp (integralCoeff ℓ E) ℓ k h j).app K) ≪≫
      integralConstructiblePullIso ℓ E k h
        ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ k j).obj K) ≪≫
      (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k h).mapIso
        (integralConstructiblePullIso ℓ E k j K) =
    integralConstructiblePullIso ℓ E k (h ≫ j) K ≪≫
      (boundedConstructibleUpperStarComp (Profinite.continuousMapRingObj E) ℓ k h j).app
        ((integralScalarConstructible ℓ E V).obj K) := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
