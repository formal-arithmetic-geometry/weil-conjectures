/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.BaseChangeMapAbelianAndSets

import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra
import WeilConjectures.AlgebraicGeometry.EtaleUnboundedRestrictionComparison
import WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsExchange
import WeilConjectures.SixFunctors.BaseChange.EtaleDerived
import WeilConjectures.AlgebraicGeometry.LimitFibreProducts
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.FieldTheory.PurelyInseparable.Basic
import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Identity
import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Horizontal
import WeilConjectures.AlgebraicGeometry.UniversalHomeomorphismInvariance

/-!
# Direct image and geometric generic restriction

Source: literature/blueprint/latest/blueprint/sec-six-functors/
sk-lem-pd-generic-restriction/det-pd-generic-direct-image.md
(blueprint: det-pd-generic-direct-image).

The geometric generic point is the spectrum of a chosen algebraic closure of the
function field, followed by the canonical generic-stalk morphism. Cartesian-square
binders allow any representatives of the geometric fibres and their induced morphism.
The conclusion concerns the canonical module-coefficient exchange on the unbounded
derived category, with the recorded bounded-constructible predicate on its input.
-/

set_option autoImplicit false

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- Geometric generic restriction commutes with direct image for a separated finite-type
morphism of finite-type schemes over a smooth integral curve, with finite coefficients
and bounded constructible input.

Source: blueprint, sec-six-functors/sk-lem-pd-generic-restriction,
det-pd-generic-direct-image (blueprint: det-pd-generic-direct-image).

Proof in words:
1. Forget the coefficient action. The canonical restriction-of-scalars comparisons
   (lem-sbc-canonical-restrict-scalars-functor-comparisons and
   lem-sbc-restrict-scalars-derived-exchange) identify the exchange with the abelian
   exchange. Forgetting reflects acyclic cones and thus isomorphisms. Bounded
   constructibility gives bounded-below input; finite type and separatedness give qcqs.
2. Present the spectrum of the relative separable closure of the function field as
   a directed affine-transition limit of affine etale curve schemes, using
   lem-sf-separable-generic-etale-presentation. The fibre-product limit comparison
   lem-weil-pbc-limit-fibre-products gives the corresponding limits over T and X.
3. At every stage, etale localization commutes with derived direct image by
   lem-weil-pbc-etale-localization-exchange. This uses no invertibility condition on A.
4. Apply lem-sf-bounded-below-limit-exchange (Stacks 0GJL) with constant right column h.
   Its qcqs, affine-transition, and bounded-below assumptions were checked above.
   The canonical exchange is therefore invertible over the separable closure.
5. The algebraic closure over the separable closure is purely inseparable by
   lem-weil-pbc-separable-first-purely-inseparable. Its spectrum map, and its base
   changes, are universal homeomorphisms by
   lem-pc-spec-pure-insep-integral-radicial-surjective and
   lem-pc-integral-radicial-surjective-universal-homeomorphism. By
   thm-weil-pbc-universal-homeomorphism-invariance their exact etale equivalences
   identify direct images; taking adjoint mates gives the canonical exchange.
6. Paste the two squares using sbc-lem-identity-and-base-change-composition.
   The resulting exchange is invertible. The comparisons in step 1 identify it with
   the underlying arrow of the displayed module exchange and reflect invertibility.
-/
theorem isIso_derivedBaseChangeMap_app_geometricGeneric
    {k : Type u} [Field k] {B : Scheme.{u}} [IsIntegral B]
    (aB : B ⟶ Spec (CommRingCat.of k)) [IsCurve aB] [Smooth aB]
    (Ω : Type u) [Field Ω] [Algebra B.functionField Ω] [IsAlgClosure B.functionField Ω]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {T X : Scheme.{u}} (t : T ⟶ B) (x : X ⟶ B)
    [LocallyOfFiniteType t] [QuasiCompact t] [LocallyOfFiniteType x] [QuasiCompact x]
    (h : T ⟶ X) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (_hB : h ≫ x = t) {Tη Xη : Scheme.{u}} (gX : Xη ⟶ X)
    (pX : Xη ⟶ Spec (CommRingCat.of Ω))
    (_sqX : IsPullback gX pX x
      (Spec.map (CommRingCat.ofHom (algebraMap B.functionField Ω)) ≫
        B.fromSpecStalk (genericPoint B)))
    (gT : Tη ⟶ T) (hη : Tη ⟶ Xη) (sq : IsPullback gT hη h gX)
    (L : DerivedCategoryModule A T) (_hL : DerivedCategory.isBoundedConstructible A T L) :
    IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app L) := by
  sorry

end AlgebraicGeometry.Etale
