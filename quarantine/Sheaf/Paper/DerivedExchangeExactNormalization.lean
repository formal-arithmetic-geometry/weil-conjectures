/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q40
-/
module

public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.BoundedConstructibleBaseChange
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Restrict
import Sheaf.AlgebraicGeometry.CondensedModulePullbackExact
import Sheaf.CategoryTheory.DerivedCategory.LeftDerivedTotalTensorExact
import Sheaf.CategoryTheory.CanonicalRightDerivedAdjunctionShift
import Sheaf.CategoryTheory.ExactDerivedComposition
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-!
# Canonical ambient exchange and its restriction

Source: blueprint main-20261015, proper-base-change rational proof, paragraph (3)
(blueprint: lem-sfb-derived-exchange-exact-normalization).

The pullback comparison uses the published derived compositors. The exchange is their
mate under the published derived adjunctions, with no cartesianness requirement. Pullback
shifts are transported from the exact termwise functor along its canonical comparison;
pushforward shifts are the canonical K-injective shifts.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The canonical integer shifts on the actual K-flat pullback, transported along its
canonical comparison with the exact termwise pullback. This fixes the shift structure,
rather than selecting an unspecified one.
Source: blueprint rational proof (3), exact derived factorization
(blueprint: lem-sfb-derived-exchange-exact-normalization). -/
instance moduleObjectDerivedPullbackCommShift {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (moduleObjectDerivedPullback Λ f).CommShift ℤ :=
  Functor.CommShift.ofIso (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm ℤ

/-- The canonical K-injective integer shifts on the total derived module pushforward.
Source: Stacks Tag 015F, blueprint rational proof (3)
(blueprint: lem-sfb-derived-exchange-exact-normalization). -/
instance moduleObjectDerivedPushforwardCommShift {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (moduleObjectDerivedPushforward Λ f).CommShift ℤ :=
  Functor.instCommShiftDerivedCategoryRightDerivedFunctorInt (lowerStar Λ f)

/-- The ambient pullback-square comparison, using the inverse compositor for `(p', g)`,
the square equality, and the compositor for `(g', p)`.
Source: blueprint rational proof (3), canonical exchange
(blueprint: lem-sfb-derived-exchange-exact-normalization). -/
def moduleObjectDerivedPullbackSquareComparison {X Y X' Y' : Scheme.{u}}
    {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : CommSq g' p' p g) :
    moduleObjectDerivedPullback Λ g ⋙ moduleObjectDerivedPullback Λ p' ≅
      moduleObjectDerivedPullback Λ p ⋙ moduleObjectDerivedPullback Λ g' :=
  (leftDerivedUpperStarComp Λ p' g).symm ≪≫
    eqToIso (congrArg (moduleObjectDerivedPullback Λ) sq.w.symm) ≪≫
      leftDerivedUpperStarComp Λ g' p

/-- The ambient unit--square--counit exchange map. `mateEquiv` inserts the unit for `p'`,
applies its right adjoint to the square comparison, and contracts the counit for `p`.
Source: blueprint rational proof (3), canonical exchange
(blueprint: lem-sfb-derived-exchange-exact-normalization). -/
def moduleObjectDerivedExchange {X Y X' Y' : Scheme.{u}}
    {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : CommSq g' p' p g) :
    moduleObjectDerivedPushforward Λ p ⋙ moduleObjectDerivedPullback Λ g ⟶
      moduleObjectDerivedPullback Λ g' ⋙ moduleObjectDerivedPushforward Λ p' :=
  (mateEquiv (derivedUpperStarLowerStarAdjunction Λ p)
    (derivedUpperStarLowerStarAdjunction Λ p')
    (TwoSquare.mk _ _ _ _ (moduleObjectDerivedPullbackSquareComparison Λ sq).hom)).natTrans

variable (ℓ : ℕ) [hℓPrime : Fact ℓ.Prime] {k : Type u} [Field k]
  [hCharPrime : Fact (ringChar k).Prime] [hCharNe : Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Over (Spec (.of k))}
  [hXFiniteType : LocallyOfFiniteType X.hom]
  [hXQuasiCompact : QuasiCompact X.hom]
  [hXSeparated : IsSeparated X.hom]
  [hYFiniteType : LocallyOfFiniteType Y.hom]
  [hYQuasiCompact : QuasiCompact Y.hom]
  [hYSeparated : IsSeparated Y.hom]
  [hXPrimeFiniteType : LocallyOfFiniteType X'.hom]
  [hXPrimeQuasiCompact : QuasiCompact X'.hom]
  [hXPrimeSeparated : IsSeparated X'.hom]
  [hYPrimeFiniteType : LocallyOfFiniteType Y'.hom]
  [hYPrimeQuasiCompact : QuasiCompact Y'.hom]
  [hYPrimeSeparated : IsSeparated Y'.hom]
  {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}
  (sq : CommSq g' p' p g)

include ℓ hℓPrime hCharPrime hCharNe
  hXFiniteType hXQuasiCompact hXSeparated hYFiniteType hYQuasiCompact hYSeparated
  hXPrimeFiniteType hXPrimeQuasiCompact hXPrimeSeparated
  hYPrimeFiniteType hYPrimeQuasiCompact hYPrimeSeparated

set_option linter.unusedSectionVars false

/-- The ambient exchange has the prescribed counit normalization, both ambient functors
are exact with their fixed canonical shifts, and the exchange commutes with every integer
shift. No cartesian hypothesis is imposed.
Source: blueprint rational proof paragraph (3)
(blueprint: lem-sfb-derived-exchange-exact-normalization).

Proof:
1. Exactness of the module pullback is `det-prop-sfb-module-pullback-exact-main`.
The exact-functor derived factorization identifies its K-flat derived functor with the
termwise derived functor, compatibly with shifts. The K-injective construction makes the
additive module pushforward exact. Compose these exact functors.
2. Apply `lem-sp-canonical-right-derived-adjunction-shift` to the underived adjunction.
The derived-counit factorization of `lem-sc-derived-adjunction-from-underived` identifies
the published K-flat adjunction with its transport along the exact comparison: the two
counits agree on K-injectives, and every derived object is isomorphic to one of these.
Thus the actual unit and counit commute with the fixed shifts.
3. By `lem-sfb-exact-derived-natural-iso` and `lem-sfb-exact-derived-composition`, the
published compositor is represented degreewise by the ordinary compositor. Shifting its
degree-r component gives the same map in degree r+n, with the same differential sign.
The inverse compositor and the square equality preserve this compatibility as well.
4. Write a = theta followed by the pullback of the counit. The exchange component is
G'(a) after the unit. Counit naturality and the adjunction triangle identity give
P'(B) followed by the counit = a.
5. The composition and whiskering rules of
`lem-weil-pbc-commshift-nattrans-comp-whisker` apply to the three factors of the mate.
They give the asserted compatibility with every canonical integer shift.
6. Naturality gives the first two squares of the image triangle morphism. Naturality at
its third arrow, followed by the shift equation for n = 1, gives the connecting square.
Exactness makes both image triangles distinguished.
-/
theorem moduleObjectDerivedExchange_exact_normalization :
    (∀ K, (moduleObjectDerivedPullback Λ p'.left).map
        ((moduleObjectDerivedExchange Λ ((Over.forget _).map_commSq sq)).app K) ≫
      (derivedUpperStarLowerStarAdjunction Λ p'.left).counit.app
        ((moduleObjectDerivedPullback Λ g'.left).obj K) =
      (moduleObjectDerivedPullbackSquareComparison Λ ((Over.forget _).map_commSq sq)).hom.app
        ((moduleObjectDerivedPushforward Λ p.left).obj K) ≫
      (moduleObjectDerivedPullback Λ g'.left).map
        ((derivedUpperStarLowerStarAdjunction Λ p.left).counit.app K)) ∧
    (moduleObjectDerivedPushforward Λ p.left ⋙
      moduleObjectDerivedPullback Λ g.left).IsTriangulated ∧
    (moduleObjectDerivedPullback Λ g'.left ⋙
      moduleObjectDerivedPushforward Λ p'.left).IsTriangulated ∧
    NatTrans.CommShift (moduleObjectDerivedExchange Λ ((Over.forget _).map_commSq sq)) ℤ ∧
    (∀ T, T ∈ distTriang _ →
      ∃ b : (moduleObjectDerivedPushforward Λ p.left ⋙
          moduleObjectDerivedPullback Λ g.left).mapTriangle.obj T ⟶
        (moduleObjectDerivedPullback Λ g'.left ⋙
          moduleObjectDerivedPushforward Λ p'.left).mapTriangle.obj T,
        b.hom₁ = (moduleObjectDerivedExchange Λ
          ((Over.forget _).map_commSq sq)).app T.obj₁ ∧
        b.hom₂ = (moduleObjectDerivedExchange Λ
          ((Over.forget _).map_commSq sq)).app T.obj₂ ∧
        b.hom₃ = (moduleObjectDerivedExchange Λ
          ((Over.forget _).map_commSq sq)).app T.obj₃) := by
  sorry

/-- Full-subcategory restriction leaves the exchange components unchanged, provided all
four pullbacks and both pushforwards preserve the chosen triangulated subcategories and
the square comparison is the restriction of the ambient one. The restricted adjunctions
below are the canonical restrictions, with exactly the ambient units and counits.
Source: blueprint rational proof (3), full-subcategory restriction
(blueprint: lem-sfb-derived-exchange-exact-normalization).

Proof: the inclusions are fully faithful and act as the identity on morphisms. The unit,
square comparison and counit have precisely their ambient components, by the restriction
hypotheses and `liftFullSubcategoryAdjunction_unit_app_hom` and its counit counterpart.
Expanding `mateEquiv` therefore gives the same three-factor composite, component by
component. Inherited shifts and distinguished triangles give the same triangle statement.
Taking the four predicates to be `ProEtale.boundedConstructible` gives the stated Dbc
case whenever the hypotheses hold; its base-change map is the three-factor formula of
`boundedConstructibleBaseChangeOfPreserves` (det-def-sfb-base-change-morphism-bc).
-/
theorem moduleObjectDerivedExchange_fullSubcategory
    (S_X : ObjectProperty (DerivedCategory (Mod
      (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) (condensedRingObj Λ X.left))))
    (S_Y : ObjectProperty (DerivedCategory (Mod
      (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1}) (condensedRingObj Λ Y.left))))
    (S_X' : ObjectProperty (DerivedCategory (Mod
      (Sheaf (Scheme.ProEt.topology X'.left) Ab.{u + 1}) (condensedRingObj Λ X'.left))))
    (S_Y' : ObjectProperty (DerivedCategory (Mod
      (Sheaf (Scheme.ProEt.topology Y'.left) Ab.{u + 1}) (condensedRingObj Λ Y'.left))))
    [S_X.IsTriangulated] [S_Y.IsTriangulated]
    [S_X'.IsTriangulated] [S_Y'.IsTriangulated]
    (hPp : ∀ K, S_Y K → S_X ((moduleObjectDerivedPullback Λ p.left).obj K))
    (hPg : ∀ K, S_Y K → S_Y' ((moduleObjectDerivedPullback Λ g.left).obj K))
    (hPp' : ∀ K, S_Y' K → S_X' ((moduleObjectDerivedPullback Λ p'.left).obj K))
    (hPg' : ∀ K, S_X K → S_X' ((moduleObjectDerivedPullback Λ g'.left).obj K))
    (hGp : ∀ K, S_X K → S_Y ((moduleObjectDerivedPushforward Λ p.left).obj K))
    (hGp' : ∀ K, S_X' K → S_Y' ((moduleObjectDerivedPushforward Λ p'.left).obj K))
    (θ : S_Y.liftFullSubcategory S_Y' (moduleObjectDerivedPullback Λ g.left) hPg ⋙
        S_Y'.liftFullSubcategory S_X' (moduleObjectDerivedPullback Λ p'.left) hPp' ≅
      S_Y.liftFullSubcategory S_X (moduleObjectDerivedPullback Λ p.left) hPp ⋙
        S_X.liftFullSubcategory S_X' (moduleObjectDerivedPullback Λ g'.left) hPg')
    (hθ : ∀ K, (θ.hom.app K).hom =
      (moduleObjectDerivedPullbackSquareComparison Λ
        ((Over.forget _).map_commSq sq)).hom.app K.obj) :
    ∀ K, ((mateEquiv
      (ObjectProperty.liftFullSubcategoryAdjunction
        (derivedUpperStarLowerStarAdjunction Λ p.left) hPp hGp)
      (ObjectProperty.liftFullSubcategoryAdjunction
        (derivedUpperStarLowerStarAdjunction Λ p'.left) hPp' hGp')
      (TwoSquare.mk _ _ _ _ θ.hom)).natTrans.app K).hom =
        (moduleObjectDerivedExchange Λ ((Over.forget _).map_commSq sq)).app K.obj := by
  sorry

/-- The bounded-constructible instance of the restriction statement, expressed with the
recorded base-change declaration. Triangulatedness and preservation are hypotheses;
the comparison restriction hypothesis is the equality of the actual components.
Source: blueprint rational proof (3), bounded-constructible specialization
(blueprint: lem-sfb-derived-exchange-exact-normalization).

Proof: use the four bounded-constructible predicates in the preceding restriction
argument. Both restricted functors are the canonical full-subcategory lifts. By
`Adjunction.map_restrictFullyFaithful_unit_app` and its counit counterpart, the
published restricted adjunctions have the ambient units and counits under the
inclusions. The hypothesis identifies the middle square component. Expanding the
three steps of `boundedConstructibleBaseChangeOfPreserves` gives the ambient mate
component, with the same identities and composition in the full subcategory.
-/
theorem boundedConstructibleBaseChangeOfPreserves_app_eq_moduleObjectDerivedExchange
    (H : PreservesBoundedConstructiblePushforwards Λ k)
    [(boundedConstructible (condensedRingObj Λ X.left)).IsTriangulated]
    [(boundedConstructible (condensedRingObj Λ Y.left)).IsTriangulated]
    [(boundedConstructible (condensedRingObj Λ X'.left)).IsTriangulated]
    [(boundedConstructible (condensedRingObj Λ Y'.left)).IsTriangulated]
    (hθ : ∀ K, ((boundedConstructiblePullbackSquareComparison Λ ℓ sq).hom.app K).hom =
      (moduleObjectDerivedPullbackSquareComparison Λ
        ((Over.forget _).map_commSq sq)).hom.app K.obj) :
    ∀ K, ((boundedConstructibleBaseChangeOfPreserves Λ ℓ H sq).app K).hom =
      (moduleObjectDerivedExchange Λ ((Over.forget _).map_commSq sq)).app K.obj := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
