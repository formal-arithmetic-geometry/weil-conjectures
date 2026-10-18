/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q100
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Compactification.BaseChange
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion
import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
import Sheaf.AlgebraicGeometry.CompactifiableOverField
import Sheaf.AlgebraicGeometry.DerivedCategories
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-!
# Compact-support actions and arbitrary base change

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
lem-amb-linear-trace-invariance.proof.md, paragraphs 1 and 2
(blueprint: lem-amb-compact-action-base-change).

The constructions below use the ordinary etale bounded-below derived formalism.
The exchange is the existing exchange for the actual Cartesian square, followed by
its existing canonical comparison to the supplied target compactification.

## Main statements

* `compactSupportActionSquare`: the automorphism square is Cartesian.
* `compactSupportAction_id`: the identity coefficient action is the identity.
* `compactSupportActionBaseChange`: invertibility, independence of compactification,
  and the equality of actual action morphisms under arbitrary base change.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The automorphism square over the identity is Cartesian. Its comparison to the
chosen pullback is the universal map `(a, f)`.
Source: blueprint linear-trace proof, paragraph 1
(blueprint: lem-amb-compact-action-base-change).

Proof: The comparison is `pullback.lift a.hom f`. Its inverse is the first projection
followed by `a.inv`. The identities follow by the two projection identities and
`a.hom ≫ f = f`; uniqueness is def-pc-fibre-product. -/
theorem compactSupportActionSquare {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : X ≅ X) (ha : a.hom ≫ f = f) : IsPullback a.hom f f (𝟙 Y) := by
  sorry

/-- The canonical compact-support exchange, with any supplied target compactification.
Source: blueprint linear-trace proof, paragraphs 1 and 2; thm-cbc-finite-torsion
(blueprint: lem-amb-compact-action-base-change).
It is the exchange for `c.ofIsPullback sq`, followed by the canonical compactification
comparison, rather than a freely chosen isomorphism. -/
noncomputable def compactSupportActionExchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [QuasiCompact f']
    (sq : IsPullback g' f' f g) (c : Compactification f) (d : Compactification f') :
    (derivedPlusFormalism (ModuleCat.{u + 1} A)).shriek c ⋙
        (derivedPlusFormalism (ModuleCat.{u + 1} A)).pb g ⟶
      (derivedPlusFormalism (ModuleCat.{u + 1} A)).pb g' ⋙
        (derivedPlusFormalism (ModuleCat.{u + 1} A)).shriek d :=
  rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap A sq c ≫
    Functor.whiskerLeft ((derivedPlusFormalism (ModuleCat.{u + 1} A)).pb g')
      ((derivedPlusFormalism (ModuleCat.{u + 1} A)).shriekIso (c.ofIsPullback sq) d).hom

/-- The actual morphism `Rf_!(theta) ∘ E_a(K)`, including the identity-pullback
identification on the base.
Source: blueprint linear-trace proof, paragraph 1
(blueprint: lem-amb-compact-action-base-change). -/
noncomputable def compactSupportAction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f]
    (c : Compactification f) {a : X ⟶ X} (sq : IsPullback a f f (𝟙 Y))
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (theta : ((derivedPlusFormalism (ModuleCat.{u + 1} A)).pb a).obj K ≅ K) :
    ((derivedPlusFormalism (ModuleCat.{u + 1} A)).shriek c).obj K ⟶
      ((derivedPlusFormalism (ModuleCat.{u + 1} A)).shriek c).obj K :=
  (upperStarIdDerivedPlus (ModuleCat.{u + 1} A) Y).inv.app _ ≫
    (compactSupportActionExchange A sq c c).app K ≫
    ((derivedPlusFormalism (ModuleCat.{u + 1} A)).shriek c).map theta.hom

/-- The actual fibre-product automorphism `a ×_Y 1_T`.
Source: blueprint linear-trace proof, paragraph 2
(blueprint: lem-amb-compact-action-base-change). -/
noncomputable def compactSupportActionPullback
    {X Y : Scheme.{u}} (f : X ⟶ Y) (a : X ≅ X) (ha : a.hom ≫ f = f)
    {T : Scheme.{u}} (u : T ⟶ Y) : pullback f u ≅ pullback f u :=
  asIso (pullback.map f u f u a.hom (𝟙 T) (𝟙 Y)
    (by simpa only [Category.comp_id] using ha.symm) (by simp))

/-- Pull back the coefficient isomorphism through the canonical inverse-image
composition comparison attached to `u' a_T = a u'`.
Source: blueprint linear-trace proof, paragraph 2
(blueprint: lem-amb-compact-action-base-change). -/
noncomputable def compactSupportActionPullbackCoefficient
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (a : X ≅ X) (ha : a.hom ≫ f = f)
    {T : Scheme.{u}} (u : T ⟶ Y)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (theta : ((derivedPlusFormalism (ModuleCat.{u + 1} A)).pb a.hom).obj K ≅ K) :
    ((derivedPlusFormalism (ModuleCat.{u + 1} A)).pb
        (compactSupportActionPullback f a ha u).hom).obj
          (((derivedPlusFormalism (ModuleCat.{u + 1} A)).pb (pullback.fst f u)).obj K) ≅
      ((derivedPlusFormalism (ModuleCat.{u + 1} A)).pb (pullback.fst f u)).obj K :=
  ((derivedPlusFormalism (ModuleCat.{u + 1} A)).sqIso
      (compactSupportActionPullback f a ha u).hom (pullback.fst f u)
      (pullback.fst f u) a.hom (by simp [compactSupportActionPullback, pullback.map])).app K ≪≫
    ((derivedPlusFormalism (ModuleCat.{u + 1} A)).pb (pullback.fst f u)).mapIso theta

/-- The identity action, with `theta` the canonical identification of identity inverse
image with `K`, is the identity morphism.
Source: blueprint linear-trace proof, paragraph 1
(blueprint: lem-amb-compact-action-base-change).

Proof: Apply the identity clause of thm-cbc-finite-torsion. Its canonical comparisons
cancel the inserted identity-pullback identification, and functoriality sends the
identity coefficient morphism to the identity. -/
theorem compactSupportAction_id
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) [QuasiCompact c.i]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    compactSupportAction A c
        (compactSupportActionSquare f (Iso.refl X) (Category.id_comp f)) K
        ((upperStarIdDerivedPlus (ModuleCat.{u + 1} A) X).app K) = 𝟙 _ := by
  sorry

/-- Compact-support actions are automorphisms, commute with every canonical
compactification comparison, and commute with arbitrary base change using any supplied
compactification on the fibre product.
Source: blueprint linear-trace proof, paragraphs 1 and 2
(blueprint: lem-amb-compact-action-base-change).

Proof, following the five steps of the DAG node:
1. Use compactSupportActionSquare: the comparison `(a,f)` has inverse `a.inv pr_1`.
2. thm-cbc-finite-torsion makes exchange invertible. The coefficient isomorphism is
sent to an isomorphism by Rf_!, hence the composite action is invertible. Naturality
of the canonical comparisons from lem-amb-etale-compact-comparisons gives the displayed
independence equation for any second compactification.
3. The identity clause is compactSupportAction_id, by the identity exchange law.
4. The fibre product is Noetherian by finite type over the Noetherian T, using
lem-pod-separated-finite-type-base-change and lem-weil-pbc-finite-type-over-noetherian.
Its pulled-back open is quasi-compact by lem-pc-quasi-compact-base-change. The fibre-product
universal property gives `u' a_T = a u'`. Let delta identify `u'^* a^* K` with
`a_T^* u'^* K`, and put D = F_T(delta) C_u(a^*K). Horizontal pasting in
thm-cbc-finite-torsion gives D u^*E_a = E_aT C_u. Naturality at theta gives
C_u u^*F(theta) = F_T(theta_T) D. Associativity yields the displayed equation.
5. The same theorem makes exchange independent of all compactification choices.
Naturality of the comparisons from lem-amb-etale-compact-comparisons also transports
F_T(theta_T) and F_T(delta). Thus the equation uses the specified maps for arbitrary d,
even when d is not the pulled-back compactification. -/
theorem compactSupportActionBaseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) [QuasiCompact c.i]
    (a : X ≅ X) (ha : a.hom ≫ f = f)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (theta : ((derivedPlusFormalism (ModuleCat.{u + 1} A)).pb a.hom).obj K ≅ K) :
    IsIso (compactSupportAction A c (compactSupportActionSquare f a ha) K theta) ∧
    (∀ (d : Compactification f) [QuasiCompact d.i],
      compactSupportAction A c (compactSupportActionSquare f a ha) K theta ≫
          ((derivedPlusFormalism (ModuleCat.{u + 1} A)).shriekIso c d).hom.app K =
        ((derivedPlusFormalism (ModuleCat.{u + 1} A)).shriekIso c d).hom.app K ≫
          compactSupportAction A d (compactSupportActionSquare f a ha) K theta) ∧
    (∀ (T : Scheme.{u}) [IsNoetherian T] (u : T ⟶ Y)
      (d : Compactification (pullback.snd f u)) [QuasiCompact d.i],
      ((derivedPlusFormalism (ModuleCat.{u + 1} A)).pb u).map
          (compactSupportAction A c (compactSupportActionSquare f a ha) K theta) ≫
          (compactSupportActionExchange A (IsPullback.of_hasPullback f u) c d).app K =
        (compactSupportActionExchange A (IsPullback.of_hasPullback f u) c d).app K ≫
          compactSupportAction A d
            (compactSupportActionSquare (pullback.snd f u)
              (compactSupportActionPullback f a ha u)
              (by simp [compactSupportActionPullback, pullback.map]))
            (((derivedPlusFormalism (ModuleCat.{u + 1} A)).pb (pullback.fst f u)).obj K)
            (compactSupportActionPullbackCoefficient A f a ha u K theta)) := by
  sorry

end AlgebraicGeometry.Etale
