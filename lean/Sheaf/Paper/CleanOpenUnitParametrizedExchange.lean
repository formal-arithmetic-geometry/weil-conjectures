/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Topology.ProfiniteCondensedRing
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Clean open units and whole profinite families

Source: blueprint main-20261015, direct-image proof paragraph (3), agent-extracted
unit and family compatibility input; Stacks Tags 07A7 and 0037
(blueprint: lem-sfb-clean-open-unit-parametrized-exchange).

The pullbacks and units are those of the specified ordinary unbounded derived adjunctions.
The exchange is the actual counit mate, followed by the inverse pullback-square comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.CleanOpenUnit

variable (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]

/-- The canonical comparison for a commutative square, from the two recorded derived
pullback compositors. Source: Stacks 07A7 and the node's proof step 1
(blueprint: lem-sfb-clean-open-unit-parametrized-exchange). -/
def squareComparison {V X V' X' : Scheme.{u}}
    (j : V ⟶ X) (j' : V' ⟶ X') (g : X' ⟶ X) (gV : V' ⟶ V)
    (w : gV ≫ j = j' ≫ g) :
    moduleObjectDerivedPullback Λ.X g ⋙ moduleObjectDerivedPullback Λ.X j' ≅
      moduleObjectDerivedPullback Λ.X j ⋙ moduleObjectDerivedPullback Λ.X gV :=
  (leftDerivedUpperStarComp Λ.X j' g).symm ≪≫
    eqToIso (congrArg (fun f ↦ moduleObjectDerivedPullback Λ.X f) w.symm) ≪≫
      leftDerivedUpperStarComp Λ.X gV j

/-- The normalized exchange on the target of the unit. Its first factor is the
counit mate of the canonical square comparison; its second factor identifies the target
with Rj'_*j'^*g^*K. Source: Stacks 07A7; proof step 2
(blueprint: lem-sfb-clean-open-unit-parametrized-exchange). -/
def exchange {V X V' X' : Scheme.{u}}
    (j : V ⟶ X) (j' : V' ⟶ X') (g : X' ⟶ X) (gV : V' ⟶ V)
    (w : gV ≫ j = j' ≫ g)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X))) :=
  (mateEquiv (derivedUpperStarLowerStarAdjunction Λ.X j)
    (derivedUpperStarLowerStarAdjunction Λ.X j')
    (TwoSquare.mk _ _ _ _ (squareComparison Λ j j' g gV w).hom)).app
      ((moduleObjectDerivedPullback Λ.X j).obj K) ≫
    (moduleObjectDerivedPushforward Λ.X j').map
      ((squareComparison Λ j j' g gV w).inv.app K)

/-- The actual exchange takes the pulled-back source unit to the target unit.
Source: Stacks 07A7 and 0037; blueprint direct-image proof (3), extracted input.
Proof: use the mate formula (step 2), move g^*η through the target unit by naturality,
then move j'^*g^*η through the square comparison by its naturality. The source triangle
identity cancels ε followed by j^*η. Finally cancel the comparison with its inverse.
This is steps 1--2 of the node proof, using the recorded compositor and mate nodes
and lem-weil-pbc-adjunction-of-natural-bijection.
(blueprint: lem-sfb-clean-open-unit-parametrized-exchange). -/
theorem exchange_unit {V X V' X' : Scheme.{u}}
    (j : V ⟶ X) [IsOpenImmersion j] (j' : V' ⟶ X')
    (g : X' ⟶ X) (gV : V' ⟶ V) (s : IsPullback gV j' j g)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X))) :
    (moduleObjectDerivedPullback Λ.X g).map
        ((derivedUpperStarLowerStarAdjunction Λ.X j).unit.app K) ≫
      exchange Λ j j' g gV s.w K =
    (derivedUpperStarLowerStarAdjunction Λ.X j').unit.app
      ((moduleObjectDerivedPullback Λ.X g).obj K) := by
  sorry

/-- Invertible source and target units make the actual exchange invertible and give
its inverse-unit equation. Source: Stacks 0037; extracted direct-image input (3).
Proof: by step 2, b = g^*(η_K^{-1}) followed by η' at g^*K. An explicit inverse is
η'^{-1} followed by g^*η_K. Functoriality preserves the inverse identities; cancelling
η' in this formula gives the displayed equation. This is node proof step 3.
(blueprint: lem-sfb-clean-open-unit-parametrized-exchange). -/
theorem exchange_isIso_and_inverse {V X V' X' : Scheme.{u}}
    (j : V ⟶ X) [IsOpenImmersion j] (j' : V' ⟶ X')
    (g : X' ⟶ X) (gV : V' ⟶ V) (s : IsPullback gV j' j g)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X)))
    [IsIso ((derivedUpperStarLowerStarAdjunction Λ.X j).unit.app K)]
    [IsIso ((derivedUpperStarLowerStarAdjunction Λ.X j').unit.app
      ((moduleObjectDerivedPullback Λ.X g).obj K))] :
    IsIso (exchange Λ j j' g gV s.w K) ∧
      (moduleObjectDerivedPullback Λ.X g).map
          (inv ((derivedUpperStarLowerStarAdjunction Λ.X j).unit.app K)) =
        exchange Λ j j' g gV s.w K ≫
          inv ((derivedUpperStarLowerStarAdjunction Λ.X j').unit.app
            ((moduleObjectDerivedPullback Λ.X g).obj K)) := by
  sorry

/-- Naturality of the unit and of its inverse on the objects where it is invertible.
Source: Stacks 0037; extracted blueprint direct-image input (3).
Proof: apply naturality of the actual unit to u, then compose with the inverse units
on either side and cancel. This is step 4 of the node proof, using
lem-weil-pbc-adjunction-of-natural-bijection.
(blueprint: lem-sfb-clean-open-unit-parametrized-exchange). -/
theorem unit_naturality_and_inverse {V X : Scheme.{u}}
    (j : V ⟶ X) [IsOpenImmersion j]
    (K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X))) (f : K ⟶ L)
    [IsIso ((derivedUpperStarLowerStarAdjunction Λ.X j).unit.app K)]
    [IsIso ((derivedUpperStarLowerStarAdjunction Λ.X j).unit.app L)] :
    (derivedUpperStarLowerStarAdjunction Λ.X j).unit.app K ≫
        (moduleObjectDerivedPushforward Λ.X j).map
          ((moduleObjectDerivedPullback Λ.X j).map f) =
      f ≫ (derivedUpperStarLowerStarAdjunction Λ.X j).unit.app L ∧
    inv ((derivedUpperStarLowerStarAdjunction Λ.X j).unit.app K) ≫ f =
      (moduleObjectDerivedPushforward Λ.X j).map
          ((moduleObjectDerivedPullback Λ.X j).map f) ≫
        inv ((derivedUpperStarLowerStarAdjunction Λ.X j).unit.app L) := by
  sorry

/-- The canonical projection X[Q] → X, using the recorded test-object functor.
Source: blueprint profinite test objects; node proof step 6
(blueprint: lem-sfb-clean-open-unit-parametrized-exchange). -/
abbrev projection (X : Scheme.{u}) (Q : Profinite.{u}) :=
  ((profiniteToProEtOf X).obj Q).hom

/-- V[Q] as the inverse-image open in X[Q]. This is the canonical open model of
Spec LC(Q, ℤ) × V, obtained by pasting the defining fibre products.
Source: blueprint direct-image proof (3), node proof step 6
(blueprint: lem-sfb-clean-open-unit-parametrized-exchange). -/
abbrev familyOpen {X : Scheme.{u}} (V : X.Opens) (Q : Profinite.{u}) :=
  projection X Q ⁻¹ᵁ V

/-- Restriction of a supplied open-preserving family map to V[Q]. The only data
are the existing scheme restriction; its containment proof is the given equality.
Source: blueprint direct-image proof (3), node proof step 6
(blueprint: lem-sfb-clean-open-unit-parametrized-exchange). -/
def familyRestriction {X : Scheme.{u}} (V : X.Opens) (Q : Profinite.{u})
    (a : ((profiniteToProEtOf X).obj Q).left ⟶ X)
    (ha : a ⁻¹ᵁ V = familyOpen V Q) :=
  a.resLE V (familyOpen V Q) ha.ge

/-- The action-family exchange, normalized with the same target open as the projection.
Source: Stacks 07A7; node proof step 6
(blueprint: lem-sfb-clean-open-unit-parametrized-exchange). -/
def familyExchange {X : Scheme.{u}} (V : X.Opens) (Q : Profinite.{u})
    (a : ((profiniteToProEtOf X).obj Q).left ⟶ X)
    (ha : a ⁻¹ᵁ V = familyOpen V Q)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X))) :=
  exchange Λ V.ι (familyOpen V Q).ι a (familyRestriction V Q a ha)
    (Scheme.Hom.resLE_comp_ι a ha.ge) K

/-- Whole-profinite-family equivariance for the supplied module action, including the
inverse-unit action equation. All equalities are morphisms on X[Q] itself.
The existential isomorphism is pinned to the actual a-pullback unit, so specifies its
unique inverse without assuming the missing unit invertible.
Source: blueprint main-20261015 direct-image proof (3), agent-extracted input;
Stacks 07A7 and 0037.
Proof: step 5 applies unit naturality at ρ. Since the projection-pullback unit and ρ
are invertible, so is the a-pullback unit: its inverse is T(ρ) followed by the inverse
projection unit followed by ρ^{-1}. Step 6 pastes the defining test-object fibre
products, applies the unit/mate identity to a and pr, and substitutes those two
identities in naturality at ρ. Step 3 makes both exchanges invertible; cancelling the
two units gives the inverse-action equation. Step 7 specializes to Q a point and to
X[P] as base. No step uses a pointwise detection criterion or units on other objects.
These are node proof steps 3, 5--7, using the recorded profinite-test-object definition
and lem-weil-pbc-adjunction-of-natural-bijection.
(blueprint: lem-sfb-clean-open-unit-parametrized-exchange). -/
theorem parametrized_exchange {X : Scheme.{u}} [IsAffine X]
    (V : X.Opens) (Q : Profinite.{u})
    (a : ((profiniteToProEtOf X).obj Q).left ⟶ X)
    (ha : a ⁻¹ᵁ V = familyOpen V Q)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X)))
    (ρ : (moduleObjectDerivedPullback Λ.X a).obj K ≅
      (moduleObjectDerivedPullback Λ.X (projection X Q)).obj K)
    [IsIso ((derivedUpperStarLowerStarAdjunction Λ.X V.ι).unit.app K)]
    [IsIso ((derivedUpperStarLowerStarAdjunction Λ.X (familyOpen V Q).ι).unit.app
      ((moduleObjectDerivedPullback Λ.X (projection X Q)).obj K))] :
    ∃ e : (moduleObjectDerivedPullback Λ.X a).obj K ≅
        (moduleObjectDerivedPushforward Λ.X (familyOpen V Q).ι).obj
          ((moduleObjectDerivedPullback Λ.X (familyOpen V Q).ι).obj
            ((moduleObjectDerivedPullback Λ.X a).obj K)),
      e.hom = (derivedUpperStarLowerStarAdjunction Λ.X (familyOpen V Q).ι).unit.app
        ((moduleObjectDerivedPullback Λ.X a).obj K) ∧
      IsIso (familyExchange Λ V Q a ha K) ∧
      IsIso (familyExchange Λ V Q (projection X Q) rfl K) ∧
      (moduleObjectDerivedPullback Λ.X a).map
          ((derivedUpperStarLowerStarAdjunction Λ.X V.ι).unit.app K) ≫
        familyExchange Λ V Q a ha K ≫
          (moduleObjectDerivedPushforward Λ.X (familyOpen V Q).ι).map
            ((moduleObjectDerivedPullback Λ.X (familyOpen V Q).ι).map ρ.hom) =
        ρ.hom ≫ (moduleObjectDerivedPullback Λ.X (projection X Q)).map
          ((derivedUpperStarLowerStarAdjunction Λ.X V.ι).unit.app K) ≫
            familyExchange Λ V Q (projection X Q) rfl K ∧
      e.inv ≫ ρ.hom =
        (moduleObjectDerivedPushforward Λ.X (familyOpen V Q).ι).map
          ((moduleObjectDerivedPullback Λ.X (familyOpen V Q).ι).map ρ.hom) ≫
            inv ((derivedUpperStarLowerStarAdjunction Λ.X (familyOpen V Q).ι).unit.app
              ((moduleObjectDerivedPullback Λ.X (projection X Q)).obj K)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.CleanOpenUnit
