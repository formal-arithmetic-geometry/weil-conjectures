/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.LogRegularPair
public import Mathlib.CategoryTheory.Endomorphism

/-!
# Very tame actions on divisorial log pairs

Source: ILO, Exposé VI, 3.1, printed p. 73
(blueprint: def-per-very-tame-divisorial-action).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Rebase an étale neighbourhood by an automorphism of its base, retaining its
underlying scheme. Source: ILO VI 3.1, the action on strict-local stalks
(blueprint: def-per-very-tame-divisorial-action). -/
def automorphismEtaleNeighbourhood {X : Scheme.{u}} (e : Aut X) (W : X.Etale) : X.Etale :=
  Scheme.Etale.mk (W.hom ≫ e.hom)

/-- A fixed geometric point remains a lift to the rebased neighbourhood.
Source: ILO VI 3.1 (blueprint: def-per-very-tame-divisorial-action). -/
noncomputable def automorphismEtaleLift {X : Scheme.{u}} (e : Aut X) {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X) (ht : t ≫ e.hom = t)
    (W : X.Etale) (w : (Scheme.pointSmallEtale t).fiber.obj W) :
    (Scheme.pointSmallEtale t).fiber.obj (automorphismEtaleNeighbourhood e W) :=
  Over.homMk w.left (by
    change w.left ≫ (W.hom ≫ e.hom) = t
    have hw : w.left ≫ W.hom = t := w.w
    rw [← Category.assoc, hw, ht])

/-- The canonical map on strict local rings, constructed by rebasing all pointed
étale neighbourhoods in the actual ring colimit. It acts by inverse pullback, which
has the same fixed elements and triviality conditions as pullback by the automorphism.
Source: ILO VI 3.1 (blueprint: def-per-very-tame-divisorial-action). -/
noncomputable def automorphismStrictLocalMap {X : Scheme.{u}} (e : Aut X) {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X) (ht : t ≫ e.hom = t) :
    strictLocalRing X t →+* strictLocalRing X t :=
  ((Scheme.pointSmallEtale t).presheafFiberDesc
    (P := X.etaleStructurePresheaf)
    (fun W w ↦ strictLocalGerm X t (automorphismEtaleNeighbourhood e W)
      (automorphismEtaleLift e t ht W w)) (by
        intro W V f w
        let f' : automorphismEtaleNeighbourhood e W ⟶ automorphismEtaleNeighbourhood e V :=
          MorphismProperty.Over.homMk f.left (by
            change f.left ≫ (V.hom ≫ e.hom) = W.hom ≫ e.hom
            rw [← Category.assoc, MorphismProperty.Over.w f])
        have hw : (Scheme.pointSmallEtale t).fiber.map f'
            (automorphismEtaleLift e t ht W w) =
            automorphismEtaleLift e t ht V ((Scheme.pointSmallEtale t).fiber.map f w) := by
          apply Over.OverMorphism.ext
          rfl
        have h := (Scheme.pointSmallEtale t).toPresheafFiber_w f'
          (automorphismEtaleLift e t ht W w) X.etaleStructurePresheaf
        rw [hw] at h
        exact h)).hom

/-- Very tameness is imposed on the geometric stabilizer, not the ordinary point
stabilizer. Its order is invertible in the residue field (automatic in characteristic
zero), each log germ changes by a ring unit, and every strict-local function is fixed
modulo the ideal of nonunit log germs. These are respectively tameness, triviality
on the characteristic monoid, and triviality on the strict-local stratum scheme.
Source: ILO VI 3.1 (blueprint: def-per-very-tame-divisorial-action). -/
def IsVeryTameDivisorialAction {X : Scheme.{u}} (U : X.Opens)
    {G : Type v} [Group G] [Finite G] (a : G →* Aut X) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X),
    IsUnit (Nat.card {g : G // t ≫ (a g).hom = t} : Ω) ∧
      ∀ (g : G) (hg : t ≫ (a g).hom = t),
        (∀ m : divisorialStalk U.ι t, ∃ z : (strictLocalRing X t)ˣ,
          automorphismStrictLocalMap (a g) t hg m = z.val * (m : strictLocalRing X t)) ∧
        ∀ r : strictLocalRing X t,
          automorphismStrictLocalMap (a g) t hg r - r ∈
            divisorialNonunitIdeal (divisorialStalk U.ι t)

end AlgebraicGeometry
