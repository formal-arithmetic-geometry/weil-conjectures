/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Closed.ProEtaleClosedLiftGenerators

/-! # Elementary overlap relations in the canonical closed-lift augmentation

Source: Step 1 of `lem-sp-proetale-proper-closed-lift-relations`.
(blueprint: def-sp-proetale-closed-lift-overlap-relations).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- The property of an object used to index the closed-lift augmentation.

Source: `def-sp-proetale-closed-lift-generators`.
(blueprint: def-sp-proetale-closed-lift-overlap-relations). -/
def ClosedLiftTest {X Z : Scheme.{u}} (z : Z ⟶ X) (U : X.ProEt) : Prop :=
  IsAffine U.left ∧
    (∀ (M N : Sheaf (ProEt.topology X) (Type (u + 1))) (f : M ⟶ N),
      Epi f → Function.Surjective (f.hom.app (op U))) ∧
    (∀ x : U.left, ∃ y : ↥(pullback U.hom z),
      Specializes x ((pullback.fst U.hom z) y))

/-- Individual arrows into `P` from the tests of the canonical augmentation.

Source: Step 1 of `lem-sp-proetale-proper-closed-lift-relations`.
(blueprint: def-sp-proetale-closed-lift-overlap-relations). -/
def ClosedLiftArrowIndex {X Z : Scheme.{u}} (z : Z ⟶ X) (P : X.ProEt) :=
  {t : Σ U : X.ProEt, U ⟶ P // ClosedLiftTest z t.1}

/-- The summand of the canonical augmentation corresponding to one arrow into `P`.

Source: Step 1 of `lem-sp-proetale-proper-closed-lift-relations`.
(blueprint: def-sp-proetale-closed-lift-overlap-relations). -/
noncomputable def closedLiftArrowι (A : Type u) [CommRing A] {X Z : Scheme.{u}}
    (z : Z ⟶ X) (P : X.ProEt) (t : ClosedLiftArrowIndex z P) :
    (ProEtale.freeSheaf (ULift.{u + 1, u} A) X).obj t.val.1 ⟶
      (closedLiftGeneratorAugmentation A z
        ((ProEtale.freeSheaf (ULift.{u + 1, u} A) X).obj P)).left := by
  let F := ProEtale.freeSheaf (ULift.{u + 1, u} A) X
  let J := {s : Σ U : X.ProEt, F.obj U ⟶ F.obj P // ClosedLiftTest z s.1}
  exact Sigma.ι (fun s : J ↦ F.obj s.val.1) ⟨⟨t.val.1, F.map t.val.2⟩, t.property⟩

/-- Composing a summand inclusion with the augmentation recovers the free arrow.

Source: the coproduct universal property.
(blueprint: def-sp-proetale-closed-lift-overlap-relations). -/
@[simp] theorem closedLiftArrowι_augmentation (A : Type u) [CommRing A]
    {X Z : Scheme.{u}} (z : Z ⟶ X) (P : X.ProEt) (t : ClosedLiftArrowIndex z P) :
    closedLiftArrowι A z P t ≫ (closedLiftGeneratorAugmentation A z
        ((ProEtale.freeSheaf (ULift.{u + 1, u} A) X).obj P)).hom =
      (ProEtale.freeSheaf (ULift.{u + 1, u} A) X).map t.val.2 := by
  simp [closedLiftArrowι, closedLiftGeneratorAugmentation, ClosedLiftTest]

/-- The difference of the two summands on their overlap over `P`, lifted to the kernel.
No specialization property is imposed on the overlap itself.

Source: Step 1 of `lem-sp-proetale-proper-closed-lift-relations`.
(blueprint: def-sp-proetale-closed-lift-overlap-relations).

Construction: subtract the two free projection maps followed by their summand inclusions.
Their images under the augmentation agree by the pullback equation. The kernel universal
property therefore supplies the displayed map, without any unproved choice of data. -/
noncomputable def closedLiftOverlapRelation (A : Type u) [CommRing A]
    {X Z : Scheme.{u}} (z : Z ⟶ X) (P : X.ProEt) (t s : ClosedLiftArrowIndex z P) :
    (ProEtale.freeSheaf (ULift.{u + 1, u} A) X).obj (pullback t.val.2 s.val.2) ⟶
      kernel (closedLiftGeneratorAugmentation A z
        ((ProEtale.freeSheaf (ULift.{u + 1, u} A) X).obj P)).hom := by
  let F := ProEtale.freeSheaf (ULift.{u + 1, u} A) X
  refine kernel.lift _
    (F.map (pullback.fst t.val.2 s.val.2) ≫ closedLiftArrowι A z P t -
      F.map (pullback.snd t.val.2 s.val.2) ≫ closedLiftArrowι A z P s) ?_
  simp only [Preadditive.sub_comp, Category.assoc, closedLiftArrowι_augmentation]
  change F.map (pullback.fst t.val.2 s.val.2) ≫ F.map t.val.2 -
    F.map (pullback.snd t.val.2 s.val.2) ≫ F.map s.val.2 = 0
  rw [← F.map_comp, ← F.map_comp, pullback.condition, sub_self]

/-- The coproduct of all elementary overlap maps.

Source: Step 1 of `lem-sp-proetale-proper-closed-lift-relations`.
(blueprint: def-sp-proetale-closed-lift-overlap-relations). -/
noncomputable def closedLiftOverlapRelationsMap (A : Type u) [CommRing A]
    {X Z : Scheme.{u}} (z : Z ⟶ X) (P : X.ProEt) :
    (∐ fun ts : ClosedLiftArrowIndex z P × ClosedLiftArrowIndex z P ↦
      (ProEtale.freeSheaf (ULift.{u + 1, u} A) X).obj
        (pullback ts.1.val.2 ts.2.val.2)) ⟶
      kernel (closedLiftGeneratorAugmentation A z
        ((ProEtale.freeSheaf (ULift.{u + 1, u} A) X).obj P)).hom :=
  Sigma.desc (fun ts ↦ closedLiftOverlapRelation A z P ts.1 ts.2)

/-- Any relation defined on a closed-lift test vanishes in the augmentation cokernel.

Source: the canonical indexing in `def-sp-proetale-closed-lift-generators`.
(blueprint: def-sp-proetale-closed-lift-overlap-relations).

Proof: the given map itself indexes one summand. Precompose the cokernel equation
with that summand inclusion and use the coproduct descent equation. -/
theorem closedLiftTestRelation_cokernel (A : Type u) [CommRing A]
    {X Z : Scheme.{u}} (z : Z ⟶ X)
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (U : X.ProEt) (hU : ClosedLiftTest z U)
    (r : (ProEtale.freeSheaf (ULift.{u + 1, u} A) X).obj U ⟶ M) :
    r ≫ cokernel.π (closedLiftGeneratorAugmentation A z M).hom = 0 := by
  let F := ProEtale.freeSheaf (ULift.{u + 1, u} A) X
  let J := {t : Σ V : X.ProEt, F.obj V ⟶ M // ClosedLiftTest z t.1}
  have H := congrArg (fun k ↦ Sigma.ι (fun t : J ↦ F.obj t.val.1)
    ⟨⟨U, r⟩, hU⟩ ≫ k) (cokernel.condition (closedLiftGeneratorAugmentation A z M).hom)
  simpa only [closedLiftGeneratorAugmentation, Arrow.mk_hom, Category.assoc,
    Sigma.ι_desc_assoc, comp_zero] using H

end AlgebraicGeometry.Scheme
