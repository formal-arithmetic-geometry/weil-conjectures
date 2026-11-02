/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Closed.ProEtaleClosedLiftOverlapRelations

/-! # The actual-arrow complex of the closed-lift augmentation

Source: Steps 2--3 of `lem-sp-proetale-closed-lift-kernel-overlap-presentation`.
(blueprint: def-sp-proetale-closed-lift-arrow-complex).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- The coproduct indexed only by actual arrows from closed-lift tests into `P`.
Source: Step 2 of `lem-sp-proetale-closed-lift-kernel-overlap-presentation`.
(blueprint: def-sp-proetale-closed-lift-arrow-complex). -/
noncomputable abbrev ClosedLiftArrowSource (A : Type u) [CommRing A]
    {X Z : Scheme.{u}} (z : Z ⟶ X) (P : X.ProEt) :=
  ∐ fun t : ClosedLiftArrowIndex z P ↦
    (ProEtale.freeSheaf (ULift.{u + 1, u} A) X).obj t.val.1

/-- The actual-arrow summands map to their summands in the full augmentation.
Source: Step 2 of `lem-sp-proetale-closed-lift-kernel-overlap-presentation`.
(blueprint: def-sp-proetale-closed-lift-arrow-complex). -/
noncomputable def closedLiftArrowAugmentation (A : Type u) [CommRing A]
    {X Z : Scheme.{u}} (z : Z ⟶ X) (P : X.ProEt) :
    ClosedLiftArrowSource A z P ⟶
      (closedLiftGeneratorAugmentation A z
        ((ProEtale.freeSheaf (ULift.{u + 1, u} A) X).obj P)).left :=
  Sigma.desc (fun t ↦ closedLiftArrowι A z P t)

/-- Differences of the two projections of each overlap into the actual-arrow source.
The overlap object need not itself be a test.
Source: Step 3 of `lem-sp-proetale-closed-lift-kernel-overlap-presentation`.
(blueprint: def-sp-proetale-closed-lift-arrow-complex). -/
noncomputable def closedLiftArrowBoundary (A : Type u) [CommRing A]
    {X Z : Scheme.{u}} (z : Z ⟶ X) (P : X.ProEt) :
    (∐ fun ts : ClosedLiftArrowIndex z P × ClosedLiftArrowIndex z P ↦
      (ProEtale.freeSheaf (ULift.{u + 1, u} A) X).obj
        (pullback ts.1.val.2 ts.2.val.2)) ⟶ ClosedLiftArrowSource A z P :=
  let F := ProEtale.freeSheaf (ULift.{u + 1, u} A) X
  Sigma.desc (fun ts ↦
    F.map (pullback.fst ts.1.val.2 ts.2.val.2) ≫
        Sigma.ι (fun t : ClosedLiftArrowIndex z P ↦ F.obj t.val.1) ts.1 -
      F.map (pullback.snd ts.1.val.2 ts.2.val.2) ≫
        Sigma.ι (fun t : ClosedLiftArrowIndex z P ↦ F.obj t.val.1) ts.2)

/-- The boundary has exactly the prescribed elementary overlap map in the full source.
Source: Step 3 of `lem-sp-proetale-closed-lift-kernel-overlap-presentation`.
(blueprint: def-sp-proetale-closed-lift-arrow-complex).

Proof: on each overlap summand, both sides are the difference of the two free
projection maps followed by the original summand inclusions. The right side
has this expression by the kernel-lift equation. -/
theorem closedLiftArrowBoundary_comp (A : Type u) [CommRing A]
    {X Z : Scheme.{u}} (z : Z ⟶ X) (P : X.ProEt) :
    closedLiftArrowBoundary A z P ≫ closedLiftArrowAugmentation A z P =
      closedLiftOverlapRelationsMap A z P ≫
        kernel.ι (closedLiftGeneratorAugmentation A z
          ((ProEtale.freeSheaf (ULift.{u + 1, u} A) X).obj P)).hom := by
  apply Sigma.hom_ext
  intro ts
  simp [closedLiftArrowBoundary, closedLiftArrowAugmentation,
    closedLiftOverlapRelationsMap, closedLiftOverlapRelation, Category.assoc,
    Preadditive.sub_comp]

/-- The actual-arrow boundary is killed by arrow evaluation.
Source: the pullback equation, equivalently the original kernel equation.
(blueprint: def-sp-proetale-closed-lift-arrow-complex).

Proof: substitute the preceding compatibility and apply the kernel equation. -/
theorem closedLiftArrowBoundary_zero (A : Type u) [CommRing A]
    {X Z : Scheme.{u}} (z : Z ⟶ X) (P : X.ProEt) :
    closedLiftArrowBoundary A z P ≫
      (closedLiftArrowAugmentation A z P ≫ (closedLiftGeneratorAugmentation A z
        ((ProEtale.freeSheaf (ULift.{u + 1, u} A) X).obj P)).hom) = 0 := by
  rw [← Category.assoc, closedLiftArrowBoundary_comp]
  simp only [Category.assoc, kernel.condition, comp_zero]

end AlgebraicGeometry.Scheme
