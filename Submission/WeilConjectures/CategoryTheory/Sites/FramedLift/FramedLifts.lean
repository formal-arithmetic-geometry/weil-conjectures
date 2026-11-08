/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.CategoryTheory.Sites.WithSection.TorsorWithSection

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Lifting torsors with a prescribed section

Source: Stacks Project, Tag 03AJ, relative refinement: the lifting-torsor construction
with its chosen lift over an object of the site.
(blueprint: lem-amb-framed-lifts-classification).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf.Torsor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {G E Q : Sheaf J AddCommGrpCat.{w}} {ι : G ⟶ E} {d : E ⟶ Q} {w₀ : ι ≫ d = 0}
  {T : C} (hT : IsTerminal T) (hS : (ShortComplex.mk ι d w₀).ShortExact) (U : C)

/-- A global quotient section together with its lift over U.
Source: Stacks Project, Tag 03AJ, relative refinement.
(blueprint: lem-amb-framed-lifts-classification). -/
def FramedLift :=
  (s : Q.obj.obj (op T)) × (lifts hT hS s).sheaf.obj.obj (op U)

/-- The lifting torsor with its specified local lift.
Source: Stacks Project, Tag 03AJ, relative refinement.
(blueprint: lem-amb-framed-lifts-classification). -/
def FramedLift.toPair (z : FramedLift hT hS U) : WithSection G U :=
  ⟨lifts hT hS z.1, z.2⟩

/-- Every pointed torsor has a pointed lifting presentation when E is injective.
Source: Stacks Project, Tag 03AJ, relative refinement, step 5.
(blueprint: lem-amb-framed-lifts-classification).
Proof: present the underlying torsor as a lifting torsor using injectivity, and transport
its specified section along that isomorphism. -/
theorem FramedLift.surjective [Injective E] :
    Function.Surjective (fun z : FramedLift hT hS U ↦
      (_root_.Quotient.mk _ z.toPair : WithSection.Classes G U)) := by
  intro p
  induction p using _root_.Quotient.inductionOn with
  | h p =>
    obtain ⟨s, ⟨e⟩⟩ := exists_equiv_lifts hT hS p.1
    refine ⟨⟨s, e.iso.hom.hom.app (op U) p.2⟩, _root_.Quotient.sound ?_⟩
    exact ⟨e.symm, by
      change e.iso.inv.hom.app (op U) (e.iso.hom.hom.app (op U) p.2) = p.2
      exact congrArg (fun f ↦ f.hom.app (op U) p.2) e.iso.hom_inv_id⟩

/-- The zero quotient section with its zero lift.
Source: Stacks Project, Tag 03AJ, relative refinement, step 6.
(blueprint: lem-amb-framed-lifts-classification). -/
def FramedLift.zero : FramedLift hT hS U :=
  ⟨0, ⟨0, by change d.hom.app (op U) 0 = Q.obj.map _ 0; simp⟩⟩

/-- Classes of framed lifts, identifying precisely global translations.
Source: Stacks Project, Tag 03AJ, relative refinement, steps 3 and 4.
(blueprint: lem-amb-framed-lifts-classification). -/
def FramedLift.setoid : Setoid (FramedLift hT hS U) :=
  Setoid.comap (FramedLift.toPair hT hS U) (WithSection.setoid G U)

/-- Framed lifting presentations modulo global translation.
Source: Stacks Project, Tag 03AJ, relative refinement.
(blueprint: lem-amb-framed-lifts-classification). -/
def FramedLift.Classes := _root_.Quotient (FramedLift.setoid hT hS U)

/-- The canonical identification of framed lifting classes with pointed torsor classes.
Source: Stacks Project, Tag 03AJ, relative refinement, steps 3 through 5.
(blueprint: lem-amb-framed-lifts-classification). -/
noncomputable def FramedLift.classEquiv [Injective E] :
    FramedLift.Classes hT hS U ≃ WithSection.Classes G U :=
  Equiv.ofBijective
    (_root_.Quotient.map (FramedLift.toPair hT hS U) (fun _ _ h ↦ h)) (by
      constructor
      · intro a b h
        induction a using _root_.Quotient.inductionOn with | h a =>
          induction b using _root_.Quotient.inductionOn with | h b =>
            exact _root_.Quotient.sound (show
              WithSection.IsIsomorphic a.toPair b.toPair from _root_.Quotient.exact h)
      · intro p
        obtain ⟨z, hz⟩ := FramedLift.surjective hT hS U p
        exact ⟨_root_.Quotient.mk _ z, hz⟩)

end CategoryTheory.Sheaf.Torsor

-- Check the axioms of the completed construction.
#print axioms CategoryTheory.Sheaf.Torsor.FramedLift.classEquiv
