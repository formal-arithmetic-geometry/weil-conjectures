/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSmallGenerator

/-!
# The affine etale generator separates sheaf maps

## References

* Stacks Project, Tags 01DO and 03EW
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem integer_isSeparator :
    IsSeparator (AddCommGrpCat.of (ULift.{u + 1} ℤ)) := by
  intro A B f g h
  simp_all only [ObjectProperty.singleton_iff, AddCommGrpCat.ext_iff,
    AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply,
    forall_eq', ULift.forall]
  intro x
  specialize h (AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (fun y ↦ y • x) fun y z ↦ by simp only [add_smul])) 1
  simpa using h

/-- The constructed affine free-Yoneda coproduct separates all large-valued etale sheaves
(Stacks, Tag 03EW). -/
theorem etaleSmallGenerator_isSeparator (X : Scheme.{u}) :
    IsSeparator (etaleSmallGenerator X) := by
  let C := SmallModel.{u} X.AffineEtale
  let e := equivSmallModel.{u} X.AffineEtale
  let J := e.inverse.inducedTopology (AffineEtale.topology X)
  let : HasSheafify J AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.hasSheafify_of_essentiallySmall AddCommGrpCat.{u + 1} J
  let : HasColimitsOfSize.{u, u} AddCommGrpCat.{u + 1} :=
    hasColimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  let : HasColimitsOfSize.{u, u} (Sheaf J AddCommGrpCat.{u + 1}) :=
    Sheaf.instHasColimitsOfSize
  let Q : C × Unit → Sheaf J AddCommGrpCat.{u + 1} :=
    fun (⟨c, _⟩ : C × Unit) ↦ Sheaf.freeYoneda J c (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  let : HasColimitsOfShape (Discrete (C × Unit)) (Sheaf J AddCommGrpCat.{u + 1}) :=
    HasColimitsOfSize.has_colimits_of_shape (C := Sheaf J AddCommGrpCat.{u + 1}) _
  let : HasColimit (Discrete.functor Q) := HasColimitsOfShape.has_colimit _
  unfold etaleSmallGenerator
  apply IsSeparator.of_equivalence
  apply IsSeparator.of_equivalence
  apply Sheaf.isSeparator (S := fun _ : Unit ↦ AddCommGrpCat.of (ULift.{u + 1} ℤ))
  intro A B f g h
  apply integer_isSeparator.{u} f g
  intro Z hZ a
  rw [ObjectProperty.singleton_iff] at hZ
  subst Z
  exact h _ (ObjectProperty.ofObj_apply _ ()) a

end AlgebraicGeometry.Scheme
