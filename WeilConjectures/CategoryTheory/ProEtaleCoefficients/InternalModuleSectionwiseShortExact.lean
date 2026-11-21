/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact

/-! # Sectionwise short exactness of internal sheaf modules

Source: Stacks Tags 03CL, 03CN, 03CO.

The canonical sheaf tensor is selected as an instance, with
the sheafification, additivity and colimit-preservation interfaces derived from its
recorded declarations. All three short complexes retain the prescribed arrows by functorial
mapping.
-/

@[expose] public section

set_option autoImplicit false

universe uC vC w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

/-- Left exact abelian sheafification on the essentially small site, transported from its
small model in the coefficient universe. -/
noncomputable instance sectionwiseShortExactSheafify
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) : HasSheafify J AddCommGrpCat.{w} := by
  let : HasSheafify ((equivSmallModel.{w} C).inverse.inducedTopology J)
      AddCommGrpCat.{w} := GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  exact hasSheafifyEssentiallySmallSite J AddCommGrpCat.{w}

/-- The canonical sheafified tensor over the integers. -/
noncomputable instance sectionwiseShortExactSheafMonoidal
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) : MonoidalCategory (Sheaf J AddCommGrpCat.{w}) :=
  (sfbSheafTensorStructure (A := AddCommGrpCat.{w}) J).monoidal

/-- The symmetry of the same canonical sheaf tensor. -/
noncomputable instance sectionwiseShortExactSheafSymmetric
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) : SymmetricCategory (Sheaf J AddCommGrpCat.{w}) :=
  (sfbSheafTensorStructure (A := AddCommGrpCat.{w}) J).symmetric

/-- Closedness of the canonical sheaf tensor. -/
@[instance_reducible]
noncomputable def sectionwiseShortExactSheafClosed
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) : MonoidalClosed (Sheaf J AddCommGrpCat.{w}) :=
  (sfbSheafTensor_properties.{uC, vC, w + 1, w, 0, 0}
    (A := AddCommGrpCat.{w}) J).2.1.some

/-- Additivity of the canonical sheaf tensor in each variable. -/
noncomputable instance sectionwiseShortExactSheafPreadditive
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) : MonoidalPreadditive (Sheaf J AddCommGrpCat.{w}) :=
  letI := sectionwiseShortExactSheafClosed J
  sfbSheafTensor_monoidalPreadditive

/-- Left tensor with a sheaf preserves finite colimits. -/
noncomputable instance sectionwiseShortExactSheafLeftColimits
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) (F : Sheaf J AddCommGrpCat.{w}) :
    PreservesFiniteColimits (tensorLeft F) :=
  ((sfbSheafTensor_properties.{uC, vC, w + 1, w, 0, 0}
    (A := AddCommGrpCat.{w}) J).2.2 F).2.2.1

end CategoryTheory

namespace CategoryTheory.Mod

/-- Sectionwise short exactness implies short exactness of the underlying presheaves,
the underlying sheaves, and the internal modules, with the same arrows.

Source: Stacks Tags 03CL, 03CN, 03CO. -/
theorem shortExact_of_sectionwise
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C)
    (R : Sheaf J AddCommGrpCat.{w}) [MonObj R]
    (S : ShortComplex (Mod (Sheaf J AddCommGrpCat.{w}) R))
    (hS : ∀ V : C,
      ((S.map (forget R)).map (sheafToPresheaf J AddCommGrpCat.{w}) |>.map
        ((evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op V))).ShortExact) :
    ((S.map (forget R)).map (sheafToPresheaf J AddCommGrpCat.{w})).ShortExact ∧
      (S.map (forget R)).ShortExact ∧ S.ShortExact := by
  let U := forget (D := Sheaf J AddCommGrpCat.{w}) R
  let i := sheafToPresheaf J AddCommGrpCat.{w}
  have hEval : JointlyReflectIsomorphisms
      (fun V : Cᵒᵖ ↦ (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj V) := by
    constructor
    intro P Q f hf
    let : ∀ V, IsIso (f.app V) := hf
    exact NatIso.isIso_of_isIso_app f
  have hP : ((S.map U).map i).ShortExact :=
    (hEval.shortExact_iff _).2 (fun V ↦ hS V.unop)
  have hSheaf : (S.map U).ShortExact := by
    have h := hP.map_of_exact (presheafToSheaf J AddCommGrpCat.{w})
    exact ShortComplex.shortExact_of_iso
      ((S.map U).mapNatIso (sheafificationNatIso J AddCommGrpCat.{w})).symm h
  have hU : JointlyReflectIsomorphisms (fun _ : Unit ↦ U) := by
    constructor
    intro M N f hf
    let : IsIso (U.map f) := hf ()
    exact isIso_of_reflects_iso f U
  exact ⟨hP, hSheaf, (hU.shortExact_iff S).2 (fun _ ↦ hSheaf)⟩

end CategoryTheory.Mod
