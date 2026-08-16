/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!

# Exactness of left Kan extension along a fully faithful functor with empty fibers

Let `L : C ⥤ D` be a fully faithful functor such that every object `Y` of `D` is either in
the essential image of `L` or has empty comma category `CostructuredArrow L Y`. Then left
Kan extension along `L` is computed by

* `(L.lan.obj F).obj (L.obj X) ≅ F.obj X` in the first case, since the unit of the Kan
  extension is an isomorphism for fully faithful `L`;
* an initial object in the second case, being a colimit over an empty category.

In particular, if the initial object of `H` is a zero object, left Kan extension along `L`
preserves every limit that exists in `H`
(`CategoryTheory.Functor.preservesLimitsOfShape_lan_of_essImage_or_isEmpty`). This is the
abstract form of the statement that extension by zero along an open immersion is left
exact.

## Main results

- `CategoryTheory.Limits.preservesLimitsOfShape_of_isTerminal_obj`: a functor all of whose
  values are terminal preserves all limits.
- `CategoryTheory.Limits.isInitialOfIsColimitOfIsEmpty`: a colimit of a diagram indexed by
  an empty category is an initial object.
- `CategoryTheory.Functor.isInitialLanObjObj`: the left Kan extension is initial at an
  object with empty comma category.
- `CategoryTheory.Functor.evaluationObjIsoLanCompEvaluation`: for fully faithful `L`,
  evaluating the left Kan extension at `L.obj X` is evaluation at `X`.
- `CategoryTheory.Functor.preservesLimitsOfShape_lan_of_essImage_or_isEmpty`: the exactness
  statement.

-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits

namespace Limits

variable {C : Type u₁} [Category.{v₁} C] {H : Type u₂} [Category.{v₂} H]

/-- A functor whose values are all terminal objects preserves all limits: both the lift and
its uniqueness are supplied by terminality of the values. -/
lemma preservesLimitsOfShape_of_isTerminal_obj {F : C ⥤ H} (hF : ∀ X, IsTerminal (F.obj X))
    (J : Type*) [Category* J] : PreservesLimitsOfShape J F where
  preservesLimit := ⟨fun {c} _ ↦ ⟨{
    lift s := (hF c.pt).from s.pt
    fac _ _ := (hF _).hom_ext _ _
    uniq _ _ _ := (hF _).hom_ext _ _ }⟩⟩

/-- A colimit of a diagram indexed by an empty category is an initial object. -/
def isInitialOfIsColimitOfIsEmpty {J : Type*} [Category* J] [IsEmpty J] {K : J ⥤ H}
    {c : Cocone K} (hc : IsColimit c) : IsInitial c.pt where
  desc s := hc.desc ⟨s.pt, ⟨fun j ↦ isEmptyElim j, fun {j} ↦ isEmptyElim j⟩⟩
  fac _ j := j.as.elim
  uniq _ _ _ := hc.hom_ext fun j ↦ isEmptyElim j

end Limits

namespace Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {H : Type u₃} [Category.{v₃} H] (L : C ⥤ D)

section

variable [∀ F : C ⥤ H, L.HasPointwiseLeftKanExtension F]

/-- If the comma category `CostructuredArrow L Y` is empty, the left Kan extension of any
functor along `L` is initial at `Y`: it is a colimit over an empty category. -/
noncomputable def isInitialLanObjObj (F : C ⥤ H) {Y : D} (hY : IsEmpty (CostructuredArrow L Y)) :
    IsInitial ((L.lan.obj F).obj Y) :=
  have := hY
  isInitialOfIsColimitOfIsEmpty (L.isPointwiseLeftKanExtensionLeftKanExtensionUnit F Y)

variable [L.Full] [L.Faithful]

/-- For a fully faithful `L`, evaluating the left Kan extension along `L` at `L.obj X` is
evaluation at `X`; the isomorphism is the unit of the Kan extension. -/
@[simps! hom_app]
noncomputable def evaluationObjIsoLanCompEvaluation (X : C) :
    (evaluation C H).obj X ≅ L.lan ⋙ (evaluation D H).obj (L.obj X) :=
  NatIso.ofComponents (fun F ↦ asIso ((L.lanUnit.app F).app X))
    fun {_ _} φ ↦ congr_app (L.lanUnit.naturality φ) X

end

/-- Left Kan extension along a fully faithful functor `L` preserves every limit that exists
in the target category, provided every object of `D` is either in the essential image of `L`
or has empty comma category, and the initial object of `H` is a zero object.

This is the abstract form of the left exactness of extension by zero along an open
immersion: on the presheaf level, the extension of `F` is `F` on objects lying over the open
subobject and zero elsewhere. -/
lemma preservesLimitsOfShape_lan_of_essImage_or_isEmpty [L.Full] [L.Faithful] [HasZeroMorphisms H]
    [∀ F : C ⥤ H, L.HasPointwiseLeftKanExtension F]
    (hL : ∀ Y : D, (∃ X : C, Nonempty (L.obj X ≅ Y)) ∨ IsEmpty (CostructuredArrow L Y))
    (J : Type*) [Category* J] [HasLimitsOfShape J H] :
    PreservesLimitsOfShape J (L.lan : (C ⥤ H) ⥤ D ⥤ H) := by
  refine preservesLimitsOfShape_of_evaluation _ _ fun Y ↦ ?_
  rcases hL Y with ⟨X, ⟨e⟩⟩ | hY
  · exact preservesLimitsOfShape_of_natIso
      (L.evaluationObjIsoLanCompEvaluation X ≪≫ isoWhiskerLeft L.lan ((evaluation D H).mapIso e))
  · exact preservesLimitsOfShape_of_isTerminal_obj
      (fun F ↦ (L.isInitialLanObjObj F hY).isZero.isTerminal) J

/-- Left Kan extension along a fully faithful functor with empty fibers is left exact.
See `CategoryTheory.Functor.preservesLimitsOfShape_lan_of_essImage_or_isEmpty`. -/
lemma preservesFiniteLimits_lan_of_essImage_or_isEmpty [L.Full] [L.Faithful] [HasZeroMorphisms H]
    [∀ F : C ⥤ H, L.HasPointwiseLeftKanExtension F] [HasFiniteLimits H]
    (hL : ∀ Y : D, (∃ X : C, Nonempty (L.obj X ≅ Y)) ∨ IsEmpty (CostructuredArrow L Y)) :
    PreservesFiniteLimits (L.lan : (C ⥤ H) ⥤ D ⥤ H) where
  preservesFiniteLimits _ := L.preservesLimitsOfShape_lan_of_essImage_or_isEmpty hL _

end Functor

end CategoryTheory
