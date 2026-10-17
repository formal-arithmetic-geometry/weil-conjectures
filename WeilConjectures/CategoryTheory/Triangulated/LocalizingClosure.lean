/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Localizing subcategories and localizing closures

Let `C` be a pretriangulated category. A property of objects `P` of `C` is *localizing*
(`CategoryTheory.ObjectProperty.IsLocalizing`) if it is a triangulated subcategory, closed under
isomorphisms and under coproducts indexed by types in `Type w`. The *localizing closure*
`Loc(G)` of a property `G` (`CategoryTheory.ObjectProperty.localizingClosure`) is the smallest
localizing property containing `G`.

The main statement is the principle by which functors are restricted to localizing closures
(`CategoryTheory.ObjectProperty.localizingClosure_obj`): a triangulated functor `F : C ⥤ D`
preserving coproducts with `F(G) ⊆ Loc(G')` maps `Loc(G)` into `Loc(G')`, because the objects
`K ∈ Loc(G)` with `F(K) ∈ Loc(G')` form a localizing property containing `G`.
-/

@[expose] public section

universe w

namespace CategoryTheory.ObjectProperty

open Limits Pretriangulated ZeroObject

variable {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A property of objects of a pretriangulated category is *localizing* if it is a triangulated
subcategory, closed under isomorphisms and under coproducts indexed by types in `Type w`. -/
structure IsLocalizing (P : ObjectProperty C) : Prop where
  isTriangulated : P.IsTriangulated
  isClosedUnderIsomorphisms : P.IsClosedUnderIsomorphisms
  prop_of_isColimit {J : Type w} {X : J → C} {c : Cofan X} (hc : IsColimit c)
    (hX : ∀ j, P (X j)) : P c.pt

/-- The *localizing closure* `Loc(G)` of a property of objects `G`: the smallest localizing
property containing `G` (for coproducts indexed by types in `Type w`). -/
def localizingClosure (G : ObjectProperty C) : ObjectProperty C :=
  fun X ↦ ∀ P : ObjectProperty C, P.IsLocalizing.{w} → G ≤ P → P X

variable (G : ObjectProperty C)

lemma le_localizingClosure : G ≤ localizingClosure.{w} G :=
  fun _ hX _ _ hG ↦ hG _ hX

lemma localizingClosure_le {P : ObjectProperty C} (hP : P.IsLocalizing.{w}) (h : G ≤ P) :
    localizingClosure.{w} G ≤ P :=
  fun _ hX ↦ hX P hP h

instance : (localizingClosure.{w} G).IsClosedUnderIsomorphisms where
  of_iso e hX P hP hG :=
    have := hP.isClosedUnderIsomorphisms
    P.prop_of_iso e (hX P hP hG)

instance : (localizingClosure.{w} G).IsTriangulated where
  exists_zero := ⟨0, isZero_zero C, fun P hP _ ↦
    have := hP.isTriangulated
    have := hP.isClosedUnderIsomorphisms
    P.prop_of_isZero (isZero_zero C)⟩
  isStableUnderShiftBy a := ⟨fun X hX P hP hG ↦
    have := hP.isTriangulated
    P.le_shift a X (hX P hP hG)⟩
  ext₂' T hT h₁ h₃ := ObjectProperty.le_isoClosure _ _ fun P hP hG ↦
    have := hP.isTriangulated
    have := hP.isClosedUnderIsomorphisms
    P.ext_of_isTriangulatedClosed₂ T hT (h₁ P hP hG) (h₃ P hP hG)

/-- The localizing closure is localizing. -/
lemma isLocalizing_localizingClosure : (localizingClosure.{w} G).IsLocalizing.{w} where
  isTriangulated := inferInstance
  isClosedUnderIsomorphisms := inferInstance
  prop_of_isColimit hc hX P hP hG := hP.prop_of_isColimit hc fun j ↦ hX j P hP hG

/-- Induction principle for the localizing closure: if the objects with some property `P` form a
localizing subcategory containing `G`, then every object of `Loc(G)` has the property. -/
lemma localizingClosure_induction {P : ObjectProperty C} (hP : P.IsLocalizing.{w})
    (h : G ≤ P) {X : C} (hX : localizingClosure.{w} G X) : P X :=
  hX P hP h

variable {D : Type*} [Category* D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Blueprint `det-proper-image-localizing-principle`: Functors preserving sums and generators
preserve the localizing closures.

Let `F : C ⥤ D` be a triangulated functor preserving coproducts indexed by types in `Type w`, and
let `G`, `G'` be properties of objects of `C` and `D` with `F(G) ⊆ Loc(G')`. Then
`F(Loc(G)) ⊆ Loc(G')`: the objects `K` with `F(K) ∈ Loc(G')` form a localizing property
containing `G`. (The restriction `Loc(G) ⥤ Loc(G')` is then triangulated and preserves
coproducts, the triangulated structures and the coproducts of the localizing subcategories
being those of `C` and `D`.) -/
lemma localizingClosure_obj (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    [∀ J : Type w, PreservesColimitsOfShape (Discrete J) F] {G' : ObjectProperty D}
    (h : ∀ X, G X → localizingClosure.{w} G' (F.obj X)) {X : C}
    (hX : localizingClosure.{w} G X) : localizingClosure.{w} G' (F.obj X) := by
  refine localizingClosure_induction G (P := fun X ↦ localizingClosure.{w} G' (F.obj X))
    ⟨⟨⟨0, isZero_zero C, (localizingClosure.{w} G').prop_of_isZero
      (F.map_isZero (isZero_zero C))⟩, ⟨fun a ↦ ⟨fun Y hY ↦ ?_⟩⟩,
      ⟨fun T hT h₁ h₃ ↦ ObjectProperty.le_isoClosure _ _
        ((localizingClosure.{w} G').ext_of_isTriangulatedClosed₂ _
          (F.map_distinguished T hT) h₁ h₃)⟩⟩,
      ⟨fun e hY ↦ (localizingClosure.{w} G').prop_of_iso (F.mapIso e) hY⟩,
      fun {J} Y c hc hY ↦ ?_⟩ h hX
  · exact (localizingClosure.{w} G').prop_of_iso ((F.commShiftIso a).app Y).symm
      ((localizingClosure.{w} G').le_shift a _ hY)
  · have hc' : IsColimit (Cofan.mk (F.obj c.pt) fun j ↦ F.map (c.inj j) :
        Cofan fun j ↦ F.obj (Y j)) :=
      isColimitCofanMkObjOfIsColimit F Y (fun j ↦ c.inj j)
        (IsColimit.ofIsoColimit hc (Cofan.ext (Iso.refl _) (fun _ ↦ by simp)))
    exact (isLocalizing_localizingClosure G').prop_of_isColimit hc' hY

end CategoryTheory.ObjectProperty
