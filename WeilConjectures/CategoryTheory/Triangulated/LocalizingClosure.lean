/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# The localizing closure of a property of objects

Let `C` be a pretriangulated category. A property of objects `P : ObjectProperty C` is
*localizing* (`CategoryTheory.ObjectProperty.IsLocalizing`) if it is a triangulated
subcategory, closed under isomorphisms and under coproducts indexed by types in a fixed universe
`w`. The *localizing closure* `P.localizingClosure` of `P` is the smallest localizing property
containing `P` (the generic part of blueprint `sk-def-localizing-closure`: for
`P = Dctf(X, Λ)` it is `Loc(Dctf(X, Λ))`).

## Main definitions and results

- `CategoryTheory.ObjectProperty.IsLocalizing`, `CategoryTheory.ObjectProperty.localizingClosure`.
- `CategoryTheory.ObjectProperty.le_localizingClosure`,
  `CategoryTheory.ObjectProperty.localizingClosure_le_of_le`: the universal property.
- `CategoryTheory.ObjectProperty.localizingClosure_le_inverseImage`
  (`det-proper-image-localizing-principle`): a triangulated functor preserving coproducts which
  maps `P` into `Loc(P')` maps `Loc(P)` into `Loc(P')`.
-/

@[expose] public section

universe w

namespace CategoryTheory

open Category Limits Pretriangulated ZeroObject

namespace ObjectProperty

variable {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A property of objects of a pretriangulated category is *localizing* if it is a triangulated
subcategory, closed under isomorphisms and under coproducts indexed by types in `Type w`. -/
class IsLocalizing (P : ObjectProperty C) : Prop extends P.IsTriangulated,
    P.IsClosedUnderIsomorphisms where
  isClosedUnderCoproducts (J : Type w) : P.IsClosedUnderColimitsOfShape (Discrete J)

attribute [instance] IsLocalizing.isClosedUnderCoproducts

/-- The *localizing closure* of `P`: the smallest localizing property of objects containing `P`,
i.e. the intersection of all localizing properties containing `P`. -/
def localizingClosure (P : ObjectProperty C) : ObjectProperty C :=
  fun X ↦ ∀ (Q : ObjectProperty C) [Q.IsLocalizing.{w}], P ≤ Q → Q X

variable (P : ObjectProperty C)

lemma le_localizingClosure : P ≤ P.localizingClosure.{w} :=
  fun _ hX _ _ hPQ ↦ hPQ _ hX

/-- The universal property of the localizing closure: it is contained in every localizing
property containing `P`. -/
lemma localizingClosure_le_of_le {Q : ObjectProperty C} [Q.IsLocalizing.{w}] (h : P ≤ Q) :
    P.localizingClosure.{w} ≤ Q :=
  fun _ hX ↦ hX Q h

instance : (P.localizingClosure.{w}).IsClosedUnderIsomorphisms where
  of_iso e hX Q _ hPQ := Q.prop_of_iso e (hX Q hPQ)

instance : (P.localizingClosure.{w}).IsLocalizing.{w} where
  exists_zero := ⟨0, isZero_zero C, fun Q _ _ ↦ Q.prop_of_isZero (isZero_zero C)⟩
  isStableUnderShiftBy n :=
    { le_shift X hX Q _ hPQ := Q.le_shift n X (hX Q hPQ) }
  toIsTriangulatedClosed₂ := .mk' fun T hT h₁ h₃ Q _ hPQ ↦
    Q.ext_of_isTriangulatedClosed₂ T hT (h₁ Q hPQ) (h₃ Q hPQ)
  isClosedUnderCoproducts J :=
    { colimitsOfShape_le := by
        rintro X ⟨h⟩ Q _ hPQ
        exact Q.prop_of_isColimit h.isColimit fun j ↦ h.prop_diag_obj j Q hPQ }

lemma localizingClosure_monotone {Q : ObjectProperty C} (h : P ≤ Q) :
    P.localizingClosure.{w} ≤ Q.localizingClosure.{w} :=
  localizingClosure_le_of_le P (h.trans (le_localizingClosure Q))

lemma localizingClosure_eq_self [P.IsLocalizing.{w}] : P.localizingClosure.{w} = P :=
  le_antisymm (localizingClosure_le_of_le P le_rfl) (le_localizingClosure P)

/-- Blueprint `det-proper-image-localizing-principle`: a triangulated functor `F : C ⥤ D`
preserving coproducts indexed by `Type w` which maps the objects of `P` into `Loc(P')` maps
`Loc(P)` into `Loc(P')`: the objects `X` with `F X ∈ Loc(P')` form a localizing property. -/
lemma localizingClosure_le_inverseImage {D : Type*} [Category* D] [HasZeroObject D]
    [HasShift D ℤ] [Preadditive D] [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
    (P : ObjectProperty C) (P' : ObjectProperty D) {F : C ⥤ D} [F.CommShift ℤ]
    [F.IsTriangulated] [∀ J : Type w, PreservesColimitsOfShape (Discrete J) F]
    (h : P ≤ (P'.localizingClosure.{w}).inverseImage F) :
    P.localizingClosure.{w} ≤ (P'.localizingClosure.{w}).inverseImage F := by
  have : ((P'.localizingClosure.{w}).inverseImage F).IsLocalizing.{w} :=
    { isClosedUnderCoproducts J :=
        { colimitsOfShape_le := by
            rintro X ⟨h⟩
            exact (P'.localizingClosure.{w}).prop_of_isColimit
              (isColimitOfPreserves F h.isColimit) h.prop_diag_obj } }
  exact localizingClosure_le_of_le P h

end ObjectProperty

end CategoryTheory
