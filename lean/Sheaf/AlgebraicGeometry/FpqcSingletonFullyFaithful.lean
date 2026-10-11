/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum

/-!
# Fully faithful pullback of descent data along an fpqc singleton

Source: Stacks Project, Descent, Lemma 0241 (lemma-fully-faithful)
(blueprint: lem-galois-fpqc-singleton-fully-faithful-0241).

## Main definitions

- `CategoryTheory.Over.DescentDataCategory`: the category `DD(X/S)` of descent data on
  schemes over `X` relative to `a : X ⟶ S`, with the morphisms of descent data.

## Main statements

- `CategoryTheory.fpqc_singleton_pullback_fullyFaithful`: pullback of descent data along a
  singleton fpqc covering `r : X' ⟶ X` is fully faithful.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace CategoryTheory

namespace Over

/-- Objects of the category of descent data relative to `X/S`, in the transport form of
`Over.DescentDatum`. Source: Stacks Project, Descent, Definition 35.34.1 (Tag 023V)
(blueprint: lem-galois-fpqc-singleton-fully-faithful-0241). -/
structure DescentDataCategory {S X : Scheme.{u}} (a : X ⟶ S) where
  V : Over X
  datum : DescentDatum a V

namespace DescentDataCategory

variable {S X : Scheme.{u}} {a : X ⟶ S}

/-- Morphisms over `X` compatible with the two descent data. Source: Stacks Project,
Descent, Definition 35.34.1 (3) (Tag 023V)
(blueprint: lem-galois-fpqc-singleton-fully-faithful-0241). -/
@[ext]
structure Hom (A B : DescentDataCategory a) where
  hom : A.V ⟶ B.V
  commutes : ∀ {T : Scheme.{u}} (f₀ f₁ : T ⟶ X) (h : f₀ ≫ a = f₁ ≫ a)
    (z : Over.mk f₀ ⟶ A.V),
    B.datum.transport f₀ f₁ h (z ≫ hom) =
      A.datum.transport f₀ f₁ h z ≫ hom

instance : Category (DescentDataCategory a) where
  Hom := Hom
  id A :=
    { hom := 𝟙 A.V
      commutes := by
        intro T f₀ f₁ h z
        simp only [Category.comp_id] }
  comp := fun {A B C} f g =>
    { hom := f.hom ≫ g.hom
      commutes := by
        intro T i j h z
        change C.datum.transport i j h ((z ≫ f.hom) ≫ g.hom) =
          (A.datum.transport i j h z ≫ f.hom) ≫ g.hom
        rw [g.commutes, f.commutes] }
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl

end DescentDataCategory

end Over

/--
Let `a : X ⟶ S` be a morphism of schemes and let `r : X' ⟶ X` be a singleton
fpqc covering.  Pullback along `r` gives a fully faithful functor from descent
data on schemes over `X` relative to `X/S` to descent data on schemes over
`X'` relative to `X'/S`.

Source: Stacks Project, Descent, Lemma 0241 (lemma-fully-faithful), assumptions
(1)--(2) and conclusion (blueprint: lem-galois-fpqc-singleton-fully-faithful-0241).

For each object, `q` exhibits the image as the pullback of its underlying scheme,
and `IsBaseChange` identifies its datum with the pulled-back datum. Naturality
of `q` says that the functor maps each morphism to its pullback.

For fullness, restrict the compatibility equation of a morphism of pulled-back
data along `X' ×_X X' → X' ×_S X'`. The diagonal identity of a descent datum
makes this the overlap equation. Descend the underlying morphism along the fpqc
cover by Tag 02W0. To check the descended map preserves descent data, pull the
equation back along `X' ×_S X' → X ×_S X`, factor this map into two base changes
of the cover, and use fpqc descent of morphisms twice. The same descent lemma
gives uniqueness and hence faithfulness.
-/
theorem fpqc_singleton_pullback_fullyFaithful
    {S X X' : Scheme.{u}} (a : X ⟶ S) (r : X' ⟶ X)
    (hr : Presieve.singleton r ∈ Scheme.fpqcPrecoverage X) :
    ∃ (F : Over.DescentDataCategory a ⥤ Over.DescentDataCategory (r ≫ a))
      (q : ∀ A : Over.DescentDataCategory a, (F.obj A).V.left ⟶ A.V.left),
      Nonempty F.FullyFaithful ∧
      (∀ A, ∃ hq : q A ≫ A.V.hom = (F.obj A).V.hom ≫ r,
        IsPullback (q A) (F.obj A).V.hom A.V.hom r ∧
        Over.DescentDatum.IsBaseChange rfl hq A.datum (F.obj A).datum) ∧
      ∀ A B (f : A ⟶ B), (F.map f).hom.left ≫ q B = q A ≫ f.hom.left := by
  sorry

end CategoryTheory
