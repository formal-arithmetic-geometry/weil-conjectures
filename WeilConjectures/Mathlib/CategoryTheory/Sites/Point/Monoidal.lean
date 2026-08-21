/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Monoidal
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# Fiber functors are braided

Let `Φ` be a point of a site `(C, J)`. Let `A` be a braided monoidal category where the
tensor product commutes with filtered colimits in both variables. We upgrade the monoidal
structures on the fiber functors `Φ.presheafFiber : (Cᵒᵖ ⥤ A) ⥤ A` and
`Φ.sheafFiber : Sheaf J A ⥤ A` from `Mathlib.CategoryTheory.Sites.Point.Monoidal` to
braided structures. For the presheaf fiber functor this is a direct computation with the
colimit presentation of the fiber; the sheaf fiber functor inherits the braiding by
descent along the braided essentially surjective functor `presheafToSheaf J A`
(`CategoryTheory.Functor.Braided.ofPrecompEssSurj`).

Since a symmetric monoidal functor is by definition a braided functor between symmetric
monoidal categories, this also covers the symmetric case.
-/

@[expose] public section

universe w v v' u u'

namespace CategoryTheory.GrothendieckTopology.Point

open Limits MonoidalCategory Functor Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (Φ : Point.{w} J)
  {A : Type u'} [Category.{v'} A] [MonoidalCategory A] [BraidedCategory A]
  [HasColimitsOfSize.{w, w} A] [LocallySmall.{w} C]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{w, w} (tensorRight X)]

/-- The fiber functor on presheaves given by a point of a site is braided. -/
noncomputable instance : (Φ.presheafFiber (A := A)).Braided where
  braided P₁ P₂ := by
    rw [← cancel_epi (δ Φ.presheafFiber P₁ P₂), ← cancel_mono (δ Φ.presheafFiber P₂ P₁)]
    simp only [Category.assoc, Functor.Monoidal.δ_μ_assoc, Functor.Monoidal.μ_δ,
      Category.comp_id]
    ext X x
    simp [BraidedCategory.braiding_naturality]

section SheafFiber

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

variable [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A] [HasProducts.{w} A]

/-- The fiber functor on sheaves given by a point of a site is braided. -/
noncomputable instance : (Φ.sheafFiber (A := A)).Braided := by
  haveI := Localization.essSurj (presheafToSheaf J A) J.W
  letI : NatTrans.IsMonoidal (Φ.presheafToSheafCompSheafFiberIso A).symm.hom :=
    inferInstanceAs (NatTrans.IsMonoidal (Φ.presheafToSheafCompSheafFiberIso A).inv)
  letI : (presheafToSheaf J A ⋙ Φ.sheafFiber (A := A)).LaxBraided :=
    Functor.LaxBraided.ofNatIso (Φ.presheafToSheafCompSheafFiberIso A).symm
  exact Functor.Braided.ofPrecompEssSurj (presheafToSheaf J A) Φ.sheafFiber
    (fun P₁ P₂ ↦ Functor.LaxBraided.braided P₁ P₂)

end SheafFiber

end CategoryTheory.GrothendieckTopology.Point
