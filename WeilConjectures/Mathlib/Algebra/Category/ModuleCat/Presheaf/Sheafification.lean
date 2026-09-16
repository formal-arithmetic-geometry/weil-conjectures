/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Sheafification of presheaves of modules

Let `α : R₀ ⟶ R.val` be a locally bijective morphism from a presheaf of rings to (the underlying
presheaf of) a sheaf of rings on a site `(C, J)`. The sheafification of presheaves of modules
`PresheafOfModules R₀ ⥤ SheafOfModules R` is left adjoint to the forgetful functor, and its
counit is always an isomorphism; we package that counit as a natural isomorphism. We also record
that the unit is an isomorphism at a presheaf of modules whose underlying presheaf is a sheaf, so
that if *every* presheaf of `R₀`-modules is a sheaf — as happens over a topological space with at
most one point — the sheafification is an equivalence of categories.

## Main declarations

- `PresheafOfModules.sheafificationCounitIso`: the counit of the sheafification adjunction, as a
  natural isomorphism.
- `PresheafOfModules.isIso_sheafificationAdjunction_unit_app`: the unit of the sheafification
  adjunction is an isomorphism at a presheaf of modules which is a sheaf.
- `PresheafOfModules.sheafificationEquivalenceOfIsSheaf`: if every presheaf of `R₀`-modules is a
  sheaf, the sheafification is an equivalence of categories.
- `SheafOfModules.sheafification`: the sheafification of presheaves of modules over the
  underlying presheaf of rings of a sheaf of commutative rings, and
  `SheafOfModules.sheafificationObjIso`, the counit isomorphism at a sheaf of modules.

-/

@[expose] public section

universe v v' u u'

open CategoryTheory

section LocallyBijective

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] [HasWeakSheafify J AddCommGrpCat.{v}]

namespace PresheafOfModules

/-- Sheafifying the underlying presheaf of modules of a sheaf of modules gives the sheaf back:
the counit of the sheafification adjunction is a natural isomorphism. -/
noncomputable def sheafificationCounitIso :
    (SheafOfModules.forget.{v} R ⋙ restrictScalars α) ⋙ sheafification.{v} α ≅ 𝟭 _ :=
  asIso (sheafificationAdjunction.{v} α).counit

/-- The unit of the sheafification adjunction for presheaves of modules is an isomorphism at a
presheaf of modules whose underlying presheaf is already a sheaf. -/
theorem isIso_sheafificationAdjunction_unit_app (M₀ : PresheafOfModules.{v} R₀)
    (h : Presheaf.IsSheaf J M₀.presheaf) :
    IsIso ((sheafificationAdjunction α).unit.app M₀) := by
  have : IsIso ((toPresheaf _).map ((sheafificationAdjunction α).unit.app M₀)) := by
    rw [toPresheaf_map_sheafificationAdjunction_unit_app]
    exact isIso_toSheafify _ h
  exact isIso_of_reflects_iso _ (toPresheaf _)

/-- **If every presheaf of `R₀`-modules is a sheaf, the sheafification of presheaves of modules
is an equivalence of categories**, quasi-inverse to the forgetful functor. -/
noncomputable def sheafificationEquivalenceOfIsSheaf
    (h : ∀ M₀ : PresheafOfModules.{v} R₀, Presheaf.IsSheaf J M₀.presheaf) :
    PresheafOfModules.{v} R₀ ≌ SheafOfModules.{v} R :=
  have := fun M₀ ↦ isIso_sheafificationAdjunction_unit_app α M₀ (h M₀)
  (sheafificationAdjunction α).toEquivalence

end PresheafOfModules

end LocallyBijective

section CommRing

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (R : Sheaf J CommRingCat.{u})

namespace SheafOfModules

/-- The sheafification functor from presheaves of modules over the underlying presheaf of rings
of a sheaf of commutative rings `R` to sheaves of modules over `R`. This is
`PresheafOfModules.sheafification` for the identity of the underlying presheaf of rings; it is
spelled with the domain `PresheafOfModules (R.obj ⋙ forget₂ _ _)` so that the monoidal structure
on presheaves of modules is found by instance resolution. -/
noncomputable abbrev sheafification :
    PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat.{u}) ⥤
      SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R) :=
  PresheafOfModules.sheafification (𝟙 _)

/-- Sheafifying the underlying presheaf of modules of a sheaf of modules `F` gives `F` back.
This is the counit of the sheafification adjunction,
`PresheafOfModules.sheafificationCounitIso`, evaluated at `F`. -/
noncomputable def sheafificationObjIso
    (F : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)) :
    (sheafification R).obj
      ((SheafOfModules.forget
        ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)).obj F) ≅ F :=
  (PresheafOfModules.sheafificationCounitIso
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R).obj)).app F

end SheafOfModules

end CommRing
