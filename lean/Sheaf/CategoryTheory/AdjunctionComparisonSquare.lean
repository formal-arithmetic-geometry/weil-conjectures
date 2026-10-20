/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M7
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # A square of normalized adjunction comparisons

Source: Stacks Project, Tag 07A6, and the uniqueness of adjoints.
-/

@[expose] public section

set_option autoImplicit false
open CategoryTheory

namespace CategoryTheory.Adjunction

/-- Counit-compatible squares intertwine the canonical right-adjoint comparisons.
Source: Stacks Project, Tag 07A6.
(blueprint: lem-kun-adjunction-comparison-square).

Proof: apply the inverse second Hom bijection to both sides. The two counit
normalizations replace the right-adjoint comparison maps by the ordinary counits.
Naturality moves the left comparisons past the remaining maps. The compatibility
of the left-adjoint square then gives equality. -/
theorem rightAdjointUniq_square
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    {L₁' L₂' : C' ⥤ D'} {R₁' R₂' : D' ⥤ C'}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₁' : L₁' ⊣ R₁') (a₂' : L₂' ⊣ R₂')
    (Q : C ⥤ C') (P : D ⥤ D')
    (i₁ : Q ⋙ L₁' ≅ L₁ ⋙ P) (i₂ : Q ⋙ L₂' ≅ L₂ ⋙ P)
    (u₁ : ∀ X, Q.obj (R₁.obj X) ⟶ R₁'.obj (P.obj X))
    (u₂ : ∀ X, Q.obj (R₂.obj X) ⟶ R₂'.obj (P.obj X))
    (h₁ : ∀ X, L₁'.map (u₁ X) ≫ a₁'.counit.app (P.obj X) =
      i₁.hom.app (R₁.obj X) ≫ P.map (a₁.counit.app X))
    (h₂ : ∀ X, L₂'.map (u₂ X) ≫ a₂'.counit.app (P.obj X) =
      i₂.hom.app (R₂.obj X) ≫ P.map (a₂.counit.app X))
    (e : L₁ ≅ L₂) (e' : L₁' ≅ L₂')
    (he : ∀ M, i₁.hom.app M ≫ P.map (e.hom.app M) =
      e'.hom.app (Q.obj M) ≫ i₂.hom.app M) (X : D) :
    u₁ X ≫ ((a₁'.ofNatIsoLeft e').rightAdjointUniq a₂').hom.app (P.obj X) =
      Q.map (((a₁.ofNatIsoLeft e).rightAdjointUniq a₂).hom.app X) ≫ u₂ X := by
  apply (a₂'.homEquiv _ _).symm.injective
  simp only [homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [rightAdjointUniq_hom_app_counit, ofNatIsoLeft_counit]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  erw [e'.inv.naturality_assoc, h₁, h₂]
  erw [i₂.hom.naturality_assoc]
  simp only [Functor.comp_map, ← P.map_comp]
  rw [rightAdjointUniq_hom_app_counit, ofNatIsoLeft_counit]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, P.map_comp]
  have hp : e'.inv.app (Q.obj (R₁.obj X)) ≫ i₁.hom.app (R₁.obj X) =
      i₂.hom.app (R₁.obj X) ≫ P.map (e.inv.app (R₁.obj X)) := by
    apply (cancel_mono (P.map (e.hom.app (R₁.obj X)))).1
    simp only [Category.assoc, ← P.map_comp, e.inv_hom_id_app, P.map_id]
    rw [he, Iso.inv_hom_id_app_assoc]
    exact (Category.comp_id _).symm
  exact (reassoc_of% hp) (P.map (a₁.counit.app X))

end CategoryTheory.Adjunction
