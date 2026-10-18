/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.ProperPushforwardKernel
public import WeilConjectures.TraceFormula.TraceClassAdditivity

/-!

# The Lefschetz–Verdier formula

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

variable {P X C : Type*} [Category* P] [Category* X] [Category* C]

/-- The unit of a composite adjunction through the conjugate of a composition isomorphism
`σ : L_g ≅ L_f ⋙ L_c`: with `λ : R_c ⋙ R_f ≅ R_g` the conjugate of `σ`,
`R_f η_c ≫ λ = η_g ≫ R_g (σ ≫ L_c ε_f)`. -/
lemma map_unit_comp_conjugateIsoEquiv_inv_app {Lf : P ⥤ X} {Rf : X ⥤ P} {Lc : X ⥤ C}
    {Rc : C ⥤ X} {Lg : P ⥤ C} {Rg : C ⥤ P} (adjf : Lf ⊣ Rf) (adjc : Lc ⊣ Rc) (adjg : Lg ⊣ Rg)
    (σ : Lg ≅ Lf ⋙ Lc) (K : X) :
    Rf.map (adjc.unit.app K) ≫
        (conjugateIsoEquiv adjg (adjf.comp adjc) σ.symm).inv.app (Lc.obj K) =
      adjg.unit.app (Rf.obj K) ≫ Rg.map (σ.hom.app (Rf.obj K) ≫ Lc.map (adjf.counit.app K)) := by
  simp only [conjugateIsoEquiv_apply_inv, Iso.symm_inv, conjugateEquiv_apply_app,
    Adjunction.comp_counit_app, Functor.comp_obj, Functor.comp_map, Category.assoc]
  sorry

/-- For an adjunction `L ⊣ R` with `Λ : L ≅ 𝟭`, the unit followed by the conjugate
`R ≅ 𝟭` of `Λ` is `Λ⁻¹`. -/
lemma unit_map_comp_conjugateIsoEquiv_hom_app {L R : P ⥤ P} (adj : L ⊣ R) (Λ : L ≅ 𝟭 P)
    {Z Y : P} (φ : L.obj Z ⟶ Y) :
    adj.unit.app Z ≫ R.map φ ≫ (conjugateIsoEquiv adj Adjunction.id Λ.symm).hom.app Y =
      Λ.inv.app Z ≫ φ := by
  simp only [conjugateIsoEquiv_apply_hom, Iso.symm_hom, conjugateEquiv_apply_app]
  sorry

end CategoryTheory
