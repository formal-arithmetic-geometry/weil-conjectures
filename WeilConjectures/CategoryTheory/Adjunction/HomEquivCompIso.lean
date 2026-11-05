/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Adjoints of morphisms between images of a cocone of functors

Consider functors `T : C ⥤ D`, `T' : C' ⥤ D`, `Φ : D ⥤ E`, `Ψ : C ⥤ E`, `Ψ' : C' ⥤ E`, with
isomorphisms `τ : T ⋙ Φ ≅ Ψ`, `τ' : T' ⋙ Φ ≅ Ψ'`, and adjunctions `T ⊣ R'`, `Ψ ⊣ R`. For a
morphism `g : T K ⟶ T' L`, the `Ψ ⊣ R`-adjoint of `τ⁻¹ ≫ Φ g ≫ τ' : Ψ K ⟶ Ψ' L` is the
`T ⊣ R'`-adjoint of `g` followed by a fixed map `R' (T' L) ⟶ R (Ψ' L)`
(`CategoryTheory.Adjunction.compIsoTransfer`,
`CategoryTheory.Adjunction.homEquiv_inv_app_comp_map_comp_hom_app`). Consequently, a morphism
`f : Ψ K ⟶ Ψ' L` is of the form `τ⁻¹ ≫ Φ g ≫ τ'` as soon as its adjoint factors through this
fixed map (`CategoryTheory.Adjunction.eq_inv_app_comp_map_comp_hom_app`).

When all the functors are induced, through comparison morphisms, by functors between other
categories (e.g. derived functors induced by functors on homotopy categories), the fixed map is
computed by the corresponding fixed map of the underlying functors
(`CategoryTheory.Adjunction.compIsoTransfer_comparison`).
-/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {C C' D E : Type*} [Category C] [Category C'] [Category D] [Category E]
  {T : C ⥤ D} {T' : C' ⥤ D} {Φ : D ⥤ E} {Ψ : C ⥤ E} {Ψ' : C' ⥤ E} {R' : D ⥤ C} {R : E ⥤ C}

end CategoryTheory.Adjunction
