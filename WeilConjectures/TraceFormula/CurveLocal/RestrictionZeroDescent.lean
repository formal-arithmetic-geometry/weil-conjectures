/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CurveLocal.RestrictionZeroChain
public import WeilConjectures.TraceFormula.CurveLocal.RestrictionZeroTraceDescent

/-!

# Descent of the punctured restriction along a cover with a trace

Let `π : T' ⟶ T` be a morphism of schemes, `w : W ⟶ T` and `w' : W' ⟶ T'` closed immersions with
`π⁻¹(T ∖ W) ⊇ T' ∖ W'`, and let `ψ : U ⟶ T ∖ W`, `ψ' : U' ⟶ T' ∖ W'` be morphisms (in the
blueprint, the punctured diagonals `B ∖ y` and `B' ∖ y'`) with a morphism `π_U : U' ⟶ U` over
`π`. Suppose that the restriction along `π_U` has a trace: a map `t` with `π_U^* ≫ t = d • 𝟙`,
`d` invertible in `Λ` (in the blueprint, `π_U` is finite étale of degree `d²`, prime to `ℓ`).
If the upstairs restriction `RΓ(T' ∖ W', π^* P) ⟶ RΓ(U', ψ'^* π^* P)` vanishes, so does the
downstairs restriction `RΓ(T ∖ W, P) ⟶ RΓ(U, ψ^* P)`
(`AlgebraicGeometry.Etale.sectionsRestriction_app_eq_zero_of_trace`, blueprint
`det-tf-restriction-zero-trace-descent`): the two restrictions form a commutative square with the
pullbacks along `π` and `π_U`, since both composites are the restriction along `U' ⟶ T`, so
`d` times the downstairs restriction factors through the upstairs one.

-/

@[expose] public section

universe u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]
  {T T' W W' U U' : Scheme.{u}} (π : T' ⟶ T) (w : W ⟶ T) [IsClosedImmersion w]
  (w' : W' ⟶ T') [IsClosedImmersion w'] (hw : w'.openComplement ≤ π ⁻¹ᵁ w.openComplement)
  (ψ : U ⟶ w.openComplement.toScheme) (ψ' : U' ⟶ w'.openComplement.toScheme) (πU : U' ⟶ U)
  (hπ : πU ≫ ψ ≫ w.openComplement.ι = ψ' ≫ w'.openComplement.ι ≫ π)

include hw hπ in
/-- **Descent of the vanishing along a cover with a trace** (blueprint
`det-tf-restriction-zero-trace-descent`): if the restriction along `π_U : U' ⟶ U` admits a trace
`t` with `π_U^* ≫ t = d • 𝟙`, `d` invertible in `Λ`, and the upstairs restriction
`RΓ(T' ∖ W', π^* P) ⟶ RΓ(U', ψ'^* π^* P)` vanishes, then the downstairs restriction
`RΓ(T ∖ W, P) ⟶ RΓ(U, ψ^* P)` vanishes. -/
theorem sectionsRestriction_app_eq_zero_of_trace
    (P : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) {d : ℤ}
    (hd : IsUnit (d : Λ))
    (ht : ∃ t, (sectionsRestriction _ πU (V := Scheme.Etale.mk (𝟙 U))
      (W := Scheme.Etale.mk (𝟙 U')) πU rfl).app
        ((ψ ≫ w.openComplement.ι)^*[ModuleCat.{u + 1} Λ].mapDerivedCategory.obj P) ≫ t = d • 𝟙 _)
    (hup : (sectionsRestriction _ (ψ' ≫ w'.openComplement.ι)
      (V := Scheme.Etale.mk w'.openComplement.ι) (W := Scheme.Etale.mk (𝟙 _)) ψ'
      (Category.id_comp _).symm).app ((π)^*[ModuleCat.{u + 1} Λ].mapDerivedCategory.obj P) = 0) :
    (sectionsRestriction _ (ψ ≫ w.openComplement.ι) (V := Scheme.Etale.mk w.openComplement.ι)
      (W := Scheme.Etale.mk (𝟙 _)) ψ (Category.id_comp _).symm).app P = 0 := by
  obtain ⟨t, ht⟩ := ht
  -- the composite of the downstairs restriction and the pullback along `π_U` vanishes
  have h₁ : (sectionsRestriction _ (ψ ≫ w.openComplement.ι)
      (V := Scheme.Etale.mk w.openComplement.ι) (W := Scheme.Etale.mk (𝟙 _)) ψ
      (Category.id_comp _).symm).app P ≫
      (sectionsRestriction _ πU (V := Scheme.Etale.mk (𝟙 U))
        (W := Scheme.Etale.mk (𝟙 U')) πU rfl).app
          ((ψ ≫ w.openComplement.ι)^*[ModuleCat.{u + 1} Λ].mapDerivedCategory.obj P) = 0 := by
    refine (sectionsRestriction_comp_app_eq_zero_iff _ _ _ _ _ _ _ P).2 ?_
    have h₂ := (sectionsRestriction_comp_app_eq_zero_iff _ π (ψ' ≫ w'.openComplement.ι)
      (V := Scheme.Etale.mk w.openComplement.ι) (W := Scheme.Etale.mk w'.openComplement.ι)
      (W'' := Scheme.Etale.mk (𝟙 _)) (Scheme.Hom.resLE π w.openComplement w'.openComplement hw)
      (Scheme.Hom.resLE_comp_ι _ _) ψ' (Category.id_comp _).symm P).1
      (by rw [hup, comp_zero])
    refine (sectionsRestriction_app_eq_zero_iff_of_eq _ ?_ ?_ _ _ _).1 h₂
    · simpa only [assoc] using hπ.symm
    · change ψ' ≫ Scheme.Hom.resLE π w.openComplement w'.openComplement hw = πU ≫ ψ
      rw [← cancel_mono w.openComplement.ι]
      simpa only [assoc, Scheme.Hom.resLE_comp_ι] using hπ.symm
  exact DerivedCategory.eq_zero_of_comp_trace_of_isUnit (p₁ := 𝟙 _) (r' := 0)
    (by rw [h₁, comp_zero]) ht hd rfl

end AlgebraicGeometry.Etale
