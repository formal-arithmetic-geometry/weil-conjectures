/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.ExchangeOnProper

/-!

# Compact-support exchanges along a refinement of compactifications

Let `ν_C = χ_P⁻¹ ∘ R'_{P*}(ν_ι)` be the compact-support exchange of a compactification `ι : N ⊆ P`
(blueprint `det-nearby-exchange-maps` (3); `ν_ι` the adjoint of the inverse of the pullback
exchange `α_ι`, `χ_P` the proper exchange). This file proves, in abstract categories, the two
formal steps showing that `ν_C` is unchanged along a refinement `π : P₃ ⟶ P₁` (with
`ι₁ = ι₃ ≫ π`):

* `ProEtale.CondensedRing.lowerShriekExchangeOfInv_comp_pushforwardExchange_aux`: the composition
  law of the pullback exchanges and the description of the base change map
  `E : ι₁! ⟶ Rπ_* ι₃!` by its adjoint give
  `χ_π(ι₃! K) ∘ Ψ_{P₁}(E_K) ∘ ν_{ι₁}(K) = Rπ'_*(ν_{ι₃}(K)) ∘ E'_{Ψ_N K}`;
* `ProEtale.CondensedRing.compactSupportExchange_comp_eq_aux`: with the composition law of the
  proper exchanges, this identity gives `χ₃⁻¹ ∘ R₃'(ν_{ι₃}) = χ₁⁻¹ ∘ R₁'(ν_{ι₁})` through `E`.

-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

section Abstract

variable {DN DN' D₁ D₁' D₃ D₃' Ds Ds' : Type*} [Category DN] [Category DN'] [Category D₁]
  [Category D₁'] [Category D₃] [Category D₃'] [Category Ds] [Category Ds']

/-- **The refinement step for compact-support exchanges**, in abstract categories: let
`ν₁ : Ψ_N ⋙ Dh₁' ⟶ Dh₁ ⋙ Ψ₁` and `ν₃ : Ψ_N ⋙ Dh₃' ⟶ Dh₃ ⋙ Ψ₃` be exchanges for two "open"
functors, related by isomorphisms `E : Dh₁ ≅ Dh₃ ⋙ Rπ`, `E' : Dh₁' ≅ Dh₃' ⋙ Rπ'` through an exchange
`χπ : Rπ ⋙ Ψ₁ ⟶ Ψ₃ ⋙ Rπ'` (`hE`), and let the exchanges `χ₁`, `χ₃` of the "proper" functors
`R₁` and `R₃ ≅ Rπ ⋙ R₁` satisfy the composition law `hχ`. If `χ₃` is invertible at `Dh₃ K`, then
`χ₃⁻¹ ∘ R₃'(ν₃)` and `χ₁⁻¹ ∘ R₁'(ν₁)` agree at `K` up to `E`, `E'`, `conj` and `conj'`, for right
inverses `χ₁inv` and `χ₃inv` of `χ₁` and `χ₃`. -/
lemma compactSupportExchange_comp_eq_aux {ΨN : DN ⥤ DN'} {Ψ₁ : D₁ ⥤ D₁'} {Ψ₃ : D₃ ⥤ D₃'}
    {Ψs : Ds ⥤ Ds'} {Dh₁ : DN ⥤ D₁} {Dh₁' : DN' ⥤ D₁'} {Dh₃ : DN ⥤ D₃} {Dh₃' : DN' ⥤ D₃'}
    {Rπ : D₃ ⥤ D₁} {Rπ' : D₃' ⥤ D₁'} {R₁ : D₁ ⥤ Ds} {R₁' : D₁' ⥤ Ds'} {R₃ : D₃ ⥤ Ds}
    {R₃' : D₃' ⥤ Ds'} (conj : R₃ ≅ Rπ ⋙ R₁) (conj' : R₃' ≅ Rπ' ⋙ R₁')
    (χπ : Rπ ⋙ Ψ₁ ⟶ Ψ₃ ⋙ Rπ') (χ₁ : R₁ ⋙ Ψs ⟶ Ψ₁ ⋙ R₁') (χ₃ : R₃ ⋙ Ψs ⟶ Ψ₃ ⋙ R₃')
    (hχ : ∀ A, χ₃.app A = Ψs.map (conj.hom.app A) ≫ χ₁.app (Rπ.obj A) ≫
      R₁'.map (χπ.app A) ≫ conj'.inv.app (Ψ₃.obj A))
    (E : Dh₁ ≅ Dh₃ ⋙ Rπ) (E' : Dh₁' ≅ Dh₃' ⋙ Rπ') (ν₁ : ΨN ⋙ Dh₁' ⟶ Dh₁ ⋙ Ψ₁)
    (ν₃ : ΨN ⋙ Dh₃' ⟶ Dh₃ ⋙ Ψ₃) (K : DN)
    (hE : ν₁.app K ≫ Ψ₁.map (E.hom.app K) ≫ χπ.app (Dh₃.obj K) =
      E'.hom.app (ΨN.obj K) ≫ Rπ'.map (ν₃.app K))
    [IsIso (χ₃.app (Dh₃.obj K))]
    (χ₁inv : R₁'.obj (Ψ₁.obj (Dh₁.obj K)) ⟶ Ψs.obj (R₁.obj (Dh₁.obj K)))
    (hχ₁ : χ₁inv ≫ χ₁.app (Dh₁.obj K) = 𝟙 _)
    (χ₃inv : R₃'.obj (Ψ₃.obj (Dh₃.obj K)) ⟶ Ψs.obj (R₃.obj (Dh₃.obj K)))
    (hχ₃ : χ₃inv ≫ χ₃.app (Dh₃.obj K) = 𝟙 _) :
    R₁'.map (E'.hom.app (ΨN.obj K)) ≫ conj'.inv.app (Dh₃'.obj (ΨN.obj K)) ≫
        R₃'.map (ν₃.app K) ≫ χ₃inv =
      R₁'.map (ν₁.app K) ≫ χ₁inv ≫
        Ψs.map (R₁.map (E.hom.app K) ≫ conj.inv.app (Dh₃.obj K)) := by
  obtain rfl : χ₃inv = inv (χ₃.app (Dh₃.obj K)) := IsIso.eq_inv_of_inv_hom_id hχ₃
  rw [← cancel_mono (χ₃.app (Dh₃.obj K)), Category.assoc, Category.assoc, Category.assoc,
    IsIso.inv_hom_id, Category.comp_id, hχ]
  have nχ := χ₁.naturality (E.hom.app K)
  have nconj := conj'.inv.naturality (ν₃.app K)
  simp only [Functor.comp_obj, Functor.comp_map] at nχ nconj
  simp only [Functor.map_comp, Category.assoc]
  rw [← Ψs.map_comp_assoc (conj.inv.app _), Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, reassoc_of% nχ, reassoc_of% hχ₁, ← R₁'.map_comp_assoc,
    ← R₁'.map_comp_assoc, Category.assoc, hE, R₁'.map_comp, Category.assoc, ← nconj]


/-- **The identity `(*)` of the refinement step**, in abstract categories: let `Dh₁ ⊣ Lh₁`,
`Dh₃ ⊣ Lh₃` (and their primed versions) be the open adjunctions of `ι₁ = ι₃ ≫ p` and `ι₃`,
`Lπ ⊣ Rπ` (and `Lπ' ⊣ Rπ'`) the adjunctions of `p`, with pullback exchanges `α₁`, `α₃`, `απ`
satisfying the composition law `hα` through the comparisons `c : Lh₁ ≅ Lπ ⋙ Lh₃`,
`c' : Lh₁' ≅ Lπ' ⋙ Lh₃'`, and `χπ` the mate of `απ` (`hχπ`). If `E : Dh₁ ⟶ Dh₃ ⋙ Rπ` is the
base change map, characterized by its adjoint `E♭ : Lπ Dh₁ ⟶ Dh₃` (`hE`: the `Lh₃`-adjoint of
`E♭` is the unit of `ι₁` read through `c`), and similarly for `E'` with `E'♭` invertible, then
`χπ(ι₃! K) ∘ Ψ₁(E_K) ∘ ν₁(K) = Rπ'(ν₃(K)) ∘ E'_{Ψ_N K}` for the mates `ν₁`, `ν₃` of `α₁⁻¹`,
`α₃⁻¹`. -/
lemma lowerShriekExchangeOfInv_comp_pushforwardExchange_aux {ΨN : DN ⥤ DN'} {Ψ₁ : D₁ ⥤ D₁'}
    {Ψ₃ : D₃ ⥤ D₃'} {Dh₁ : DN ⥤ D₁} {Lh₁ : D₁ ⥤ DN} {Dh₃ : DN ⥤ D₃} {Lh₃ : D₃ ⥤ DN}
    {Dh₁' : DN' ⥤ D₁'} {Lh₁' : D₁' ⥤ DN'} {Dh₃' : DN' ⥤ D₃'} {Lh₃' : D₃' ⥤ DN'}
    (adj₁ : Dh₁ ⊣ Lh₁) (adj₃ : Dh₃ ⊣ Lh₃) (adj₁' : Dh₁' ⊣ Lh₁') (adj₃' : Dh₃' ⊣ Lh₃')
    {Lπ : D₁ ⥤ D₃} {Rπ : D₃ ⥤ D₁} (adjπ : Lπ ⊣ Rπ) {Lπ' : D₁' ⥤ D₃'} {Rπ' : D₃' ⥤ D₁'}
    (adjπ' : Lπ' ⊣ Rπ') (α₁ : Ψ₁ ⋙ Lh₁' ⟶ Lh₁ ⋙ ΨN) [IsIso α₁] (α₃ : Ψ₃ ⋙ Lh₃' ⟶ Lh₃ ⋙ ΨN)
    [IsIso α₃] (απ : Ψ₁ ⋙ Lπ' ⟶ Lπ ⋙ Ψ₃) (χπ : Rπ ⋙ Ψ₁ ⟶ Ψ₃ ⋙ Rπ')
    (hχπ : ∀ A, Lπ'.map (χπ.app A) ≫ adjπ'.counit.app (Ψ₃.obj A) =
      απ.app (Rπ.obj A) ≫ Ψ₃.map (adjπ.counit.app A))
    (c : Lh₁ ≅ Lπ ⋙ Lh₃) (c' : Lh₁' ≅ Lπ' ⋙ Lh₃')
    (hα : ∀ A, α₁.app A = c'.hom.app (Ψ₁.obj A) ≫ Lh₃'.map (απ.app A) ≫ α₃.app (Lπ.obj A) ≫
      ΨN.map (c.inv.app A))
    (E : Dh₁ ⟶ Dh₃ ⋙ Rπ) (E' : Dh₁' ⟶ Dh₃' ⋙ Rπ') (K : DN)
    (hE : adj₁.unit.app K ≫ c.hom.app (Dh₁.obj K) ≫
      Lh₃.map (Lπ.map (E.app K) ≫ adjπ.counit.app (Dh₃.obj K)) = adj₃.unit.app K)
    (hE' : adj₁'.unit.app (ΨN.obj K) ≫ c'.hom.app (Dh₁'.obj (ΨN.obj K)) ≫
      Lh₃'.map (Lπ'.map (E'.app (ΨN.obj K)) ≫ adjπ'.counit.app (Dh₃'.obj (ΨN.obj K))) =
        adj₃'.unit.app (ΨN.obj K))
    [IsIso (Lπ'.map (E'.app (ΨN.obj K)) ≫ adjπ'.counit.app (Dh₃'.obj (ΨN.obj K)))] :
    (lowerShriekExchangeOfInv adj₁ adj₁' α₁).app K ≫ Ψ₁.map (E.app K) ≫ χπ.app (Dh₃.obj K) =
      E'.app (ΨN.obj K) ≫ Rπ'.map ((lowerShriekExchangeOfInv adj₃ adj₃' α₃).app K) := by
  apply (adjπ'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have h1 := απ.naturality (E.app K)
  have h2 := adjπ'.counit.naturality ((lowerShriekExchangeOfInv adj₃ adj₃' α₃).app K)
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj] at h1 h2
  rw [hχπ, reassoc_of% h1, h2, ← Ψ₃.map_comp]
  -- the source is identified with `Dh₃' Ψ_N K` by `E'♭`
  rw [← cancel_epi (inv (Lπ'.map (E'.app (ΨN.obj K)) ≫ adjπ'.counit.app (Dh₃'.obj (ΨN.obj K))))]
  conv_rhs => rw [← Category.assoc (Lπ'.map _), IsIso.inv_hom_id_assoc]
  apply (adj₃'.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  have h3 : adj₃'.unit.app (ΨN.obj K) ≫
      Lh₃'.map (inv (Lπ'.map (E'.app (ΨN.obj K)) ≫ adjπ'.counit.app (Dh₃'.obj (ΨN.obj K)))) =
        adj₁'.unit.app (ΨN.obj K) ≫ c'.hom.app (Dh₁'.obj (ΨN.obj K)) := by
    rw [← hE', Category.assoc, Category.assoc, ← Functor.map_comp, IsIso.hom_inv_id]
    simp
  have h4 := c'.hom.naturality ((lowerShriekExchangeOfInv adj₁ adj₁' α₁).app K)
  have h5 : c'.hom.app (Ψ₁.obj (Dh₁.obj K)) ≫ Lh₃'.map (απ.app (Dh₁.obj K)) =
      α₁.app (Dh₁.obj K) ≫ ΨN.map (c.hom.app (Dh₁.obj K)) ≫
        (inv α₃).app (Lπ.obj (Dh₁.obj K)) := by
    rw [hα]
    simp [← ΨN.map_comp_assoc]
  have h6 := (inv α₃).naturality (Lπ.map (E.app K) ≫ adjπ.counit.app (Dh₃.obj K))
  simp only [Functor.comp_map, Functor.comp_obj] at h4 h6
  rw [unit_comp_lowerShriekExchangeOfInv_app, Functor.map_comp, reassoc_of% h3, Functor.map_comp,
    Functor.map_comp, ← reassoc_of% h4, reassoc_of% (unit_comp_lowerShriekExchangeOfInv_app adj₁
    adj₁' α₁ K), reassoc_of% h5, NatIso.isIso_inv_app α₁, IsIso.inv_hom_id_assoc, ← h6,
    ← ΨN.map_comp_assoc, ← ΨN.map_comp_assoc, Category.assoc, hE]
  rfl

end Abstract

end AlgebraicGeometry.ProEtale.CondensedRing
