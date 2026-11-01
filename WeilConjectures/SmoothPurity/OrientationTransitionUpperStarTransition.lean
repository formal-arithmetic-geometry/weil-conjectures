/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionPullUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionProperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ComapUpperStarIsoComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingReduction

/-!
# The condensed transition commutes with the derived pullbacks: the generic argument

For adjunctions `E_a ⊣ R_a`, `E_b ⊣ R_b`, `E_c ⊣ R_c` on two sides `Y` and `X`, with the
transitivity isomorphisms `ε : E_c ≅ E_a ⋙ E_b` conjugate to isomorphisms `κ : R_b ⋙ R_a ≅ R_c`,
functors `F` (pullbacks) commuting with the right adjoints (`s`) and with the left adjoints (`P`),
`P` being transposed to `s` along the units, the transitions `η^b ≫ R_b(ε⁻¹)` commute with the
pullbacks (`CategoryTheory.map_unit_app_comp_map_inv_app_comp_eq`), provided the commutations
`s` are compatible with `κ`.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

/-- For the transitivity isomorphism `ε : E_c ≅ E_a ⋙ E_b` conjugate to `κ : R_b ⋙ R_a ≅ R_c`,
the units are related by `η^a ≫ R_a(η^b) ≫ R_a R_b(ε⁻¹) = η^c ≫ κ⁻¹`. -/
lemma unit_app_comp_map_unit_app_comp_map_conjugateIsoEquiv_symm_inv_app {C₀ C₁ C₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂] {Ea : C₀ ⥤ C₁} {Ra : C₁ ⥤ C₀} {Eb : C₁ ⥤ C₂}
    {Rb : C₂ ⥤ C₁} {Ec : C₀ ⥤ C₂} {Rc : C₂ ⥤ C₀} (adja : Ea ⊣ Ra) (adjb : Eb ⊣ Rb)
    (adjc : Ec ⊣ Rc) (κ : Rb ⋙ Ra ≅ Rc) (c : C₀) :
    adja.unit.app c ≫ Ra.map (adjb.unit.app (Ea.obj c)) ≫
        Ra.map (Rb.map (((conjugateIsoEquiv (adja.comp adjb) adjc).symm κ).inv.app c)) =
      adjc.unit.app c ≫ κ.inv.app (Ec.obj c) := by
  set ε := (conjugateIsoEquiv (adja.comp adjb) adjc).symm κ
  have h := unit_conjugateEquiv (adja.comp adjb) adjc ε.hom c
  rw [← conjugateIsoEquiv_apply_hom, Equiv.apply_symm_apply, Adjunction.comp_unit_app] at h
  have hn := κ.inv.naturality (ε.hom.app c)
  simp only [Functor.comp_map, Functor.comp_obj] at h hn
  rw [← cancel_mono (Ra.map (Rb.map (ε.hom.app c)))]
  simp only [assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  rw [← hn, ← reassoc_of% h, Iso.hom_inv_id_app]
  simp

/-- **The transitions commute with the pullbacks, generically.** See the module docstring. -/
lemma map_unit_app_comp_map_inv_app_comp_eq {DY₀ DY₁ DY₂ DX₀ DX₁ DX₂ : Type*}
    [Category DY₀] [Category DY₁] [Category DY₂] [Category DX₀] [Category DX₁] [Category DX₂]
    {EaY : DY₀ ⥤ DY₁} {RaY : DY₁ ⥤ DY₀} {EbY : DY₁ ⥤ DY₂} {RbY : DY₂ ⥤ DY₁}
    {EcY : DY₀ ⥤ DY₂} {RcY : DY₂ ⥤ DY₀}
    {EaX : DX₀ ⥤ DX₁} {RaX : DX₁ ⥤ DX₀} {EbX : DX₁ ⥤ DX₂} {RbX : DX₂ ⥤ DX₁}
    {EcX : DX₀ ⥤ DX₂} {RcX : DX₂ ⥤ DX₀}
    {adjaY : EaY ⊣ RaY} {adjbY : EbY ⊣ RbY} {adjcY : EcY ⊣ RcY}
    {adjaX : EaX ⊣ RaX} {adjbX : EbX ⊣ RbX} {adjcX : EcX ⊣ RcX}
    {F₀ : DY₀ ⥤ DX₀} {F₁ : DY₁ ⥤ DX₁} {F₂ : DY₂ ⥤ DX₂}
    {sa : RaY ⋙ F₀ ≅ F₁ ⋙ RaX} {sb : RbY ⋙ F₁ ≅ F₂ ⋙ RbX} {sc : RcY ⋙ F₀ ≅ F₂ ⋙ RcX}
    {Pa : F₀ ⋙ EaX ≅ EaY ⋙ F₁} {Pc : F₀ ⋙ EcX ≅ EcY ⋙ F₂}
    {κY : RbY ⋙ RaY ≅ RcY} {κX : RbX ⋙ RaX ≅ RcX}
    {εY : EcY ≅ EaY ⋙ EbY} {εX : EcX ≅ EaX ⋙ EbX}
    (hεY : εY = (conjugateIsoEquiv (adjaY.comp adjbY) adjcY).symm κY)
    (hεX : εX = (conjugateIsoEquiv (adjaX.comp adjbX) adjcX).symm κX)
    (ha : ∀ M, F₀.map (adjaY.unit.app M) ≫ sa.hom.app (EaY.obj M) =
      adjaX.unit.app (F₀.obj M) ≫ RaX.map (Pa.hom.app M))
    (hc : ∀ M, F₀.map (adjcY.unit.app M) ≫ sc.hom.app (EcY.obj M) =
      adjcX.unit.app (F₀.obj M) ≫ RcX.map (Pc.hom.app M))
    (hs : ∀ N, F₀.map (κY.inv.app N) ≫ sa.hom.app (RbY.obj N) ≫ RaX.map (sb.hom.app N) =
      sc.hom.app N ≫ κX.inv.app (F₂.obj N))
    (A : DY₀) :
    F₁.map (adjbY.unit.app (EaY.obj A) ≫ RbY.map (εY.inv.app A)) ≫ sb.hom.app (EcY.obj A) ≫
        RbX.map (Pc.inv.app A) =
      Pa.inv.app A ≫ adjbX.unit.app (EaX.obj (F₀.obj A)) ≫ RbX.map (εX.inv.app (F₀.obj A)) := by
  subst hεY hεX
  rw [← cancel_epi (Pa.hom.app A), Iso.hom_inv_id_app_assoc]
  apply (adjaX.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [unit_app_comp_map_unit_app_comp_map_conjugateIsoEquiv_symm_inv_app, ← reassoc_of% (ha A)]
  have hn := sa.hom.naturality (adjbY.unit.app (EaY.obj A) ≫
    RbY.map (((conjugateIsoEquiv (adjaY.comp adjbY) adjcY).symm κY).inv.app A))
  simp only [Functor.comp_map, Functor.map_comp, assoc] at hn
  simp only [assoc]
  rw [← reassoc_of% hn, ← F₀.map_comp_assoc, ← F₀.map_comp_assoc, assoc,
    unit_app_comp_map_unit_app_comp_map_conjugateIsoEquiv_symm_inv_app, F₀.map_comp_assoc,
    reassoc_of% (hs (EcY.obj A)), reassoc_of% (hc A)]
  have hκ := κX.inv.naturality (Pc.hom.app A)
  simp only [Functor.comp_map] at hκ
  rw [reassoc_of% hκ, ← RaX.map_comp, ← RbX.map_comp, Iso.hom_inv_id_app]
  simp


/-- The variant of `CategoryTheory.map_unit_app_comp_map_inv_app_comp_eq` in the shape of the
reduction squares: the transitions `t` are given through their factorizations
(`htY`, `htX`) involving identities, and the pullbacks `w` of the reductions through
`Pc` and `Pa` (`hw₂`, `hw₁`), up to identities `v`. -/
lemma map_unit_app_comp_map_comp_eq {DY₀ DY₁ DY₂ DX₀ DX₁ DX₂ : Type*}
    [Category DY₀] [Category DY₁] [Category DY₂] [Category DX₀] [Category DX₁] [Category DX₂]
    {EaY : DY₀ ⥤ DY₁} {RaY : DY₁ ⥤ DY₀} {EbY : DY₁ ⥤ DY₂} {RbY : DY₂ ⥤ DY₁}
    {EcY : DY₀ ⥤ DY₂} {RcY : DY₂ ⥤ DY₀}
    {EaX : DX₀ ⥤ DX₁} {RaX : DX₁ ⥤ DX₀} {EbX : DX₁ ⥤ DX₂} {RbX : DX₂ ⥤ DX₁}
    {EcX : DX₀ ⥤ DX₂} {RcX : DX₂ ⥤ DX₀}
    {adjaY : EaY ⊣ RaY} {adjbY : EbY ⊣ RbY} {adjcY : EcY ⊣ RcY}
    {adjaX : EaX ⊣ RaX} {adjbX : EbX ⊣ RbX} {adjcX : EcX ⊣ RcX}
    {F₀ : DY₀ ⥤ DX₀} {F₁ : DY₁ ⥤ DX₁} {F₂ : DY₂ ⥤ DX₂}
    {sa : RaY ⋙ F₀ ≅ F₁ ⋙ RaX} {sb : RbY ⋙ F₁ ≅ F₂ ⋙ RbX} {sc : RcY ⋙ F₀ ≅ F₂ ⋙ RcX}
    {Pa : F₀ ⋙ EaX ≅ EaY ⋙ F₁} {Pc : F₀ ⋙ EcX ≅ EcY ⋙ F₂}
    {κY : RbY ⋙ RaY ≅ RcY} {κX : RbX ⋙ RaX ≅ RcX}
    {εY : EcY ≅ EaY ⋙ EbY} {εX : EcX ≅ EaX ⋙ EbX}
    (hεY : εY = (conjugateIsoEquiv (adjaY.comp adjbY) adjcY).symm κY)
    (hεX : εX = (conjugateIsoEquiv (adjaX.comp adjbX) adjcX).symm κX)
    (ha : ∀ M, F₀.map (adjaY.unit.app M) ≫ sa.hom.app (EaY.obj M) =
      adjaX.unit.app (F₀.obj M) ≫ RaX.map (Pa.hom.app M))
    (hc : ∀ M, F₀.map (adjcY.unit.app M) ≫ sc.hom.app (EcY.obj M) =
      adjcX.unit.app (F₀.obj M) ≫ RcX.map (Pc.hom.app M))
    (hs : ∀ N, F₀.map (κY.inv.app N) ≫ sa.hom.app (RbY.obj N) ≫ RaX.map (sb.hom.app N) =
      sc.hom.app N ≫ κX.inv.app (F₂.obj N))
    {A : DY₀} {tY : EbY.obj (EaY.obj A) ⟶ EcY.obj A}
    {tX : EbX.obj (EaX.obj (F₀.obj A)) ⟶ EcX.obj (F₀.obj A)}
    {u₁ : EaY.obj A ⟶ EaY.obj A} {u₂ : EcY.obj A ⟶ EcY.obj A}
    {u₁' : EaX.obj (F₀.obj A) ⟶ EaX.obj (F₀.obj A)} {u₂' : EcX.obj (F₀.obj A) ⟶ EcX.obj (F₀.obj A)}
    {v₁ : F₁.obj (EaY.obj A) ⟶ F₁.obj (EaY.obj A)} {v₂ : F₂.obj (EcY.obj A) ⟶ F₂.obj (EcY.obj A)}
    {w₁ : F₁.obj (EaY.obj A) ⟶ EaX.obj (F₀.obj A)} {w₂ : F₂.obj (EcY.obj A) ⟶ EcX.obj (F₀.obj A)}
    (htY : tY = EbY.map u₁ ≫ εY.inv.app A ≫ u₂)
    (htX : tX = EbX.map u₁' ≫ εX.inv.app (F₀.obj A) ≫ u₂')
    (hu₁ : u₁ = 𝟙 _) (hu₂ : u₂ = 𝟙 _) (hu₁' : u₁' = 𝟙 _) (hu₂' : u₂' = 𝟙 _) (hv₁ : v₁ = 𝟙 _)
    (hv₂ : v₂ = 𝟙 _) (hw₁ : w₁ = Pa.inv.app A) (hw₂ : w₂ = Pc.inv.app A) :
    F₁.map (adjbY.unit.app (EaY.obj A) ≫ RbY.map tY) ≫ sb.hom.app (EcY.obj A) ≫
        RbX.map (v₂ ≫ w₂) =
      v₁ ≫ w₁ ≫ adjbX.unit.app (EaX.obj (F₀.obj A)) ≫ RbX.map tX := by
  subst htY htX hu₁ hu₂ hu₁' hu₂' hv₁ hv₂ hw₁ hw₂
  simpa using map_unit_app_comp_map_inv_app_comp_eq hεY hεX ha hc hs A

end CategoryTheory
