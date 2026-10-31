/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalIso
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidalComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.NonFlatPullFacGeneric

/-!
# The transitivity of the derived extensions of scalars and the monoidal units

For morphisms `φ : R ⟶ S`, `ψ : S ⟶ T` of commutative condensed ring objects on `X_proét` with
`φ ≫ ψ = χ`, the transitivity isomorphism `L(Ext_χ) ≅ L(Ext_φ) ⋙ L(Ext_ψ)`
(`Mod.derivedExtendScalarsCompIso`, the conjugate of the composition of the restrictions of
scalars) is compatible with the unit comparisons of the monoidal functors
`Functor.leftDerivedFunctorMonoidal` (`ProEtale.CondensedRing.map_ε_comp_derivedExtendScalarsCompIso_inv_app_comp_η`).
No flatness is needed: through the counits of the left derived functors, both sides are computed
on the unit complex by the underived transitivity isomorphism, which is monoidal
(`Mod.isMonoidal_extendScalarsComp_hom`).

This is the condensed part of the compatibility of the reduction `𝒪_E ⧸ ℓⁿ⁺¹ ⟶ 𝒪_E ⧸ ℓⁿ` with the
identifications of the reductions of the unit (blueprint `det-sp-purity-coefficient-change`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable {X : Scheme.{u}} {R S T : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
  [MonObj S] [MonObj T] [IsCommMonObj R] [IsCommMonObj S] [IsCommMonObj T]
  (φ : R ⟶ S) [IsMonHom φ] (ψ : S ⟶ T) [IsMonHom ψ] (χ : R ⟶ T) [IsMonHom χ]

set_option maxHeartbeats 1000000 in
-- the monoidal structures of the derived functors on sheaf categories are slow to unfold
/-- **The transitivity of the derived extensions of scalars preserves the units**: for
`φ ≫ ψ = χ`, `L(Ext_ψ)(𝟙 ≅ L(Ext_φ) 𝟙)`, followed by the transitivity isomorphism and the unit
comparison `L(Ext_χ) 𝟙 ≅ 𝟙`, is the unit comparison of `L(Ext_ψ)`. -/
lemma map_ε_comp_derivedExtendScalarsCompIso_inv_app_comp_η (h : φ ≫ ψ = χ) :
    letI := Mod.extendScalarsMonoidal φ
    letI := Mod.extendScalarsMonoidal ψ
    letI := Mod.extendScalarsMonoidal χ
    letI := (Mod.extendScalars φ).leftDerivedFunctorMonoidal
    letI := (Mod.extendScalars ψ).leftDerivedFunctorMonoidal
    letI := (Mod.extendScalars χ).leftDerivedFunctorMonoidal
    (Mod.extendScalars ψ).leftDerivedFunctor.map (ε (Mod.extendScalars φ).leftDerivedFunctor) ≫
        (Mod.derivedExtendScalarsCompIso φ ψ χ h).inv.app (𝟙_ _) ≫
          η (Mod.extendScalars χ).leftDerivedFunctor =
      η (Mod.extendScalars ψ).leftDerivedFunctor := by
  subst h
  let := Mod.extendScalarsMonoidal φ
  let := Mod.extendScalarsMonoidal ψ
  let := Mod.extendScalarsMonoidal (φ ≫ ψ)
  let := (Mod.extendScalars φ).leftDerivedFunctorMonoidal
  let := (Mod.extendScalars ψ).leftDerivedFunctorMonoidal
  let := (Mod.extendScalars (φ ≫ ψ)).leftDerivedFunctorMonoidal
  have := DerivedCategory.isIso_ε_Qh (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) T)
  have := DerivedCategory.isIso_ε_Qh (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S)
  -- the underived transitivity isomorphism preserves the units
  have := Mod.isMonoidal_extendScalarsComp_hom φ ψ
  have hτ := Functor.natTransMapHomotopyCategory_app_unit_comp_η
    (Mod.extendScalarsComp φ ψ).inv
  rw [← Functor.mapHomotopyCategory_map_η_comp_η] at hτ
  -- the unit comparison of `L(Ext_φ)` through the counit
  have hηφ := Functor.leftDerivedFunctorMonoidal_η (Mod.extendScalars φ)
  have hc := Mod.derivedExtendScalarsCompIso_inv_app_Qh_comp_counit φ ψ (𝟙_ _)
  have hn := (Mod.derivedExtendScalarsCompIso φ ψ (φ ≫ ψ) rfl).inv.naturality (ε DerivedCategory.Qh)
  have hk := (Mod.extendScalars ψ).leftDerivedFunctorCounit.naturality
    (η ((Mod.extendScalars φ).mapHomotopyCategory (.up ℤ)))
  simp only [Functor.comp_obj, Functor.comp_map] at hn hk
  have hε : ε (Mod.extendScalars φ).leftDerivedFunctor ≫
      (Mod.extendScalars φ).leftDerivedFunctor.map (ε DerivedCategory.Qh) ≫
        (Mod.extendScalars φ).leftDerivedFunctorCounit.app (𝟙_ _) ≫
          DerivedCategory.Qh.map (η ((Mod.extendScalars φ).mapHomotopyCategory (.up ℤ))) =
      ε DerivedCategory.Qh := by
    rw [← hηφ, Functor.Monoidal.ε_η_assoc]
  rw [← cancel_mono (ε DerivedCategory.Qh), Category.assoc, Category.assoc,
    Functor.leftDerivedFunctorMonoidal_η, Functor.leftDerivedFunctorMonoidal_η, ← reassoc_of% hn,
    reassoc_of% hc, ← Functor.map_comp]
  erw [hτ]
  rw [Functor.map_comp, ← reassoc_of% hk, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
    ← Functor.map_comp_assoc]
  simp only [Category.assoc, hε]

end AlgebraicGeometry.ProEtale.CondensedRing
