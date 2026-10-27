/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.CompactSupportExchangeRefinement
public import WeilConjectures.TraceFormula.Specialization.OpenProperLowerShriek
public import WeilConjectures.TraceFormula.Specialization.TraitModelProperExchange
public import WeilConjectures.TraceFormula.Specialization.TraitModelRefinement

/-!

# The compact-support exchange of a trait model over the base

Let `N` be a trait model over the base of a separated `k`-scheme `Y` of finite type, with special
fibre `Y'`, over the strictly henselian trait `S = Spec k'⟦t⟧`. For a compactification `C` of `N`
(`NearbyCyclesModel.IsTraitModelOfBase.Compactification`: `N ⊆ P` open in a trait model over the
base with proper total space, over `ι : Y ⟶ X`, `ι' : Y' ⟶ X'`), the compact-support exchange of
the structure morphism `a : Y ⟶ Spec k` (blueprint `det-nearby-exchange-maps` (3)) is
```
ν_C = χ_{a_P}⁻¹ ∘ Ra'_{P*}(ν_ι) : Ra'_! Ψ_N ⟶ Ψ_S Ra_!
```
through `Ra_! ≅ ι_! ⋙ Ra_{P*}`, with `ν_ι` the adjoint of `α_ι⁻¹`
(`NearbyCyclesModel.IsTraitModelOfBase.Compactification.compactSupportExchange`, an instance of
`ProEtale.CondensedRing.compactSupportExchangeOfCompactification`).

## The refinement identity

The independence of `ν_C` from the compactification (blueprint `det-nearby-exchange-maps`) is
proved along a refinement `π : P₃ ⟶ P₁` over a proper `p : X₃ ⟶ X₁` with `ι₁ = ι₃ ≫ p` and `N`
cartesian over `P₁` (any two compactifications have a common refinement,
`NearbyCyclesModel.IsTraitModelOfBase.Compactification.exists_refinement`). Its key identity
```
χ_π(ι₃! K) ∘ Ψ_{P₁}(E_K) ∘ ν_{ι₁}(K) = Rp'_*(ν_{ι₃}(K)) ∘ E'_{Ψ_N K}
```
for the identifications `E : ι₁! ≅ Rp_* ι₃!` (`ProEtale.CondensedRing.openProperLowerShriekIso`)
is `NearbyCyclesModel.Hom.lowerShriekExchangeOfInv_comp_pushforwardExchange`, from the composition
law of the pullback exchanges and the description of the adjoint of `E` as the inverse of the
extension-by-zero base change. The remaining assembly is the formal
`ProEtale.CondensedRing.compactSupportExchangeAux_lift_eq_of_refinement`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme

section Refinement

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {k' : Type u} [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]
  {Y X₃ X₁ : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] [LocallyOfFiniteType X₃.hom] [QuasiCompact X₃.hom] [IsSeparated X₃.hom]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  {Y' X₃' X₁' : Over (Spec (.of k'))} [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
  [IsSeparated Y'.hom] [LocallyOfFiniteType X₃'.hom] [QuasiCompact X₃'.hom] [IsSeparated X₃'.hom]
  [LocallyOfFiniteType X₁'.hom] [QuasiCompact X₁'.hom] [IsSeparated X₁'.hom]
  {ι₃ : Y ⟶ X₃} {p : X₃ ⟶ X₁} {ι₁ : Y ⟶ X₁} [IsOpenImmersion ι₃.left] [IsProper p.left]
  [IsOpenImmersion ι₁.left] {ι₃' : Y' ⟶ X₃'} {p' : X₃' ⟶ X₁'} {ι₁' : Y' ⟶ X₁'}
  [IsOpenImmersion ι₃'.left] [IsProper p'.left] [IsOpenImmersion ι₁'.left]
  {N : NearbyCyclesModel Y.left Y'.left} {P₃ : NearbyCyclesModel X₃.left X₃'.left}
  {P₁ : NearbyCyclesModel X₁.left X₁'.left}

set_option maxHeartbeats 400000 in
-- the abstract identity is instantiated on the ambient derived categories of `ℚ̄_ℓ`-modules
/-- **The key identity of the refinement step for models** (blueprint `det-nearby-exchange-maps`,
proof): for open immersions `φ₃ : N ⟶ P₃`, `φ₁ : N ⟶ P₁` of models and a morphism
`π : P₃ ⟶ P₁` over proper `p`, `p'` with `ι₁ = ι₃ ≫ p`, `φ₁ = φ₃ ≫ π` and `Y`, `Y'` cartesian,
the identifications `E : ι₁! ≅ ι₃! ⋙ Rp_*` (`ProEtale.CondensedRing.openProperLowerShriekIso`)
intertwine the exchanges `ν_ι` (adjoint to `α_ι⁻¹`) through the pushforward exchange `χ_π`:
`χ_π(ι₃! K) ∘ Ψ_{P₁}(E_K) ∘ ν_{ι₁}(K) = Rp'_*(ν_{ι₃}(K)) ∘ E'_{Ψ_N K}`. The morphisms `E_K`,
`E'_{Ψ_N K}` are read on the ambient derived categories. -/
theorem NearbyCyclesModel.Hom.lowerShriekExchangeOfInv_comp_pushforwardExchange
    (φ₃ : N.Hom P₃ ι₃.left ι₃'.left) (φ₁ : N.Hom P₁ ι₁.left ι₁'.left)
    (π : P₃.Hom P₁ p.left p'.left) [IsIso (φ₃.pullbackExchange (Profinite.padicAlgClRingObj ℓ))]
    [IsIso (φ₁.pullbackExchange (Profinite.padicAlgClRingObj ℓ))]
    (w : ι₃ ≫ p = ι₁) (w' : ι₃' ≫ p' = ι₁') (htot : φ₃.total ≫ π.total = φ₁.total)
    (hgen : φ₃.generic ≫ π.generic = φ₁.generic)
    (sq : IsPullback ι₃.left (𝟙 Y.left) p.left ι₁.left)
    (sq' : IsPullback ι₃'.left (𝟙 Y'.left) p'.left ι₁'.left)
    (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (lowerShriekExchangeOfInv (openImmersionAdjunction ℓ ι₁.left)
        (openImmersionAdjunction ℓ ι₁'.left)
        (φ₁.pullbackExchange (Profinite.padicAlgClRingObj ℓ))).app
          M.obj ≫
      (P₁.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).map
        (X := D((ι₁.left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).obj
          M.obj)
        (Y := R((p.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
          (D((ι₃.left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).obj
            M.obj))
        ((openProperLowerShriekIso ℓ ι₃ p ι₁ w).hom.app M).hom ≫
      (π.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)).app
        (D((ι₃.left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).obj M.obj) =
    CategoryStruct.comp
      (X := D((ι₁'.left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).obj
        ((N.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj M.obj))
      (Y := R((p'.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
        (D((ι₃'.left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).obj
          ((N.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj M.obj)))
      ((openProperLowerShriekIso ℓ ι₃' p' ι₁' w').hom.app
        ((NearbyCyclesModel.boundedConstructibleNearbyCycles hN).obj M)).hom
      (R((p'.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).map
        ((lowerShriekExchangeOfInv (openImmersionAdjunction ℓ ι₃.left)
          (openImmersionAdjunction ℓ ι₃'.left)
          (φ₃.pullbackExchange (Profinite.padicAlgClRingObj ℓ))).app
            M.obj)) := by
  have hι : ι₃.left ≫ p.left = ι₁.left := congrArg CommaMorphism.left w
  have hι' : ι₃'.left ≫ p'.left = ι₁'.left := congrArg CommaMorphism.left w'
  have := isIso_map_openProperLowerShriekIso_comp_counit ℓ ι₃' p' ι₁' w' sq'
      ((NearbyCyclesModel.boundedConstructibleNearbyCycles hN).obj M)
  apply lowerShriekExchangeOfInv_app_comp_map_comp_pushforwardExchange_app
    (adjπ := derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) p.left)
    (adjπ' := derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) p'.left)
    (c := leftDerivedUpperStarCompOfEq (Profinite.padicAlgClRingObj ℓ) hι)
    (c' := leftDerivedUpperStarCompOfEq (Profinite.padicAlgClRingObj ℓ) hι')
    (adj₁ := openImmersionAdjunction ℓ ι₁.left) (adj₃ := openImmersionAdjunction ℓ ι₃.left)
    (adj₁' := openImmersionAdjunction ℓ ι₁'.left) (adj₃' := openImmersionAdjunction ℓ ι₃'.left)
  case hχπ => exact π.map_pushforwardExchange_app_comp_counit_app (Profinite.padicAlgClRingObj ℓ)
  case hα =>
    intro A
    rw [← reassoc_of% φ₃.pullbackExchange_comp_app_of_eq (Profinite.padicAlgClRingObj ℓ) π φ₁ hι hι'
          htot hgen A,
      ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.comp_id]
  case hE => exact unit_comp_upperStarComp_comp_map_openProperLowerShriekIso ℓ ι₃ p ι₁ w sq M
  case hE' =>
    exact unit_comp_upperStarComp_comp_map_openProperLowerShriekIso ℓ ι₃' p' ι₁' w' sq'
      ((NearbyCyclesModel.boundedConstructibleNearbyCycles hN).obj M)
  case hEb' => exact this

end Refinement

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.IsTraitModelOfBase

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {k' : Type u} [Field k'] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] [Algebra k k']
  {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {Y' : Over (Spec (.of k'))} [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
  [IsSeparated Y'.hom] {N : NearbyCyclesModel Y.left Y'.left} {q : N.total ⟶ trait k'}
  {g : N.generic ⟶ Spec (.of (traitGenericField k'))} {h : N.IsTraitModelOfBase k q g}

namespace Compactification

variable (C : h.Compactification)

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
  [IsSeparated Y'.hom] in
/-- The proper exchange `χ_a : Ψ_S Ra_* ⟶ Ra'_* Ψ_P` of the structure morphism of a
compactification is invertible on bounded constructible complexes
(`NearbyCyclesModel.IsTraitModelOfBase.isIso_pushforwardExchange_app_ambient`). -/
lemma isIsoOn_pushforwardExchange :
    IsIsoOn (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) C.X.left)).ι
      (C.isTraitModelOfBase.toTrait.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)) :=
  fun K ↦ C.isTraitModelOfBase.isIso_pushforwardExchange_app_ambient ℓ C.isPullback_ε _ K.property

instance : IsIso (C.hom.pullbackExchange (Profinite.padicAlgClRingObj ℓ)) :=
  C.hom.isIso_pullbackExchange_of_isOpenImmersion _ C.isPullback_hom_j

/-- **The compact-support exchange of a compactification** (blueprint `det-nearby-exchange-maps`
(3)): for the structure morphisms `a : Y ⟶ Spec k`, `a' : Y' ⟶ Spec k'` and a compactification
`N ⊆ P` over `ι : Y ⟶ X`, `ι' : Y' ⟶ X'`, the exchange `ν = χ_{a_P}⁻¹ ∘ Ra'_{P*}(ν_ι) :
Ra'_! Ψ_N ⟶ Ψ_S Ra_!` (`ProEtale.CondensedRing.compactSupportExchangeOfCompactification`). -/
noncomputable def compactSupportExchange :
    boundedConstructibleNearbyCycles (h.preservesBoundedConstructible ℓ) ⋙
        boundedConstructibleLowerShriek ℓ (toPoint Y') ⟶
      boundedConstructibleLowerShriek ℓ (toPoint Y) ⋙ traitSpecialization k k' (ℓ := ℓ) :=
  compactSupportExchangeOfCompactification ℓ (h.preservesBoundedConstructible ℓ)
    (preservesBoundedConstructible_traitModel ℓ) (comp_toPoint C.ι) (comp_toPoint C.ι') C.hom
    C.isTraitModelOfBase.toTrait (C.isIsoOn_pushforwardExchange ℓ)

end Compactification

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.IsTraitModelOfBase
