/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.Module
public import WeilConjectures.SixFunctors.ProEtale.GaloisCoverTrace

/-!
# The unit of `g^* ⊣ g_*` is a monomorphism for a surjective weakly étale `g`

Let `g : Y ⟶ X` be a quasi-compact surjective weakly étale morphism of schemes. The unit
`M ⟶ g_* g^* M` of pro-étale sheaves is a monomorphism.

## Main results

- `AlgebraicGeometry.ProEtale.mono_upperStarLowerStarAdjunction_unit_app_of_surjective`: the
  unit of `g^* ⊣ g_*` on sheaves of `ℚ̄_ℓ`-modules is a monomorphism.
- `AlgebraicGeometry.ProEtale.mono_adicUpperStarLowerStarAdjunction_unit_app`: the same for
  sheaves of modules over the constant `ℓ`-adic sheaf.

## Implementation details

Since `g` is weakly étale, the pullback `g^*` on pro-étale sheaves is restriction along the
localization functor, and the unit `M ⟶ g_* g^* M` evaluates, on sections over `V ∈ X_proét`, to
the restriction of `M` along the projection `V ×_X Y ⟶ V`. This projection is a pro-étale
covering, so restriction along it is injective. The `ℓ`-adic version follows since its underlying
morphism of sheaves of `ℚ̄_ℓ`-modules is the unit of
`AlgebraicGeometry.ProEtale.upperStarLowerStarAdjunction`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (g : Y ⟶ X) [WeaklyEtale g] [Surjective g]
  [QuasiCompact g]

/-- For a quasi-compact surjective weakly étale `g`, the unit of `g^* ⊣ g_*` on sheaves of
`ℚ̄_ℓ`-modules is a monomorphism. -/
theorem mono_upperStarLowerStarAdjunction_unit_app_of_surjective
    (M : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)) :
    Mono ((upperStarLowerStarAdjunction (WeilCoefficients.{u} l) g).unit.app M) := by
  have hM : Presieve.IsSheaf (Scheme.ProEt.topology X)
      (M.obj ⋙ CategoryTheory.forget (WeilCoefficients.{u} l)) :=
    (isSheaf_iff_isSheaf_of_type _ _).1 ((sheafCompose _ (CategoryTheory.forget _)).obj M).property
  have : Mono ((localizationRestrictionLowerStarAdjunction (WeilCoefficients.{u} l) g
      inferInstance).unit.app M).hom := by
    have (V : X.ProEtᵒᵖ) : Mono (((localizationRestrictionLowerStarAdjunction
        (WeilCoefficients.{u} l) g inferInstance).unit.app M).hom.app V) := by
      rw [ModuleCat.mono_iff_injective]
      exact (Presieve.isSeparatedFor_singleton
        (P := M.obj ⋙ CategoryTheory.forget (WeilCoefficients.{u} l))).1
        ((Presieve.isSheafFor_iff_generate _).2
          (hM _ (generate_singleton_baseChangeProj_mem g V.unop))).isSeparatedFor
    exact NatTrans.mono_of_mono_app _
  have : Mono ((localizationRestrictionLowerStarAdjunction (WeilCoefficients.{u} l) g
      inferInstance).unit.app M) := Sheaf.Hom.mono_of_presheaf_mono _ _ _
  exact mono_of_mono_fac (Adjunction.unit_leftAdjointUniq_hom_app _
    (localizationRestrictionLowerStarAdjunction (WeilCoefficients.{u} l) g inferInstance) M)

/-- For a quasi-compact surjective weakly étale `g`, the unit of `g^* ⊣ g_*` on `ℓ`-adic
sheaves is a monomorphism. -/
theorem mono_adicUpperStarLowerStarAdjunction_unit_app (M : AdicSheaf l X) :
    Mono ((adicUpperStarLowerStarAdjunction l g).unit.app M) := by
  have : Mono ((adicUpperStarLowerStarAdjunction l g).unit.app M).hom := by
    rw [adicUpperStarLowerStarAdjunction, Adjunction.modAdjunction_unit_app_hom]
    have := mono_upperStarLowerStarAdjunction_unit_app_of_surjective l g M.X
    infer_instance
  have : Mono ((AdicSheaf.forget X).map ((adicUpperStarLowerStarAdjunction l g).unit.app M)) :=
    this
  exact (AdicSheaf.forget X).mono_of_mono_map this

end AlgebraicGeometry.ProEtale
