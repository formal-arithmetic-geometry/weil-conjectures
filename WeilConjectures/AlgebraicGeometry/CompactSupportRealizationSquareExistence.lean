/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedERealization
public import WeilConjectures.AlgebraicGeometry.IntegralCoefficientCompletenessTransportSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.CompactSupportCondensedRealization


/-! Existence of the normalized ordinary restriction square.

Source: Bhatt--Scholze 6.8.14(2), separated from the uniqueness argument in
`lem-zl-compact-support-realization-coordinates-setup`.
(blueprint: lem-zl-compact-support-realization-square-existence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open WeilConjectures

namespace WeilConjectures.CompactSupportFactorNormalization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The identity-on-sections ordinary restriction square exists.
Source: Bhatt--Scholze 6.8.14(2); the existence part of the coordinate square.
(blueprint: lem-zl-compact-support-realization-square-existence).
Proof: the coefficient maps are precomposition on continuous functions. The
restriction/direct-image square is induced by these maps and is identity on every
underlying section. The construction of the map and its naturality are left as the
existence step; the parent proves its uniqueness from the displayed section law. -/
theorem ordinaryRestrictionSquare_exists {X Y : Scheme.{u}} (g : X ⟶ Y)
    (AX : CondensedERealization.At l E X) (AY : CondensedERealization.At l E Y) :
    let ordinaryRestrictCore := fun (W : Scheme.{u})
        (A : CondensedERealization.At l E W) =>
      (CondensedERealization.moduleEncoding l E W A.sectionIso).functor ⋙
        pbcRestrict (A.integralIso.hom ≫ A.inclusion) ⋙
          purOrdinaryCoefficientModel l E W
    ∃ e : CondensedRing.lowerStar (Profinite.continuousCoefficientRingObj E) g ⋙
        ordinaryRestrictCore Y AY ≅
      ordinaryRestrictCore X AX ⋙
        proEtaleRingModuleDirectImage g ((PurCompactSupport.completed l E).ring Y)
          ((PurCompactSupport.completed l E).ring X)
          ((PurCompactSupport.completed l E).pull g),
      ∀ (M : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
          (CondensedERealization.Coefficient E X)) (V : Y.ProEtᵒᵖ)
        (x : ((ordinaryRestrictCore X AX ⋙
          proEtaleRingModuleDirectImage g ((PurCompactSupport.completed l E).ring Y)
            ((PurCompactSupport.completed l E).ring X)
            ((PurCompactSupport.completed l E).pull g)).obj M).val.obj V),
        ((e.hom.app M).val.app V).hom x = x := by
  sorry

end WeilConjectures.CompactSupportFactorNormalization
