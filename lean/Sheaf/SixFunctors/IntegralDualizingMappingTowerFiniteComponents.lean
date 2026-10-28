/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A9
-/
module

public import Sheaf.SixFunctors.IntegralDualizingMappingTower
import Sheaf.SixFunctors.IntegralDualizingMappingTowerSystemModel
import Sheaf.SixFunctors.IntegralDualizingSystemFiniteAdjunction
import Sheaf.SixFunctors.IntegralDualizingSupportSystemHomComparison
import Sheaf.SixFunctors.CoefPairingCompactificationModels

/-! # Coherent component comparisons for strict mapping towers

Source: current blueprint prop-coef-integral-dualizing, second proof paragraph.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/--
The finite exceptional adjunctions provide a coherent component comparison before
those components are assembled into a natural isomorphism of functors.  The
component family is indexed by the opposite integral constructible category, and
its equation is the naturality square for every morphism in that category.

Source: current blueprint prop-coef-integral-dualizing, middle and final displayed
comparisons in the second proof paragraph, and its final counit-compatibility sentence.
(blueprint: lem-coef-integral-dualizing-mapping-tower-finite-components).

Proof: realize the normalized tower by a quotient-system complex Q. Transport
its finite identifications through the realization isomorphisms; cancelling the
realization isomorphism at the source reduces their transition square to he.
Choose the existing compactification pairing frame. Compose the scalar mapping
comparison, the strict finite exceptional adjunction, and the compact-support
scalar Hom comparison. Taking the components of this composite natural
isomorphism gives the asserted family, and its naturality gives the equation.
The three comparisons are separate named steps; the construction takes place
before any inverse limit. Zero inputs and empty schemes are included.
-/
theorem integralDualizing_mapping_tower_finite_components
    (T : NormalizedDVRTower l E X D hl)
    (e : ∀ n : ℕ, T.M n ≅ integralDualizingFiniteTerm l E D X n)
    (he : ∀ {m n : ℕ} (h : n ≤ m),
      T.tau h ≫ (normalizedDVRRes l E X h).map (e n).hom =
        (e m).hom ≫
          (Adjunction.ofIsRightAdjoint (normalizedDVRRes l E X h)).homEquiv _ _
            (integralDualizingFiniteComparison l E D X hl h)) :
    ∃ (a : ∀ K : (sfIntegralConstructibleCategory l E X)ᵒᵖ,
      (integralDualizingMappingTower l E X T.tower).obj K ≅
        ((integralDualizingCompactSections l E D hl X).op ⋙
          integralDualizingCoefficientHomTower l E).obj K),
      ∀ {K L : (sfIntegralConstructibleCategory l E X)ᵒᵖ} (f : K ⟶ L),
        (integralDualizingMappingTower l E X T.tower).map f ≫ (a L).hom =
          (a K).hom ≫
            ((integralDualizingCompactSections l E D hl X).op ⋙
              integralDualizingCoefficientHomTower l E).map f := by
  obtain ⟨Q, a, ha, hmodel⟩ := integralDualizing_mapping_tower_system_model
    D l hl E X T
  let eQ (n : ℕ) := (a n).symm ≪≫ e n
  have hQ : ∀ {m n : ℕ} (h : n ≤ m),
      (coefficientSequenceDerivedTransition l E X h).app (coefTraceInput l E X Q) ≫
          (normalizedDVRRes l E X h).map (eQ n).hom =
        (eQ m).hom ≫
          (Adjunction.ofIsRightAdjoint (normalizedDVRRes l E X h)).homEquiv _ _
            (integralDualizingFiniteComparison l E D X hl h) := by
    intro m n h
    apply (cancel_epi (a m).hom).1
    calc
      (a m).hom ≫
          ((coefficientSequenceDerivedTransition l E X h).app (coefTraceInput l E X Q) ≫
            (normalizedDVRRes l E X h).map (eQ n).hom) =
          (T.tau h ≫ (normalizedDVRRes l E X h).map (a n).hom) ≫
            (normalizedDVRRes l E X h).map (eQ n).hom := by
        rw [ha h]
        simp only [Category.assoc]
      _ = T.tau h ≫ (normalizedDVRRes l E X h).map (e n).hom := by
        rw [Category.assoc, ← Functor.map_comp]
        simp [eQ]
      _ = (e m).hom ≫
          (Adjunction.ofIsRightAdjoint (normalizedDVRRes l E X h)).homEquiv _ _
            (integralDualizingFiniteComparison l E D X hl h) := he h
      _ = (a m).hom ≫ ((eQ m).hom ≫
          (Adjunction.ofIsRightAdjoint (normalizedDVRRes l E X h)).homEquiv _ _
            (integralDualizingFiniteComparison l E D X hl h)) := by
        simp [eQ, Category.assoc]
  obtain ⟨S, G, _⟩ := coefPairingCompactificationModels l E D X hl Q eQ
  obtain ⟨b⟩ := hmodel S
  obtain ⟨c⟩ := integralDualizing_system_finite_adjunction D l hl E X S G Q eQ hQ
  obtain ⟨d⟩ := integralDualizing_support_system_hom_comparison D l hl E X S G
  let α := b ≪≫ c ≪≫ d
  exact ⟨fun K ↦ α.app K, fun f ↦ α.hom.naturality f⟩

end WeilConjectures
