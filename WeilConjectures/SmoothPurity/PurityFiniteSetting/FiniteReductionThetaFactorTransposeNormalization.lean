/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionComparisons
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting
section Morphism
variable (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
variable {X Y : Scheme.{u}}
variable [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
variable [QuasiCompact (X ↘ Spec (.of P.field.k))]
variable [IsSeparated (X ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y ↘ Spec (.of P.field.k))]
variable [IsSeparated (Y ↘ Spec (.of P.field.k))]
variable (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

set_option linter.unusedSectionVars false in
private theorem finiteReductionSupport_naturality
    {K L : Scheme.proEtaleDerivedCategory X P.Ring} (a : K ⟶ L) :
    (P.finiteReduction m hm hmn Y).map ((P.smoothCompactSupport f).map a) ≫
        P.finiteReductionCompactSupportComparison m hm hmn f L =
      P.finiteReductionCompactSupportComparison m hm hmn f K ≫
        ((P.finiteReductionSetting m hm).smoothCompactSupport f).map
          ((P.finiteReduction m hm hmn X).map a) := by
  let := hasCompactification_of_finiteType_over_field P.field.k X Y f
  unfold finiteReductionCompactSupportComparison
  rw [← Adjunction.homEquiv_naturality_left_symm,
    ← Adjunction.homEquiv_naturality_right_symm]
  congr 1
  have hu := (P.finiteReductionAdjunction m hm hmn X).unit.naturality a
  have hc := (Scheme.sfCompactSupportRestriction
    (HasCompactification.compactification f)
      (P.finiteReductionRingHom m hm hmn)).hom.naturality
        ((P.finiteReduction m hm hmn X).map a)
  simp only [Functor.comp_map, Functor.id_map] at hu hc
  change (P.smoothCompactSupport f).map
      ((X.proEtaleCoefficientRestrictScalars
        (P.finiteReductionRingHom m hm hmn)).mapDerivedCategory.map
          ((P.finiteReduction m hm hmn X).map a)) ≫ _ =
    _ ≫ (Y.proEtaleCoefficientRestrictScalars
      (P.finiteReductionRingHom m hm hmn)).mapDerivedCategory.map
        (((P.finiteReductionSetting m hm).smoothCompactSupport f).map
          ((P.finiteReduction m hm hmn X).map a)) at hc
  rw [← Category.assoc, ← Functor.map_comp, hu, Functor.map_comp, Category.assoc, hc]
  simp only [Category.assoc]

/-- Reduction of a morphism followed by the exceptional coefficient mate has
the reduced original counit composite as transpose.
Source: blueprint/latest, thm-pur-finite-reduction-of-purity, Step 2
(blueprint: lem-pur-finite-reduction-theta-factor-transpose-normalization).

Proof: the counit equation defining finiteReductionExceptionalComparison
rewrites the transpose at its target. Naturality of the compact-support scalar
comparison at a moves F_B(Q_X a) across its inverse. Functoriality of scalar
extension then combines Q_Y(F_A a) with Q_Y(epsilon_A). No tensor, projection,
symmetry, theta, or orientation identity is used in this step.
-/
theorem finiteReduction_thetaFactor_transpose_normalization
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K)
    (S : Scheme.proEtaleDerivedCategory X P.Ring)
    (hS : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos X S)
    (a : S ⟶ (P.compositionExceptional f).obj K) :
    ((P.finiteReductionSetting m hm).smoothCompactSupport f).map
        ((P.finiteReduction m hm hmn X).map a ≫
          P.finiteReductionExceptionalComparison m hm hmn f d K hK) ≫
        (P.finiteReductionSetting m hm).smoothExceptionalCounit f
          ((P.finiteReduction m hm hmn Y).obj K) =
      (letI := P.finiteReductionCompactSupportComparison_isIso m hm hmn f S hS
       inv (P.finiteReductionCompactSupportComparison m hm hmn f S) ≫
         (P.finiteReduction m hm hmn Y).map
           ((P.smoothCompactSupport f).map a ≫ P.smoothExceptionalCounit f K))  := by
  let := P.finiteReductionCompactSupportComparison_isIso m hm hmn f S hS
  let cS := P.finiteReductionCompactSupportComparison m hm hmn f S
  let cL := P.finiteReductionCompactSupportComparison m hm hmn f
    ((P.compositionExceptional f).obj K)
  have hb0 := (P.existsUnique_finiteReductionExceptionalComparison
    m hm hmn f d K hK).choose_spec.1
  have hb := (show
      cL ≫
        ((P.finiteReductionSetting m hm).smoothCompactSupport f).map
          (P.finiteReductionExceptionalComparison m hm hmn f d K hK) ≫
        (P.finiteReductionSetting m hm).smoothExceptionalCounit f
          ((P.finiteReduction m hm hmn Y).obj K) =
      (P.finiteReduction m hm hmn Y).map (P.smoothExceptionalCounit f K) from by
    simpa only [cL, finiteReductionExceptionalComparison] using hb0)
  have hn := finiteReductionSupport_naturality P m hm hmn f a
  apply (cancel_epi cS).1
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc]
  rw [← hn]
  rw [Category.assoc]
  rw [hb]
  exact (IsIso.hom_inv_id_assoc cS _).symm



end Morphism
end WeilConjectures.PurityFiniteSetting
