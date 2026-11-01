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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting
section Morphism
variable (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
variable {X Y : Scheme.{u}}
variable [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
variable [QuasiCompact (X ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y ↘ Spec (.of P.field.k))]
variable (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- The counit cancellation needed after comparing theta mates.
Source: blueprint/latest, thm-pur-finite-reduction-of-purity, Step 2.
On a finite-Tor constructible source the reduced exceptional counit is
injective on the relevant Hom set.  The public wrapper
`finiteReduction_counit_bijective_public` supplies this restricted bijection;
applying its injective half to `h` proves the cancellation.  The source
hypothesis is essential, since the unrestricted Hom-set statement is not
available from the bounded-model adjunction.
(blueprint: lem-pur-finite-reduction-theta-factor-counit). -/
theorem finiteReduction_thetaFactor_counit
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K)
    {S : Scheme.proEtaleDerivedCategory X (P.finiteReductionSetting m hm).Ring}
    (hS : finiteTorConstructible (P.finiteReductionSetting m hm).coefficients.l
      (P.finiteReductionSetting m hm).extension (P.finiteReductionSetting m hm).level
      (P.finiteReductionSetting m hm).level_pos X S)
    {a b : S ⟶
      ((P.finiteReductionSetting m hm).compositionExceptional f).obj
        ((P.finiteReduction m hm hmn Y).obj K)}
    (h : ((P.finiteReductionSetting m hm).smoothCompactSupport f).map a ≫
        (P.finiteReductionSetting m hm).smoothExceptionalCounit f
          ((P.finiteReduction m hm hmn Y).obj K) =
      ((P.finiteReductionSetting m hm).smoothCompactSupport f).map b ≫
        (P.finiteReductionSetting m hm).smoothExceptionalCounit f
          ((P.finiteReduction m hm hmn Y).obj K)) : a = b := by
  exact (finiteReduction_counit_bijective_public
    (P.finiteReductionSetting m hm) f S hS
    ((P.finiteReduction m hm hmn Y).obj K)
    (P.finiteReduction_preserves_ctf m hm hmn Y K hK)).1 h
end Morphism
end WeilConjectures.PurityFiniteSetting
