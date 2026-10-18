/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.ExceptionalProEtaleRealization
/-! # Realization of the actual etale/pro-etale system comparison
Source: blueprint def-weil-exceptional-inverse-image. All ordinary maps are fixed on
sections or by adjunction transposes; their derived maps retain the localization units.
(blueprint: def-pur-adic-site-realization).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry SheafOfModules
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
  (P : StrictEtaleEvaluation W (integralExceptionalIntegers l E)
    (integralExceptionalUniformizer l E))
  (B : IntegralExceptionalComparison l E W P)

/-- Ordinary site direct-image realization, fixed on every section by the actual
underlying set-sheaf comparison.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-site-realization).
Proof: both direct images restrict a sheaf along the actual etale-to-pro-etale functor. The
recorded rightUnderlying map identifies their values on each etale test object. The
quotient coordinate equivalence fixes constants, so these maps are linear, natural,
and invertible. Faithful forgetting to set sheaves proves uniqueness. -/
theorem integralExceptionalSiteRight_existsUnique (n : ℕ) :
    ∃! e : B.ordinary.right n ⋙ integralExceptionalEtaleRealization l E W n ≅
      integralExceptionalProRealization l E W n ⋙
        ProEtale.comparisonLowerStar (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W,
      ∀ (M : coefficientLevelModules (J := Scheme.ProEt.topology W)
        (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n)
        (U : W.Etaleᵒᵖ) (x : ((B.ordinary.right n).obj M).val.obj U),
        (e.hom.app M).hom.app U x =
          ((B.ordinary.rightUnderlying n).hom.app M).hom.app U x := by
  sorry

/-- The ordinary direct realization, fixed on all sections.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-site-realization). -/
def integralExceptionalSiteRight (n : ℕ) :=
  (integralExceptionalSiteRight_existsUnique l E W P B n).exists.choose

/-- Ordinary inverse realization, fixed by its full adjunction transpose equation.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-site-realization).
Proof: transport the two site adjunctions along the exact realization equivalences.Take
 the mate of the already section-normalized ordinary direct comparison. The
adjunction bijections imply the displayed equation and uniqueness of the map. -/
theorem integralExceptionalSiteInverse_existsUnique (n : ℕ) :
    ∃! e : (B.ordinary.lift n).modules ⋙ integralExceptionalProRealization l E W n ≅
      integralExceptionalEtaleRealization l E W n ⋙
        ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W,
      ∀ (M : strictEtaleLevel W (integralExceptionalIntegers l E)
          (integralExceptionalUniformizer l E) n)
        (N : coefficientLevelModules (J := Scheme.ProEt.topology W)
          (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n)
        (h : (B.ordinary.lift n).modules.obj M ⟶ N),
        (ProEtale.comparisonAdjunction (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).homEquiv _ _
          (e.inv.app M ≫ (integralExceptionalProRealization l E W n).map h) =
        (integralExceptionalEtaleRealization l E W n).map
          ((B.ordinary.levelAdj n).homEquiv _ _ h) ≫
            (integralExceptionalSiteRight l E W P B n).hom.app N := by
  sorry

/-- The specified ordinary inverse comparison.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-site-realization). -/
@[no_expose] def integralExceptionalSiteInverse (n : ℕ) :=
  (integralExceptionalSiteInverse_existsUnique l E W P B n).exists.choose

end WeilConjectures
