/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefTowerTraceData

/-! Exact transport between the two chosen section localizations. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Identity on module complexes, localized into the smaller chosen derived category.
Source: universal property of localization
(blueprint: new-def-coef-trace-section-normalization). -/
def coefTraceSmallSections :
    @DerivedCategory.{u + 2} (ModuleCat.{u + 1} (coefTraceRing l E)) _ _
        (HasDerivedCategory.standard _) ⥤
      @DerivedCategory.{u + 1} (ModuleCat.{u + 1} (coefTraceRing l E)) _ _
        (HasDerivedCategory.ofIsGrothendieckAbelian _) :=
  @Functor.mapDerivedCategory.{u + 2, u + 1, u + 1, u + 1, u + 2, u + 2}
    (ModuleCat.{u + 1} (coefTraceRing l E)) _ _ (HasDerivedCategory.standard _)
    (ModuleCat.{u + 1} (coefTraceRing l E)) _ _
      (HasDerivedCategory.ofIsGrothendieckAbelian _) (𝟭 _) _ _ _

end WeilConjectures
