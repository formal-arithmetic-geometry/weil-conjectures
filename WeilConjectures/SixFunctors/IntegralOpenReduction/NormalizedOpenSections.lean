/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralOpenReduction.IntegralOpenReductionDefinitions
import WeilConjectures.AlgebraicGeometry.System.SystemBlockRepetition
/-! # Section normalization for semilinear open localization

## References

* [Stacks, Tag 03DI]
* [Stacks, Tag 03DJ]
* [Stacks, Tag 0941]
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralOpenReduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The semilinear calculus can use the literal section identification at the given open. -/
theorem normalizedOpenSections :
    ∃ sections : SemilinearSections.SemilinearDerivedSectionsData.{t+1, t, max u (t+1)}
        (ProEt.topology X) (rings l E X) (transitions l E X),
      ∀ (n : ℕ) N V x,
        HEq ((((sections.localization (openObject j)).restrictionEvaluation n).hom.app N).val.app
          V x) x := by
  classical
  let : EssentiallySmall.{max u (t + 1)} X.ProEt :=
    essentiallySmallSelf.{u, t, t + 1} X.ProEt
  let J := ProEt.topology X
  let B := rings l E X
  let τ := transitions l E X
  obtain ⟨sections⟩ :=
    SemilinearSections.semilinearDerivedSections.{t + 1, t, max u (t + 1)} J B τ
  obtain ⟨R⟩ :=
    SemilinearSections.systemBlockRepetition.{t + 1, t, max u (t + 1)} J B τ
    SemilinearSections.SystemBlockMap.id
  have existsNormalized (V : X.ProEt) :
      ∃ O : SemilinearSections.OpenSystems.{t + 1, t, max u (t + 1)} J B τ V,
        ∀ (n : ℕ) N W x,
          HEq ((((O.restrictionEvaluation n).hom.app N).val.app W) x) x := by
    obtain ⟨O, _OD, hO, _hOD, _⟩ :=
      SemilinearSections.blockRepeat_extensionByZero.{t + 1, t, max u (t + 1)}
        J SemilinearSections.SystemBlockMap.id B τ V R
    exact ⟨O, hO⟩
  choose O hO using existsNormalized
  exact ⟨{ sections with localization := O }, hO (openObject j)⟩

end WeilConjectures.IntegralOpenReduction
