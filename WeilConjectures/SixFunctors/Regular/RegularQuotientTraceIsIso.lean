/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Regular.RegularQuotientTraceData
import WeilConjectures.SixFunctors.RegularQuotientTraceOnInjectiveTerms

/-! # Invertibility of the normalized regular quotient coinduction trace

## References

* [Stacks, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks, Tag 0BZE](https://stacks.math.columbia.edu/tag/0BZE)
* [Stacks, Tag 0BZH](https://stacks.math.columbia.edu/tag/0BZH)
* [Stacks, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks, Tag 0A71](https://stacks.math.columbia.edu/tag/0A71)
* Zheng Lemma 5.22 and Proposition 5.26
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

attribute [-instance] PrincipalKoszulStrictReplacement.siteSmall
  PrincipalKoszulStrictReplacement.abSheafify PrincipalKoszulStrictReplacement.abLocallyBijective
  integralCoefficientAbSheafify integralCoefficientAbLocallyBijective
  scalarReductionSourceDerived scalarReductionTargetDerived
  GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance] HasDerivedCategory.standard
attribute [local irreducible] HasDerivedCategory.standard

/-- The actual quotient-linear cone trace is an isomorphism on unbounded derived categories. -/
theorem reductionCoinductionTrace_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ) :
    IsIso (reductionCoinductionTrace.{u} l E T n) := by
  obtain ⟨_, _, Rf, η, h⟩ :=
    SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{
      u + 1, u, u + 1} (Scheme.ProEt.topology T) (completedIntegralCommRingSheafUnrestricted l E T)
  suffices ∀ K, IsIso ((reductionCoinductionTrace.{u} l E T n).app K) from
    NatIso.isIso_of_isIso_app _
  intro K
  let X := DerivedCategory.Q.objPreimage K
  have : ∀ i : ℤ, Injective ((Rf.obj X).X i) := (h X).2.2
  have : QuasiIso (η.app X) := (h X).1
  refine (NatTrans.isIso_app_iff_of_iso _
    (DerivedCategory.Q.objObjPreimageIso K)).mp ?_
  exact (NatTrans.isIso_app_iff_of_iso _ (asIso (DerivedCategory.Q.map (η.app X)))).mpr
    (reductionCoinductionTrace_isIso_onInjectiveTerms l E T n (Rf.obj X))

end WeilConjectures
