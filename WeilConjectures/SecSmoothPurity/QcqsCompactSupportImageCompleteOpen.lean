/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.DerivedCompletionSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.IntegralResidueCriterion
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel

/-! # Derived completeness of ordinary quasi-compact open extension

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-lem-sp-tower/lem-coef-integral-compact-support.proof.md, completeness paragraph
(blueprint: lem-qcqs-compact-support-image-complete-open).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Extension by zero along a quasi-compact open immersion preserves derived completeness.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-tower/
lem-coef-integral-compact-support.proof.md, completeness paragraph: the open factor `j_!`
commutes with the derived inverse-limit
reduction tower and carries the canonical completion map to that of `j_! K`.
The final implication is the integral criterion on a Noetherian open.
Proof plan: (1) represent `K` by a K-flat complex and use the principal-reduction
cone calculus; exact, additive, integral-linear extension by zero identifies every
reduction cone and its transition and coaugmentation maps with the corresponding
cone for the image. (2) The quasi-compact open-extension limit theorem identifies
the image of the derived inverse limit with the derived inverse limit of these
identified reductions. (3) Apply extension by zero to the invertible completion map
of `K`; the resulting composite is the canonical completion map of the image, so it
is invertible. (4) On a Noetherian `U`, the integral criterion gives completeness of
every integral bounded constructible `K`, and step (3) applies.
(blueprint: lem-qcqs-compact-support-image-complete-open). -/
theorem qcqsCompactSupportImageCompleteOpen
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (K : DerivedCategory (AdicCompletion.Modules l E U)) :
    (IsDerivedComplete l E U K →
      IsDerivedComplete l E X
        ((CondensedRing.openImmersionLowerShriek
          (DerivedNakayama.integerRing l E) j).mapDerivedCategory.obj K)) ∧
    (∀ [IsNoetherian U],
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) U K →
        IsDerivedComplete l E X
          ((CondensedRing.openImmersionLowerShriek
            (DerivedNakayama.integerRing l E) j).mapDerivedCategory.obj K)) := by
  sorry

end AlgebraicGeometry.ProEtale
