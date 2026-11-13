/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
public import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedTensorReflector
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedPullback
import WeilConjectures.AlgebraicGeometry.Pbc.PbcIntrinsicTowerComplete
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulQuotientComparison

/-! # Presentation witnesses imply canonical actual completeness

Source: blueprint `sec-six-functors/sk-rem-sf-pf-done/def-wf-tensor-product`,
first sentence and the base proof Step 10 (`wfConstructible_complete`);
Stacks Tags 0A0E and 099M.
(blueprint: lem-sf-constructible-canonical-completeness).

The hypothesis is the published existential presentation witness. The conclusions
use the actual completed ring, every generating tuple and representative, the
reflector's canonical representative, and the specified strict quotient-tower unit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- An intrinsic presentation witness makes every actual Koszul unit and the canonical
strict quotient-tower unit invertible.
Source: blueprint `prose-03-02`, first sentence, base proof Step 10;
Stacks Tags 0A0E and 099M
(blueprint: lem-sf-constructible-canonical-completeness).

Proof: apply `pbcIntrinsicComplete_towerComplete` to the existential presentation
witness to obtain invertibility of `d.completionUnit X M`. For any generating tuple,
actual complex and realization, `completedKoszulQuotientComparison` gives an
isomorphism from its Koszul completion to the derived quotient limit. Its unit
equation identifies the Koszul unit followed by this isomorphism with the same
canonical tower unit. The quotient tower indexed by n >= 0 uses I^(n+1), which
reindexes the positive-exponent tower without changing its augmentation. Cancel
the comparison isomorphism to obtain invertibility of the specified Koszul unit.
No relation with the witnessing tuple or representative is required. -/
theorem sfConstructibleCanonicalCompleteness
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : PbcCompletedDerived X d) (hM : PbcIsIntrinsicallyComplete X d M) :
    (∀ (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
      (D : CochainComplex (reductionModules X (d.completedRing X)) ℤ)
      (i : (DerivedCategory.Q.obj D : PbcCompletedDerived X d) ≅ M),
      IsIso (intrinsicCompletionUnit X d r a ha M D i)) ∧
    d.TowerComplete X M := by
  have hTower := pbcIntrinsicComplete_towerComplete d X M hM
  refine ⟨?_, hTower⟩
  intro r a ha D i
  obtain ⟨c, hc⟩ := completedKoszulQuotientComparison X d r a ha M D i
  change intrinsicCompletionUnit X d r a ha M D i ≫ c.hom = d.completionUnit X M at hc
  apply (isIso_comp_right_iff _ c.hom).mp
  rw [hc]
  exact hTower

end AlgebraicGeometry.Scheme
