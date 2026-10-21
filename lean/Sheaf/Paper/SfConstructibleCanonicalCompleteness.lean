/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.WeilCompletedTensorReflector
public import Sheaf.Paper.CompletedPullback
import Sheaf.Paper.PbcIntrinsicTowerComplete
import Sheaf.Paper.CompletedKoszulQuotientComparison

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
Source: blueprint `def-wf-tensor-product`, first sentence, base proof Step 10;
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
      (i : DerivedCategory.Q.obj D ≅ M),
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

/-- In particular, the reflector's canonical actual representative has invertible unit.
Source: blueprint `def-wf-tensor-product`, first sentence, base proof Step 10;
Stacks Tag 0A0E
(blueprint: lem-sf-constructible-canonical-completeness).

Proof: specialize the arbitrary-representative assertion of
`sfConstructibleCanonicalCompleteness` to `wfCompletionRepresentative X d M` and
`DerivedCategory.Q.objObjPreimageIso M`. By definition this is precisely the unit
used in `WfIsComplete`, including its supplied realization isomorphism. -/
theorem sfConstructibleCanonicalReflectorComplete
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : PbcCompletedDerived X d) (hM : PbcIsIntrinsicallyComplete X d M)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal) :
    WfIsComplete X d r a ha M := by
  exact (sfConstructibleCanonicalCompleteness X d M hM).1 r a ha
    (wfCompletionRepresentative X d M) (DerivedCategory.Q.objObjPreimageIso M)

/-- Every integral bounded constructible complete object satisfies canonical actual
completeness, both for the reflector and for the strict quotient-tower unit.
Source: blueprint `def-wf-tensor-product`, first sentence, base proof Step 10;
Stacks Tags 0A0E and 099M
(blueprint: lem-sf-constructible-canonical-completeness).

Proof: the first membership condition of the published integral full subcategory
supplies `PbcIsIntrinsicallyComplete` for its underlying object. Apply
`sfConstructibleCanonicalCompleteness` for tower completeness and
`sfConstructibleCanonicalReflectorComplete` for every generating tuple. The
uniform constructibility and compatible etale-origin conditions are not used.
The valuation-ring datum is exactly `pbcPadicCoefficientDatum l E`. -/
theorem sfIntegralConstructibleCanonicalCompleteness
    (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [IsNoetherian X] (hdim : ∃ n : ℕ, topologicalKrullDim X ≤ n)
    (hl : IsUnit (l : Γ(X, ⊤))) (M : pbcBoundedConstructibleComplete X l E hdim hl) :
    (pbcPadicCoefficientDatum l E).TowerComplete X M.obj ∧
    ∀ (r : ℕ) (a : Fin r → Padic.coefficientExtensionIntegers l E)
      (ha : Ideal.span (Set.range a) = (pbcPadicCoefficientDatum l E).ideal),
      WfIsComplete X (pbcPadicCoefficientDatum l E) r a ha M.obj := by
  have hM : PbcIsIntrinsicallyComplete X (pbcPadicCoefficientDatum l E) M.obj := M.property.1
  refine ⟨(sfConstructibleCanonicalCompleteness X _ M.obj hM).2, ?_⟩
  intro r a ha
  exact sfConstructibleCanonicalReflectorComplete X _ M.obj hM r a ha

end AlgebraicGeometry.Scheme
