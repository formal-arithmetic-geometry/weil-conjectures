/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.Paper.SmoothPurityTowerShriekData

/-! # Evaluation of the tower open adjunction unit

Source: blueprint latest, integral direct-image proof, paragraph (3), and the
ordinary open-unit evaluation and termwise localization in SpTowerShriek.Open.
(blueprint: lem-sp-tower-open-adjunction-unit-evaluation)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The specified derived open and inverse-image comparisons carry the tower unit
into the finite unit. No tensor or projection map occurs in this statement.
Source: blueprint latest, integral direct-image proof, paragraph (3), evaluation of
projection transposes; Open.unit_evaluation and Open.unit_termwise
(blueprint: lem-sp-tower-open-adjunction-unit-evaluation).
Proof: substitute Open.unit_termwise and the termwise definition of openEvaluation.
The inverse-image comparison is the localization of ordinaryPullEvaluation, by its
identification with the generic normalized comparison. On complexes, apply the
ordinary Open.unit_evaluation degree by degree. The factors for localization of
identities and compositions cancel by their naturality and associativity laws.
The finite adjunction is the right-derived localization of finiteOpenAdjunction,
transported along rightDerivedFunctorIsoMapDerivedCategory, so its unit is the
same termwise localized unit. Equality descends by the universal property of the
ordinary derived localization; no faithfulness of level evaluation is used. -/
theorem open_adjunction_unit_evaluation (b : Base l E)
    {U T : Scheme.{u}} {j : U ⟶ T} [IsOpenImmersion j]
    {g : Geometry l E b j} (o : Open l E b j g) (n : ℕ) (C : D l E U) :
    (Ev l E U n).map (o.derivedAdjunction.unit.app C) ≫
        (g.pullEvaluation n).hom.app ((openD l E b o).obj C) ≫
        (proEtaleConstantRingDerivedPullback (R l E n) j).map
          ((openEvaluation l E b o n).hom.app C) =
      (Adjunction.unit
        (((finiteOpenAdjunction l E b j n).mapDerivedCategoryRightDerivedAdjunction).ofNatIsoRight
          (proEtaleConstantRingPullback (R l E n) j).rightDerivedFunctorIsoMapDerivedCategory)).app
        ((Ev l E U n).obj C) := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerShriek
