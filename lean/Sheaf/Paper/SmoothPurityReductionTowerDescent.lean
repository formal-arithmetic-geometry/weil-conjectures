/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Sheaf.Paper.SmoothPurityReductionTowerData


/-! # Strict reduction in the chosen coefficient-tower presentation

Source: blueprint latest, normalized-towers-reduction, construction paragraph;
Stacks Tags 00YV, 06YS, 06YY, 0G7D.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- Transport strict tensor descent to the fixed section-ring and tower presentations.
For a supplied coefficient isomorphism, this constructs the functor and its universal
comparison only; it asserts
neither invertibility of reduction maps nor any constructibility or Tor bound.

Source: blueprint latest, sec-smooth-purity, normalized-towers-reduction, construction;
Stacks Tags 00YV, 06YS, 06YY, 0G7D
(blueprint: lem-sp-reduction-tower-presentation-descent).

Proof:
1. Compose the supplied coefficient isomorphism with the ell-power projections.
Naturality of the limit cone makes them compatible with all quotient transitions,
including equal indices.
2. Apply strictCoefficientTensorDescent to these maps. Its ordinary tensor systems have
levels M tensor R_n and quotient transitions on pure tensors.
3. Uncurry the ringed-sequence-site systems into StrictRingSystem, then apply the
inverse of D.equivalence. Both equivalences preserve the actual section modules and
semilinear maps. The resulting ordinary functor is additive. Uniqueness of the
sheafified scalar-extension left adjoint identifies its levels with D.scalar, carrying
their actual pure tensor generators to systemModelTmul. Hence transition has the
specified formula for every pair of indices.
4. Apply the exact equivalences to the descended derived functor and its comparison.
The universal property of localization and uniqueness of left derived functors give
the asserted counit and universal property. Evaluation compares it with D.scalar's
universal derived functor, giving the natural evaluation isomorphisms.
5. For a K-flat complex, scalar extension preserves quasi-isomorphisms between such
complexes, without requiring flat terms. Every evaluated comparison is therefore
invertible by the K-flat computation theorem. Exact evaluations jointly detect
quasi-isomorphisms of tower complexes, hence detect these derived isomorphisms.
This proves computes for all K-flat complexes, beyond the flat-term resolving class.
No qcqs assumption or boundedness is used; zero modules and empty schemes are included.
-/
theorem sp_reduction_tower_presentation_descent (D : SpCoefficientTowersAbelian l E T)
    (coefficient : spIntegralSectionRing l E T ≅
      WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T) :
    ∃ (ordinary : spIntegralSectionModules l E T ⥤ spCoefficientTowers l E T)
        (_additive : ordinary.Additive)
        (level : spReductionOrdinaryLevels l E T D coefficient ordinary),
        IsSpReductionTransition l E T D coefficient ordinary level ∧
        ∃ (red : DerivedCategory (spIntegralSectionModules l E T) ⥤
            spDerivedCoefficientTowers l E T D)
          (counit : DerivedCategory.Q ⋙ red ⟶
            ordinary.mapHomologicalComplex (.up ℤ) ⋙ spTowerLocalization l E T D),
          red.IsLeftDerivedFunctor counit
            (HomologicalComplex.quasiIso (spIntegralSectionModules l E T) (.up ℤ)) ∧
          (∀ P : CochainComplex (spIntegralSectionModules l E T) ℤ,
            CochainComplex.IsKFlatIndependentCoefficients (R := spIntegralSectionRing l E T)
              P → IsIso (counit.app P)) ∧
          Nonempty (spReductionDerivedEvaluations l E T D coefficient red) := by sorry

end AlgebraicGeometry.ProEtale
