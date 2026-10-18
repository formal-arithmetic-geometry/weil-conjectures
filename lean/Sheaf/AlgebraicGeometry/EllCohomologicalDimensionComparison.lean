/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q121
-/
module

public import Sheaf.AlgebraicGeometry.CohomologicalDimension
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension
import Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-!
# Pro-étale and étale primary cohomological dimensions agree

Source: current blueprint, `sec-six-functors-basics/sk-def-cd/`
`sk-def-cd-etale-comparison.md`, clauses 1--4 (blueprint: det-cd-etale-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Torsion transport, absolute and relative comparison, and the all-torsion bound.
Source: current blueprint, `sk-def-cd-etale-comparison.md`, clauses 1--4
(blueprint: det-cd-etale-comparison).
Proof:
1. By `det-pe-classical-sheaves-modules`, comparison pullback is an exact fully
faithful left adjoint on abelian sheaves (take the discrete coefficient ring Z).
Exactness preserves `F[ℓ^r]`, and the adjunction preserves their sheaf colimit.
It therefore sends the canonical annihilator cocone to the corresponding cocone.
Full faithfulness reflects invertibility of the canonical colimit map. An isomorphism
of coefficient sheaves preserves this condition, proving clause 1.
2. Apply the cohomology comparison to an étale abelian sheaf in degree zero.
The right-derived-functor definitions identify both sides as derived sections.
Taking degree-q cohomology gives isomorphic groups. Step 1 and the classical-sheaf
equivalence identify exactly the permitted inputs, so the sets of nonvanishing degrees
and their suprema agree, also if empty.
3. For the given qcqs g, the direct-image comparison in degree zero gives comparison
pullback of the étale derived image isomorphic to the pro-étale image. These are the
right derived functors in the cohomological-dimension definition. Exact pullback
commutes with cohomology and preserves zero; faithfulness reflects zero. Step 1 on X
and the classical-sheaf equivalence identify all inputs, giving equality of relative
suprema. No qcqs hypothesis is imposed on X or Y separately.
4. The annihilator colimit is the sheafification of the sectionwise union of kernels,
so its canonical map being invertible gives local ℓ-power annihilation. Thus it
satisfies the local torsion condition of `def-sc-etale-torsion-cd`; its cohomology
vanishes above c. By step 2 all nonvanishing degrees in the absolute supremum are at
most c, and the empty supremum is zero while c is nonnegative. -/
theorem ellCohomologicalDimension_etale_comparison (ℓ : ℕ) (hℓ : ℓ.Prime)
    (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [QuasiCompact g] [QuasiSeparated g] (c : ℕ) :
    (∀ (F₀ : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
      (F : Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1}),
      IsClassical ((sheafCompose (Scheme.ProEt.topology S)
        (forget AddCommGrpCat.{u + 1})).obj F) →
      Nonempty (F ≅ (comparisonUpperStar AddCommGrpCat.{u + 1} S).obj F₀) →
      (IsEllPowerTorsion ℓ hℓ F ↔ IsEllPowerTorsion ℓ hℓ F₀)) ∧
    cohomologicalDimension ℓ hℓ S = etaleCohomologicalDimension ℓ hℓ S ∧
    relativeCohomologicalDimension ℓ hℓ g =
      sSup {q : WithTop ℕ |
        ∃ n : ℕ, q = n ∧ ∃ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
          IsEllPowerTorsion ℓ hℓ F ∧
            ¬ IsZero
              ((_root_.DerivedCategory.homologyFunctor _ (n : ℤ)).obj
                ((AlgebraicGeometry.Etale.lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctor.obj
                  ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))} ∧
    (S.HasTorsionEtaleCohomologicalDimensionLE c →
      cohomologicalDimension ℓ hℓ S ≤ c) := by
  sorry

end AlgebraicGeometry.ProEtale
