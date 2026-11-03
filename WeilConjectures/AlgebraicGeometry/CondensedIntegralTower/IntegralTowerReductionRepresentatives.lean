/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.IntegralTowerOrdinaryTransition

/-! # K-flat representatives of the specified reduction maps

Source: latest blueprint, sk-lem-sp-tower, reduction-image step, and
sk-prop-sp-integral-towers-reduction, Normalization paragraph.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedIntegralTower
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

set_option maxHeartbeats 1600000 in
-- The representative formula compares several dependent scalar-extension coordinates.
/-- The universal reduction counit computes on native K-flat complexes; evaluation
of their ordinary reductions computes every successive scalar extension. The last
identity pins the derived transition adjunct to the ordinary one on all representatives.
Source: latest blueprint, sk-lem-sp-tower.proof.md, paragraph 1, reduction-image
sentence; sk-prop-sp-integral-towers-reduction.proof.md, Construction and Normalization;
Stacks 06YS, 06YY and 0FND
(blueprint: lem-sp-current-reduction-representatives).

Proof: transport a native K-flat complex through the exact monoidal section equivalence.
K-flatness is tested by tensoring with acyclic complexes and is preserved by that
comparison. Internal scalar extension sends a K-flat complex to a K-flat complex over
the finite quotient: by the tensor-restriction adjunction its acyclic tests are the
same acyclic tests after exact restriction. The ordinaryLevels comparisons therefore
identify the evaluated ordinary reductions with K-flat scalar extensions. The normalized
scalar counit computes on them. The finiteCounit maps also compute on the source
K-flat complex. Apply levels_counit and the finite level isomorphisms to see that every
evaluation of redCounit is invertible; the section equivalences reflect isomorphisms
and D.reductions.detectsIso gives invertibility of redCounit itself.
For the final equation apply the injective derived scalar Hom correspondence. The
scalar model's transpose formula sends its counit followed by Q of the ordinary
adjunct to Q of the strict transition followed by the exact restriction factorization.
D.reductions.transition_rep is precisely this same map on Q of a tower complex.
Cancel the invertible evaluation and restriction factorizations, and transpose back.
This equation holds for every tower complex; no K-flatness is used for this equality.
The zero complex, unbounded complexes and equal indices are covered by the same
localization and normalized-unit identities. -/
theorem reduction_representatives (D : Model l E T) :
    (∀ (P : CochainComplex (AdicCompletion.Modules l E T) ℤ),
      (HomologicalComplex.quasiIso (AdicCompletion.Modules l E T) (.up ℤ)).kFlat P →
      IsIso (D.redCounit.app P)) ∧
    (∀ (P : CochainComplex (AdicCompletion.Modules l E T) ℤ),
      (HomologicalComplex.quasiIso (AdicCompletion.Modules l E T) (.up ℤ)).kFlat P →
      ∀ (m n : ℕ) (h : m ≤ n),
      IsIso ((D.scalar ((rings l E T).map (homOfLE h).op)).model.ε.app
        (((SheafOfModules.systemEvaluation (rings l E T) n).mapHomologicalComplex
          (.up ℤ)).obj ((D.ordinaryRed.mapHomologicalComplex (.up ℤ)).obj P)))) ∧
    ∀ (P : CochainComplex (Towers l E T) ℤ) (m n : ℕ) (h : m ≤ n),
      (D.reduction h).app (DerivedCategory.Q.obj P) =
        (SheafOfModules.systemDerivedTensor D.scalar (rings l E T) h).map
          ((SheafOfModules.systemEvaluation (rings l E T) n).mapDerivedCategoryFactors.hom.app P) ≫
        (D.scalar ((rings l E T).map (homOfLE h).op)).model.ε.app
          (((SheafOfModules.systemEvaluation (rings l E T) n).mapHomologicalComplex
            (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (ordinaryTransitionAdjunct l E T D h)
            (.up ℤ)).app P) ≫
        (SheafOfModules.systemEvaluation (rings l E T) m).mapDerivedCategoryFactors.inv.app P := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedIntegralTower
