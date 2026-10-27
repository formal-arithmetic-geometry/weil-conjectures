/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Sheaf.Paper.SmoothPurityReductionTowerData


/-! # Constructible cohomology of the evaluated strict reductions

Source: blueprint latest, normalized-towers-reduction, constructibility paragraph;
Stacks Tags 093M, 093U, 06YY, 08J5.
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

/-- Evaluated reductions of a bounded constructible integral complex have
constructible cohomology. Only constructibility is asserted, without any Tor bound
or normalization condition on a tower.

Source: blueprint latest, sec-smooth-purity, normalized-towers-reduction,
constructibility paragraph; Stacks Tags 093M, 093U(3), 06YY, 08J5
(blueprint: lem-sp-reduction-tower-level-constructibility).

Proof:
1. Boundedness leaves finitely many nonzero integral cohomology sheaves. On a qcqs
scheme their finite constructible stratifications have a common finite refinement
by constructible-stratification-intersection. Refined strata are actual fiber
products of the original strata. PullbackFiniteConstantLocalModel transports the
finite constant models to this refinement; the zero sheaves have the zero model.
2. The normalized coefficient isomorphism and the section/internal equivalence
identify these models with the finite scalar constant models over the completed
section ring. Transport the site to a small skeleton if required by the matrix
lemma, preserving the ring, its scalar map, and all quotient projections.
3. Apply integral_local_model_finite_matrix_reduction on each stratum. A finite
presentation over the DVR has finite free kernel, giving a two-term finite free
matrix resolution. Flatness of completed coefficients over constant integers and
K-flat computation reduce it by the same matrix modulo ell^(n+1). Its kernels
and cokernels are finite modules over the finite scalar quotient ring.
4. Apply sp_stratified_reduction_postnikov_comparison to the refined partition.
Its coefficient-preserving inverse-image comparison and images of the finite
truncation triangles give locally constant finite-type cohomology on every stratum.
The same partition works for every level and every degree; finite scalar modules
have finite geometric stalks. This is exactly IsConstructibleProEtaleModuleSheaf.
5. Uniqueness of derived scalar extension identifies that lemma's reduction with
the specified evaluation via evaluation. Homology preserves this isomorphism and
constructibility is invariant under isomorphism, proving the conclusion.
For the zero object take the one-stratum partition; empty schemes have vacuous
stalk conditions. Reduction is not interchanged with truncation.
-/
theorem sp_reduction_tower_level_constructibility
    (D : SpCoefficientTowersAbelian l E T)
    (coefficient : spIntegralSectionRing l E T ≅
      WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T)
    (coefficient_normalized : ∀ (U : T.ProEtᵒᵖ)
      (x : (condensedRingObj (spIntegralCondensed l E) T).obj.obj U),
      coefficient.hom.hom.app U x = (spIntegralAbComparison l E T).hom.hom.app U x)
    (red : DerivedCategory (spIntegralSectionModules l E T) ⥤
      spDerivedCoefficientTowers l E T D)
    (evaluation : spReductionDerivedEvaluations l E T D coefficient red)
    [CompactSpace T] [QuasiSeparatedSpace T]
    (M : DerivedCategory (spIntegralSectionModules l E T))
    (hM : constantModelBoundedConstructible (spIntegralCondensed l E) T
      ((spIntegralInternalization l E T).obj M)) :
    ∀ (n : ℕ) (i : ℤ), Scheme.IsConstructibleProEtaleModuleSheaf T
      (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))
      ((@DerivedCategory.homologyFunctor
        (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T
          (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))))
        _ _ (HasDerivedCategory.standard _) i).obj
        ((spDerivedCoefficientEvaluation l E T D n).obj (red.obj M))) := by sorry

end AlgebraicGeometry.ProEtale
