/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcAutomorphismLocalComplex
public import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.LevelwiseAdicTruncations

/-! Compatible finite reductions of the transported local complex. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable {X Y U : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
  {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (g : U ⟶ Y)

/-- The relabeled local complex computes the reductions of ordinary pullback, and
these identifications intertwine every comparable pair of levels.
Source: blueprint order 2106, preservation clause; Stacks Tags 06YY and 09BT.
Proof: restrict the source level comparison along g, then compose its local-model
identification with the derived scalar-change comparison for the square of completed
and finite coefficient isomorphisms. In the other direction the composition comparison
for inverse images and g followed by the inverse of f identifies restriction of the
ordinary pullback with restriction along g. These give the stated identification at
each level. For compatibility take the adjuncts under scalar extension and restriction.
The projection square identifies their units, while naturality moves the source level
comparison through the units. The source comparison equation and the local model's
compatibility equation then identify both composites. The mate construction uses the
same normalized scalar adjunctions as adicTowerLocalTransition, so it works for arbitrary
comparable indices, including equal indices, without choosing new transition maps.
(blueprint: lem-wf-pbc-automorphism-local-reduction-comparison). -/
theorem pbcIsoLocalComplex_reduction_comparison
    (K : PbcCompletedDerived Y d) (M : AdicTower Y d)
    (eK : ∀ n, M.level n ≅ (pbcCompletedReduction Y d n).obj K)
    (heK : ∀ (b a : ℕ) (hab : a ≤ b),
      adicTowerSemilinearTransition Y d M.level M.normalization b a hab ≫
          (pbcDerivedRestrict (pbcAdicQuotient Y d b a hab)).map (eK a).hom =
        (eK b).hom ≫ pbcReductionTransition (pbcAdicProjection Y d b)
          (pbcAdicQuotient Y d b a hab) (pbcAdicProjection Y d a)
          (pbcAdicProjection_comp Y d b a hab) K)
    (a b : ℤ) (L : AdicTowerLocalModel d g M a b) :
    ∃ e : ∀ n : ℕ,
      (adicTowerPullback (g ≫ inv f) ((pbcAdicRings X d).obj (op n))).obj
          ((pbcReductionAdicTower X d ((completedOrdinaryPullback f d).obj K)).level n) ≅
        adicTowerLocalReduction d (g ≫ inv f) (pbcIsoLocalComplex f d g L.complex) n,
      ∀ (j i : ℕ) (hij : i ≤ j),
        adicTowerRestrictedTransition d (g ≫ inv f)
            (pbcReductionAdicTower X d ((completedOrdinaryPullback f d).obj K)) j i hij ≫
          (pbcDerivedRestrict ((adicTowerInverseImage (g ≫ inv f)).map
            (pbcAdicQuotient X d j i hij))).map (e i).hom =
        (e j).hom ≫ adicTowerLocalTransition d (g ≫ inv f)
          (pbcIsoLocalComplex f d g L.complex) j i hij := by
  sorry

end AlgebraicGeometry.Scheme
