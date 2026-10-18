/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Sheaf.AlgebraicGeometry.AbelianVariety.GeometricJacobianGaloisAction
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Category.Grp.Limits
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Final
import WeilConjectures.GroupTheory.TateModule

/-! # Integral first cohomology and the dual Tate module

Source: Weil conjectures blueprint, sec-purity-real-sheaves, sk-p-real-rankone,
equation (4.1) (blueprint: lem-wf-curve-h1-dual-tate-module).

## Main definitions

- `AlgebraicGeometry.curveH1CoefficientSystem`: coefficient reduction on integral H¹.

## Main statements

- `AlgebraicGeometry.exists_curveH1_dualTateModule`: the equivariant duality (4.1).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj

namespace AlgebraicGeometry

open Scheme

/-- The ordinary inverse system H¹(C, ℤ/ℓⁿ), with coefficient reduction as transition.
Source: blueprint sk-p-real-rankone, equation (4.1)
(blueprint: lem-wf-curve-h1-dual-tate-module).
The cohomology is `Sheaf.H`, the Ext model of the recorded `Etale.cohomology`.
Level zero is zero and does not alter the limit over positive levels. -/
noncomputable def curveH1CoefficientSystem (C : Scheme.{u}) (ℓ : ℕ) :
    ℕᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  Functor.ofOpSequence
    (X := fun n ↦ AddCommGrpCat.of (Sheaf.H (C.constantZMod (ℓ ^ n)) 1)) (fun n ↦
    AddCommGrpCat.ofHom (Sheaf.H.map
      ((constantSheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        ((AddCommGrpCat.uliftFunctor.{u + 1, 0}).map
          (AddCommGrpCat.ofHom
            (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_add_right n 1))
              (ZMod (ℓ ^ n))).toAddMonoidHom))) 1))

set_option linter.overlappingInstances false in
/-- Untwisted integral classes are the linear dual of the Jacobian Tate module.
Source: blueprint sk-p-real-rankone, equation (4.1)
(blueprint: lem-wf-curve-h1-dual-tate-module).

The first clause expresses ℤ_ℓ-linearity using the standard coordinatewise action:
the n-th coordinate of r x is multiplication by r modulo ℓⁿ. The second expresses
Galois equivariance as simultaneous invariance of evaluation. The cohomology action is
pullback along id × Spec sigma, and the point action is the canonical semilinear action
of `existsUnique_geometricJacobian_galoisAction`, twisted by Spec sigma on the source.
Thus evaluation is invariant, equivalently the action on the dual is contragredient.

Proof, following all six DAG steps:
1. `lem-wf-curve-finite-level-pd` supplies the perfect cup-trace pairing. Compose its
adjoint with the inverse of `lem-wf-curve-kummer-jacobian-tate-module` to obtain the
finite-level isomorphisms from H¹(C, ℤ/ℓⁿ) to the dual of J[ℓⁿ].
2. `lem-wf-curve-trace-cup-naturality` and the Kummer transition and equivariance clauses
show that these pairings commute with reduction and with every semilinear Galois action.
3. Divisibility in `thm-av-final` makes the torsion transition maps onto. Recursively
lift a torsion point to a compatible tuple to prove each Tate projection onto. Shifting
a tuple whose n-th coordinate vanishes proves its kernel is ℓⁿ times the Tate module.
4. Evaluate each finite pairing on the corresponding Tate coordinate. Compatibility
gives a p-adic integer; coordinatewise additivity and scalars give a linear functional.
Surjectivity of the projections and finite-level perfectness prove injectivity.
5. Conversely reduce a linear functional modulo ℓⁿ and descend through the Tate
projection, whose kernel was computed in step 3. Invert the finite-level pairings.
Their transition compatibility gives a tuple in the ordinary limit, inverse to step 4.
6. Galois invariance follows at every residue from step 2 and the componentwise Tate
action. Equality of residues gives invariance over ℤ_ℓ. All maps are the canonical
cup-trace, Kummer and projection maps; lifts are used only to prove surjectivity.
-/
theorem exists_curveH1_dualTateModule
    (k₀ K : Type u) [Field k₀] [Field K] [Algebra k₀ K]
    [IsAlgClosure k₀ K] [IsAlgClosed K]
    (C₀ : Scheme.{u}) [C₀.Over (Spec (.of k₀))]
    [SmoothOfRelativeDimension 1 (C₀ ↘ Spec (.of k₀))]
    [IsProper (C₀ ↘ Spec (.of k₀))]
    [GeometricallyConnected (C₀ ↘ Spec (.of k₀))]
    (C : Scheme.{u}) [C.Over (Spec (.of K))]
    [IsCurve (C ↘ Spec (.of K))] [Smooth (C ↘ Spec (.of K))]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (.of K))]
    [IsProper (C ↘ Spec (.of K))] [GeometricallyIntegral (C ↘ Spec (.of K))]
    (p : C ⟶ C₀)
    (hC : IsPullback p (C ↘ Spec (.of K)) (C₀ ↘ Spec (.of k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (J : Over (Spec (.of K))) [CommGrpObj J] [IsJacobian (C ↘ Spec (.of K)) J]
    (φ : (picardFunctorDegree (C ↘ Spec (.of K)) 0).obj.RepresentableBy J)
    (hφ : IsPicardZeroMul (C ↘ Spec (.of K)) φ)
    (ℓ : ℕ) [Fact ℓ.Prime] (c : ℕ) [CharP k₀ c] (hℓ : ℓ ≠ c) :
    ∃ e : ↥(limit (curveH1CoefficientSystem C ℓ)) ≃+
        (IsAbelianVariety.tateModule ℓ J →ₗ[ℤ_[ℓ]] ℤ_[ℓ]),
      (∀ (r : ℤ_[ℓ]) (x : ↥(limit (curveH1CoefficientSystem C ℓ))),
        ∃ x' : ↥(limit (curveH1CoefficientSystem C ℓ)),
          (∀ n : ℕ, limit.π (curveH1CoefficientSystem C ℓ) (.op n) x' =
            (r.toZModPow n).val • limit.π (curveH1CoefficientSystem C ℓ) (.op n) x) ∧
          e x' = r • e x) ∧
      ∀ (σ : K ≃ₐ[k₀] K) (γ : C ⟶ C), γ ≫ p = p →
        γ ≫ (C ↘ Spec (.of K)) = (C ↘ Spec (.of K)) ≫
          Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) →
        ∀ (x : ↥(limit (curveH1CoefficientSystem C ℓ))) (t : IsAbelianVariety.tateModule ℓ J),
          ∃ (x' : ↥(limit (curveH1CoefficientSystem C ℓ)))
            (t' : IsAbelianVariety.tateModule ℓ J),
            (∀ n : ℕ, limit.π (curveH1CoefficientSystem C ℓ) (.op n) x' =
              Sheaf.H.map
                (((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} γ).app
                  (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n))))).hom) 1
                (Etale.cohomologyMap γ (C.constantZMod (ℓ ^ n)) 1
                  (limit.π (curveH1CoefficientSystem C ℓ) (.op n) x))) ∧
            (∀ n : ℕ,
              ((IsAbelianVariety.pointsAddEquivGeometricPoints J).symm (t'.1 n)).toMul.left =
                Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫
                  ((IsAbelianVariety.pointsAddEquivGeometricPoints J).symm (t.1 n)).toMul.left ≫
                    ((Classical.choose
                      (existsUnique_geometricJacobian_galoisAction
                        k₀ K C₀ C p hC J φ hφ).exists) σ).hom) ∧
            e x' t' = e x t := by
  sorry

end AlgebraicGeometry
