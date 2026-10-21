/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q77
-/
module

public import Sheaf.AlgebraicGeometry.AbelianVariety.GeometricJacobianGaloisAction
public import Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Sheaf.Paper.FiniteTateSiteDescent
import Sheaf.Paper.IntrinsicCoefficientTwists
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Sheaf.Paper.RingedTopoiDerivedTensorPullback
import Sheaf.AlgebraicGeometry.GmPicardPullback
import WeilConjectures.AlgebraicGeometry.PullbackCohomologyLongExactLadder
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.CategoryTheory.Sites.Torsor
import WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule
import WeilConjectures.AlgebraicGeometry.Curve
import WeilConjectures.AlgebraicGeometry.Sites.Gm

/-! # Kummer comparison with the geometric Jacobian

Source: Weil conjectures blueprint, sec-purity-real-sheaves, sk-d-real-jacobian,
order 2610 (blueprint: lem-wf-curve-kummer-jacobian-tate-module).

We use the statement's canonical model of A_n(1) as nu-star mu, with its
specified comparison from finite Tate descent. Both sites' cohomology groups
appear below. The index n denotes the positive level n + 1.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj

namespace AlgebraicGeometry

open Scheme

set_option linter.overlappingInstances false in
/-- The canonical finite Kummer isomorphisms, their transitions and Galois equivariance.
Source: blueprint sk-d-real-jacobian, order 2610
(blueprint: lem-wf-curve-kummer-jacobian-tate-module).

The normalization of Phi uses the fixed representing comparison phi. The normalization
of alpha uses H^1 of the Kummer inclusion, followed by the canonical Picard comparison.
The next clause states naturality for any curve pullback compatible with these data.
The transition p is
characterized by its composite with the monic Kummer inclusion, hence is the power map.
Likewise the roots-of-unity pullback comparison q is characterized on local units.
The final clause gives the pro-etale form, using A_n(1) = nu-star mu as in the statement.

Proof, following all seven DAG steps:
1. Specialize finite_tate_site_descent to Q_l, uniformizer l and exponent n+1.
The etale tensor mu tensor A_n is canonically mu by scalar multiplication.
Use comparisonCohomologyMap_bijective to pass between the two sites.
2. Apply pullbackCohomology_longExact_ladder at the identity to the exact Kummer
sequence. H^1 of its inclusion maps to H^1(G_m), canonically Pic(C), and its
power endomorphism induces tensor power on line bundles.
3. GlobalSectionsBijective.of_isAlgClosed identifies global functions with K.
The degree-zero cohomology comparison identifies global units with K-units.
Every nonzero element has an l^(n+1)-th root, so multiplication on H^0 is onto.
Exactness identifies H^1(mu) with the torsion subgroup of Pic(C).
4. Degree maps torsion to zero in the torsion-free group of integers. Thus all
these torsion classes lie in Pic^0. Use the fixed representing comparison in
existsUnique_geometricJacobian_galoisAction to obtain Phi and restrict its inverse.
5. The Kummer sequences at adjacent levels have vertical maps (power-l, [l], id).
Their first square gives precisely the stated transition equality after H^1.
6. Pullback of roots of unity commutes with the inclusion into local units.
Cohomology pullback naturality and picard_cohomology_pullback identify its action
with pullback of line bundles. The geometric Jacobian theorem identifies this
with the specified semilinear point action. The two contravariances give a left action.
7. Transport alpha through the canonical site comparison to obtain alphaPro.
Compatibility of finite Tate descent with pullback and powers preserves both equations.
These finite transitions are exactly the system in IsAbelianVariety.tateModule;
no interchange of cohomology with an inverse limit is asserted or used. -/
theorem exists_curve_kummer_jacobian_tate_comparison
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
    ∃ Φ : Additive (picardZero K C) ≃+
        Additive (𝟙_ (Over (Spec (.of K))) ⟶ J),
      (∀ L : Additive (picardZero K C), ∃ hL,
        φ.homEquiv (Φ L).toMul =
          (toSheafify (Scheme.fppfTopology.over (Spec (.of K)))
            (picardSubfunctorDegree (C ↘ Spec (.of K)) 0).toFunctor).app
              (.op (𝟙_ (Over (Spec (.of K)))))
              ⟨Pic.map (pullback.fst (C ↘ Spec (.of K))
                (𝟙_ (Over (Spec (.of K)))).hom) L.toMul.1, hL⟩) ∧
      ∃ α : ∀ n : ℕ, Sheaf.H (C.rootsOfUnitySheaf (ℓ ^ (n + 1))) 1 ≃+
          AddSubgroup.torsionBy
            (Additive (𝟙_ (Over (Spec (.of K))) ⟶ J)) ((ℓ : ℤ) ^ (n + 1)),
        (∀ (n : ℕ) (x : Sheaf.H (C.rootsOfUnitySheaf (ℓ ^ (n + 1))) 1),
          (Φ.symm (α n x).1).toMul.1 =
            (Pic.toCohomologicalPicardGroup C).symm
              (Sheaf.H.map (kernel.ι ((ℓ ^ (n + 1)) • 𝟙 C.gmSheaf)) 1 x)) ∧
        (∀ (D : Scheme.{u}) [D.Over (Spec (.of K))]
          [IsCurve (D ↘ Spec (.of K))] [Smooth (D ↘ Spec (.of K))]
          [SmoothOfRelativeDimension 1 (D ↘ Spec (.of K))]
          [IsProper (D ↘ Spec (.of K))] [GeometricallyIntegral (D ↘ Spec (.of K))]
          (J' : Over (Spec (.of K))) [CommGrpObj J'] [IsJacobian (D ↘ Spec (.of K)) J']
          (Φ' : Additive (picardZero K D) ≃+ Additive (𝟙_ (Over (Spec (.of K))) ⟶ J'))
          (α' : ∀ n : ℕ, Sheaf.H (D.rootsOfUnitySheaf (ℓ ^ (n + 1))) 1 ≃+
            AddSubgroup.torsionBy
              (Additive (𝟙_ (Over (Spec (.of K))) ⟶ J')) ((ℓ : ℤ) ^ (n + 1))),
          (∀ (n : ℕ) (x : Sheaf.H (D.rootsOfUnitySheaf (ℓ ^ (n + 1))) 1),
            (Φ'.symm (α' n x).1).toMul.1 =
              (Pic.toCohomologicalPicardGroup D).symm
                (Sheaf.H.map (kernel.ι ((ℓ ^ (n + 1)) • 𝟙 D.gmSheaf)) 1 x)) →
          ∀ (g : D ⟶ C)
            (j : Additive (𝟙_ (Over (Spec (.of K))) ⟶ J) →+
              Additive (𝟙_ (Over (Spec (.of K))) ⟶ J')),
            (∀ L : Additive (picardZero K C),
              (Φ'.symm (j (Φ L))).toMul.1 = Pic.map g L.toMul.1) →
            ∀ n : ℕ, ∃ q : (Etale.upperStar AddCommGrpCat.{u + 1} g).obj
                (C.rootsOfUnitySheaf (ℓ ^ (n + 1))) ≅ D.rootsOfUnitySheaf (ℓ ^ (n + 1)),
              q.hom ≫ kernel.ι ((ℓ ^ (n + 1)) • 𝟙 D.gmSheaf) =
                (Etale.upperStar AddCommGrpCat.{u + 1} g).map
                  (kernel.ι ((ℓ ^ (n + 1)) • 𝟙 C.gmSheaf)) ≫
                    upperStarGmSheafToGmSheaf g ∧
              ∀ x : Sheaf.H (C.rootsOfUnitySheaf (ℓ ^ (n + 1))) 1,
                (α' n (Sheaf.H.map q.hom 1
                  (Etale.cohomologyMap g (C.rootsOfUnitySheaf (ℓ ^ (n + 1))) 1 x))).1 =
                    j (α n x).1) ∧
        (∀ n : ℕ, ∃ pₙ : C.rootsOfUnitySheaf (ℓ ^ (n + 2)) ⟶
            C.rootsOfUnitySheaf (ℓ ^ (n + 1)),
          pₙ ≫ kernel.ι ((ℓ ^ (n + 1)) • 𝟙 C.gmSheaf) =
            ℓ • kernel.ι ((ℓ ^ (n + 2)) • 𝟙 C.gmSheaf) ∧
          ∀ x : Sheaf.H (C.rootsOfUnitySheaf (ℓ ^ (n + 2))) 1,
            (α n (Sheaf.H.map pₙ 1 x)).1 = (ℓ : ℤ) • (α (n + 1) x).1) ∧
        (∀ (σ : K ≃ₐ[k₀] K) (g : C ⟶ C), g ≫ p = p →
          g ≫ (C ↘ Spec (.of K)) = (C ↘ Spec (.of K)) ≫
            Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) →
          ∀ n : ℕ, ∃ q : (Etale.upperStar AddCommGrpCat.{u + 1} g).obj
              (C.rootsOfUnitySheaf (ℓ ^ (n + 1))) ≅ C.rootsOfUnitySheaf (ℓ ^ (n + 1)),
            q.hom ≫ kernel.ι ((ℓ ^ (n + 1)) • 𝟙 C.gmSheaf) =
              (Etale.upperStar AddCommGrpCat.{u + 1} g).map
                (kernel.ι ((ℓ ^ (n + 1)) • 𝟙 C.gmSheaf)) ≫
                  upperStarGmSheafToGmSheaf g ∧
            ∀ x : Sheaf.H (C.rootsOfUnitySheaf (ℓ ^ (n + 1))) 1,
              (α n (Sheaf.H.map q.hom 1
                (Etale.cohomologyMap g (C.rootsOfUnitySheaf (ℓ ^ (n + 1))) 1 x))).1.toMul.left =
                Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫
                  (α n x).1.toMul.left ≫
                    ((Classical.choose
                      (existsUnique_geometricJacobian_galoisAction
                        k₀ K C₀ C p hC J φ hφ).exists) σ).hom) ∧
        ∃ αPro : ∀ n : ℕ, Sheaf.H
            ((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} C).obj
              (C.rootsOfUnitySheaf (ℓ ^ (n + 1)))) 1 ≃+
            AddSubgroup.torsionBy
              (Additive (𝟙_ (Over (Spec (.of K))) ⟶ J)) ((ℓ : ℤ) ^ (n + 1)),
          ∀ (n : ℕ) (x : Sheaf.H (C.rootsOfUnitySheaf (ℓ ^ (n + 1))) 1),
            αPro n (ProEtale.comparisonCohomologyMap C
              (C.rootsOfUnitySheaf (ℓ ^ (n + 1))) 1 x) = α n x := by
  sorry

end AlgebraicGeometry
