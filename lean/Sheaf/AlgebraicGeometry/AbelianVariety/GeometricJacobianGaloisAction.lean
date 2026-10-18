/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule
import WeilConjectures.Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Functor.FullyFaithful
import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
import WeilConjectures.GroupTheory.TateModule

/-!
# The canonical semilinear action on a geometric Jacobian

Source: Weil conjectures blueprint, `sec-purity-real-sheaves`, `sk-d-real-jacobian`,
with the variance correction recorded in the DAG
(blueprint: lem-wf-geometric-jacobian-galois-action).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj

namespace AlgebraicGeometry

open Scheme

set_option linter.overlappingInstances false in
/-- The geometric Jacobian has a unique semilinear left Galois action relative to its fixed
representing isomorphism. Source: blueprint `sk-d-real-jacobian`, both proof paragraphs,
with the DAG's variance correction (blueprint: lem-wf-geometric-jacobian-galois-action).

Proof, following the six DAG steps:
1. `thm-pd-jacobian-general-field` supplies the ground-field Jacobian and its base change.
Use `def-sc-jacobian` and `lem-sc-jacobian-unique` to compare the fixed representation with
this base change. The comparison is characterized below on every test scheme and every
class before fppf sheafification, so no arbitrary representing comparison is substituted.
2. On the base change use identity on the model and `Spec (sigma inverse)` on the base.
Check the two projections to obtain the left action law and compatibility with multiplication,
identity and inverse in the semilinear sense.
3. Conjugate by the representing comparison. `lem-pc-representable-unique` makes the resulting
action independent of the model, since its comparison is over the ground field. This gives
the unique action asserted here.
4. Twist a point on the right by `Spec sigma`. Contravariance of Spec and the scheme action
law give the left point action. The comparison with model points is precomposition by
`specAlgEquivOver sigma`. The geometric-point equivariance clause of
`thm-pd-jacobian-general-field` identifies it with pullback of line bundles on the curve.
5. Restrict that one group isomorphism to every subgroup killed by a prime power. Its
additivity gives compatibility with multiplication by the prime, including in characteristic
that prime. Equivariance follows from the unrestricted point comparison.
6. `def-tate-module-abelian-group` gives the inverse limit. Act at each coordinate; additivity
preserves the torsion and transition equations, and commutation with integer multiplication
proves linearity over the compatible residue scalars in the p-adic integers. The canonical
point-to-geometric-point equivalence identifies this limit with
`def-wf-abelian-tate-module` when the prime differs from the characteristic.
-/
theorem existsUnique_geometricJacobian_galoisAction
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
    (hφ : IsPicardZeroMul (C ↘ Spec (.of K)) φ) :
    ∃! a : (σ : K ≃ₐ[k₀] K) →
        SemilinearGrpHom (Spec.map (CommRingCat.ofHom σ.symm.toAlgHom.toRingHom)) J J,
      (∀ σ, IsIso (a σ).hom) ∧
      (a 1).hom = 𝟙 J.left ∧
      (∀ σ τ, (a (σ * τ)).hom = (a τ).hom ≫ (a σ).hom) ∧
      ∃ (J₀ : Over (Spec (.of k₀))) (_ : CommGrpObj J₀)
        (r₀ : (picardFunctorDegree (C₀ ↘ Spec (.of k₀)) 0).obj.RepresentableBy J₀),
        IsPicardZeroMul (C₀ ↘ Spec (.of k₀)) r₀ ∧
        IsProper J₀.hom ∧
        SmoothOfRelativeDimension (arithmeticGenus k₀ C₀) J₀.hom ∧
        GeometricallyIntegral J₀.hom ∧
        ∃ (q : J.left ⟶ J₀.left)
          (hJ : IsPullback q J.hom J₀.hom
            (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))),
          (∀ (T : Over (Spec (.of K)))
            (L : (pullback (C₀ ↘ Spec (.of k₀))
              (T.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))).Pic)
            (hL : L ∈ (picardSubfunctorDegree (C₀ ↘ Spec (.of k₀)) 0).obj
              (.op ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))).obj T))),
            ∃ hLK : Pic.map (pullbackIsoOfIsPullback hC T).hom L ∈
                (picardSubfunctorDegree (C ↘ Spec (.of K)) 0).obj (.op T),
              (φ.homEquiv.symm ((toSheafify (Scheme.fppfTopology.over (Spec (.of K)))
                (picardSubfunctorDegree (C ↘ Spec (.of K)) 0).toFunctor).app (.op T)
                  ⟨Pic.map (pullbackIsoOfIsPullback hC T).hom L, hLK⟩)).left ≫ q =
              (r₀.homEquiv.symm ((toSheafify (Scheme.fppfTopology.over (Spec (.of k₀)))
                (picardSubfunctorDegree (C₀ ↘ Spec (.of k₀)) 0).toFunctor).app
                  (.op ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))).obj T))
                    ⟨L, hL⟩)).left) ∧
          (∀ σ, hJ.isoPullback.inv ≫ (a σ).hom ≫ hJ.isoPullback.hom =
            baseChangeMap J₀.hom (specAlgEquivOver σ.symm)) ∧
          ∃ (ρ : (K ≃ₐ[k₀] K) →*
                Multiplicative (AddAut (Additive (𝟙_ (Over (Spec (.of K))) ⟶ J))))
            (Φ : Additive (picardZero K C) ≃+
              Additive (𝟙_ (Over (Spec (.of K))) ⟶ J))
            (Φ₀ : Additive (picardZero K C) ≃+ Additive
              (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) ⟶ J₀)),
            (∀ σ x, ((ρ σ).toAdd x).toMul.left =
              Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫
                x.toMul.left ≫ (a σ).hom) ∧
            (∀ L : Additive (picardZero K C), ∃ hL,
              φ.homEquiv (Φ L).toMul =
                (toSheafify (Scheme.fppfTopology.over (Spec (.of K)))
                  (picardSubfunctorDegree (C ↘ Spec (.of K)) 0).toFunctor).app
                    (.op (𝟙_ (Over (Spec (.of K)))))
                    ⟨Pic.map (pullback.fst (C ↘ Spec (.of K))
                      (𝟙_ (Over (Spec (.of K)))).hom) L.toMul.1, hL⟩) ∧
            (∀ L, (Φ₀ L).toMul.left = (Φ L).toMul.left ≫ q) ∧
            (∀ σ L, (Φ₀ (Φ.symm ((ρ σ).toAdd (Φ L)))).toMul =
              specAlgEquivOver σ ≫ (Φ₀ L).toMul) ∧
            (∀ σ, ∃ γ : C ⟶ C, γ ≫ p = p ∧
              γ ≫ (C ↘ Spec (.of K)) = (C ↘ Spec (.of K)) ≫
                Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ∧
              ∀ L, (Φ.symm ((ρ σ).toAdd (Φ L))).toMul.1 = Pic.map γ L.toMul.1) ∧
            (∀ (ℓ : ℕ) (_ : Fact ℓ.Prime) (n : ℕ), 1 ≤ n →
              ∃ e : AddSubgroup.torsionBy (Additive
                  (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) ⟶ J₀))
                    ((ℓ : ℤ) ^ n) ≃+
                AddSubgroup.torsionBy (Additive (picardZero K C)) ((ℓ : ℤ) ^ n),
                (∀ z, (e z).1 = Φ₀.symm z.1) ∧
                (∀ σ z z', z'.1.toMul = specAlgEquivOver σ ≫ z.1.toMul →
                  Φ ((e z').1) = (ρ σ).toAdd (Φ ((e z).1))) ∧
                ∀ (z : AddSubgroup.torsionBy (Additive
                    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) ⟶ J₀))
                      ((ℓ : ℤ) ^ (n + 1)))
                  (z' : AddSubgroup.torsionBy (Additive
                    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) ⟶ J₀))
                      ((ℓ : ℤ) ^ n)),
                  z'.1 = (ℓ : ℤ) • z.1 → (e z').1 = (ℓ : ℤ) • Φ₀.symm z.1) ∧
            ∀ (ℓ : ℕ) [Fact ℓ.Prime],
              ∃ R : (K ≃ₐ[k₀] K) →*
                  (AddCommGroup.tateModule ℓ
                    (Additive (𝟙_ (Over (Spec (.of K))) ⟶ J)) ≃ₗ[ℤ_[ℓ]]
                   AddCommGroup.tateModule ℓ
                    (Additive (𝟙_ (Over (Spec (.of K))) ⟶ J))),
                (∀ σ t n, (R σ t).1 n = (ρ σ).toAdd (t.1 n)) ∧
                ∀ (c : ℕ) [CharP k₀ c], ℓ ≠ c →
                  ∃ R' : (K ≃ₐ[k₀] K) →*
                      (IsAbelianVariety.tateModule ℓ J ≃ₗ[ℤ_[ℓ]]
                        IsAbelianVariety.tateModule ℓ J),
                    ∀ σ t, R' σ (AddCommGroup.tateModule.congr
                      (IsAbelianVariety.pointsAddEquivGeometricPoints J) t) =
                        AddCommGroup.tateModule.congr
                          (IsAbelianVariety.pointsAddEquivGeometricPoints J) (R σ t) := by
  sorry

end AlgebraicGeometry
