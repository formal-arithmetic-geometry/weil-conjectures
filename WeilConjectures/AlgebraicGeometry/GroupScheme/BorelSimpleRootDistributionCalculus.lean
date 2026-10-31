/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import WeilConjectures.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations
public import WeilConjectures.AlgebraicGeometry.GroupScheme.AffineGroupDistributionCalculus
public import Mathlib.Data.Finset.NatAntidiagonal

/-! # Simple-root distributions and the infinitesimal subalgebra

Source: Mathieu, Tilting Modules and their Applications (2000), Section 1,
printed pp.150--152; Lemma 2.3, printed p.155, with positive roots.
(blueprint: lem-sfb-borel-simple-root-distribution-calculus)

The equalities are in the faithful inclusion into the full convolution dual.
Generation identifies its finite-order subset with a unital subalgebra, so no
closure property of distributions is assumed as additional data.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj TensorProduct

namespace AlgebraicGeometry.BorelDistributions

/-- Simple-root divided powers generate the distributions of the Borel radical.
The infinitesimal subalgebra is stable under the canonical rational conjugation
and satisfies the divided-power commutation identity on all rational modules.
Each simple parametrization is a closed immersion onto a T-stable smooth connected
subgroup with tangent space the root space; by the uniqueness in
lem-sfb-reductive-root-subgroup-parametrizations this is an isomorphism onto U_alpha.

Source: Mathieu, Section 1, pp.150--152; Lemma 2.3, p.155.
(blueprint: lem-sfb-borel-simple-root-distribution-calculus)

Proof plan:
1. Apply lem-sfb-borel-kostant-distribution-comparison, extending the prescribed
   simple parametrizations to all positive roots. Use
   lem-sfb-borel-root-product-coordinates: ordered products identify the coordinate
   ring with a polynomial ring and its augmentation ideal with the variable ideal.
   Ordered products of coefficient distributions are the dual monomial basis of
   every finite jet quotient. Hence the Kostant comparison is surjective.
2. Apply lem-sfb-positive-kostant-simple-divided-generation before reduction to F.
   Images of its simple divided powers generate the entire distribution algebra;
   no bad-prime root-string constant is inverted.
3. The additive root group law gives D(a)D(b)=choose(a+b,a)D(a+b). Coefficients
   of degree one in a product show that D(1) is an augmentation derivation.
   Induction gives e^b=b!D(b); for b<p the factorial is invertible, including b=0.
4. Conjugation preserves the augmentation ideal and each of its powers. Each jet
   quotient is finite dimensional by the root coordinates. Its dual action is
   polynomial with a finite expansion. Conjugation preserves the derivation
   identity coefficientwise; multiplying these expansions proves stability of A.
   The group law gives coassociativity and the identity gives the counit law.
5. Apply a in the middle variable to the polynomial group identity
   x(t)v=(x(t)v x(-t))x(t), and compare the coefficient of t^n. This gives exactly
   the antidiagonal sum, in the indicated multiplication order. Coassociativity
   of any rational module coaction gives its convolution action, so the same
   identity holds on modules without a dimension restriction.
6. For an empty simple base the positive roots are empty. Root-product coordinates
   identify U with the trivial group, its coordinate ring with F, and its
   augmentation ideal and derivation space with zero. Thus H=A=F. -/
theorem borel_simple_root_distribution_calculus
    (F : Type u) [Field F] [IsAlgClosed F]
    (S T B : Grp (Over (Spec (.of F))))
    (U : Scheme.{u}) [U.Over (Spec (.of F))]
    [GrpObj (U.asOver (Spec (.of F)))] [IsAffine U]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (hS : IsSemisimpleGroupScheme S.X)
    (hsc : ∀ (S' : Over (Spec (.of F))) [GrpObj S'],
      IsSemisimpleGroupScheme S' → ∀ (f : S' ⟶ S.X) [IsMonHom f],
      Surjective f.left → IsFinite (GrpObj.ker f).hom →
      (∀ (A : Type u) [CommRing A] [Algebra F A]
        (x : StandardGroupSchemes.affine F A ⟶ GrpObj.ker f)
        (s : StandardGroupSchemes.affine F A ⟶ S'),
        (x ≫ GrpObj.kerι f) * s = s * (x ≫ GrpObj.kerι f)) → IsIso f)
    (iT : T ⟶ S) (iB : B ⟶ S) (jT : T ⟶ B) (iU : Grp.mk (U.asOver (Spec (.of F))) ⟶ B)
    (hTB : jT ≫ iB = iT)
    (hT : ReductiveTorusCentralizer.IsMaximalTorus iT)
    (hsplit : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    (hB : IsBorelGroupScheme iB.hom.hom)
    (hU : IsClosedSubgroupScheme iU.hom.hom ∧ IsNormalSubgroupScheme iU.hom.hom ∧
      Smooth (U ↘ Spec (.of F)) ∧ ConnectedSpace U ∧
      SolvableGroupStructure.IsUnipotent (Grp.mk (U.asOver (Spec (.of F)))) ∧
      ∀ (N : Grp (Over (Spec (.of F)))) (iN : N ⟶ B),
        IsClosedSubgroupScheme iN.hom.hom → IsNormalSubgroupScheme iN.hom.hom →
        Smooth N.X.hom → ConnectedSpace N.X.left → SolvableGroupStructure.IsUnipotent N →
        ∃ f : N ⟶ Grp.mk (U.asOver (Spec (.of F))), f ≫ iU = iN)
    [IsCommMonObj T.X] [IsCommMonObj (StandardGroupSchemes.multiplicative F)]
    [ModObj T.X S.X] [ModObj T.X B.X]
    (hconjS : γ[T.X,S.X] = (iT.hom.hom ⊗ₘ 𝟙 S.X) ≫ GrpObj.conj S.X)
    (hconjB : γ[T.X,B.X] = (jT.hom.hom ⊗ₘ 𝟙 B.X) ≫ GrpObj.conj B.X)
    (Φ : Finset (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))))
    (P : RootDatum Φ
      (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)))
    [P.IsReduced] (b : P.Base)
    (hroot : ∀ α : Φ, P.root α = α.val)
    (hpair : ∀ (χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (ν : Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)),
      ν.toMul.hom.hom ≫ χ.toMul.hom.hom =
        (𝟙 (StandardGroupSchemes.multiplicative F)) ^ (P.toLinearMap χ ν))
    (hweights : ∀ χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
      χ ∈ Φ ↔ χ ≠ 0 ∧ TorusCharacterTangent.weightSpace T S χ.toMul ≠ ⊥)
    (hpos : ∀ α : Φ, b.IsPos α ↔
      TorusCharacterTangent.weightSpace T B α.val.toMul ≠ ⊥)
    (πT : B ⟶ T) (hπT : jT ≫ πT = 𝟙 T)
    (hker : IsPullback iU.hom.hom (toUnit (U.asOver (Spec (.of F))))
      πT.hom.hom η[T.X])
    (hsd : IsIso ((fst (U.asOver (Spec (.of F))) T.X ≫ iU.hom.hom) *
      (snd (U.asOver (Spec (.of F))) T.X ≫ jT.hom.hom)))
    (x : ∀ _ : b.support, Grp.mk (StandardGroupSchemes.additive F) ⟶
      Grp.mk (U.asOver (Spec (.of F))))
    (hx : ∀ α : b.support,
      IsClosedImmersion ((x α).hom.hom ≫ iU.hom.hom ≫ iB.hom.hom).left ∧
      TorusCharacterTangent.IsStable T S (x α ≫ iU ≫ iB) ∧
      (GrpObj.differential ((x α).hom.hom ≫ iU.hom.hom ≫ iB.hom.hom)).toLinearMap.range =
        TorusCharacterTangent.weightSpace T S α.val.val.toMul) :
    {a : fullDual (.of F) U | finiteOrder (.of F) U a} =
      (Algebra.adjoin F (Set.range (fun z : b.support × ℕ ↦
        dividedPower (.of F) U (x z.1).hom.hom z.2)) : Set (fullDual (.of F) U)) ∧
    (∀ i : b.support, tangent (.of F) U (dividedPower (.of F) U (x i).hom.hom 1)) ∧
    (∀ (i : b.support) (m : ℕ), m < p →
      dividedPower (.of F) U (x i).hom.hom m =
        ((m.factorial : F)⁻¹) • (dividedPower (.of F) U (x i).hom.hom 1) ^ m ∧
      dividedPower (.of F) U (x i).hom.hom m ∈ infinitesimalAlgebra (.of F) U) ∧
    (∀ i : b.support,
      (∃ cA : infinitesimalAlgebra (.of F) U →ₗ[F]
          infinitesimalAlgebra (.of F) U ⊗[F] Polynomial F,
        IsAdditiveCoaction (.of F) cA ∧
        ∀ (a : infinitesimalAlgebra (.of F) U) (f : Γ(U, ⊤)),
          evaluatePolynomialTensor (.of F) U f
              (TensorProduct.map (infinitesimalAlgebra (.of F) U).val.toLinearMap
                LinearMap.id (cA a)) =
            conjugationPolynomial (.of F) U (x i).hom.hom a.val f) ∧
      ∀ a : infinitesimalAlgebra (.of F) U,
        (∃ N : ℕ, ∀ r : ℕ, N < r →
          conjugationCoefficient (.of F) U (x i).hom.hom a.val r = 0) ∧
        (∀ r : ℕ, conjugationCoefficient (.of F) U (x i).hom.hom a.val r ∈
          infinitesimalAlgebra (.of F) U) ∧
        ∀ n : ℕ, dividedPower (.of F) U (x i).hom.hom n * a.val =
          ∑ rb ∈ Finset.antidiagonal n,
            conjugationCoefficient (.of F) U (x i).hom.hom a.val rb.1 *
              dividedPower (.of F) U (x i).hom.hom rb.2) ∧
    (∀ (M : Type v) [AddCommGroup M] [Module F M]
      (c : M →ₗ[F] M ⊗[F] Γ(U, ⊤)), IsCoordinateCoaction (.of F) U c →
      ∀ (i : b.support) (a : infinitesimalAlgebra (.of F) U) (n : ℕ),
        moduleAction (.of F) U c (dividedPower (.of F) U (x i).hom.hom n * a.val) =
          ∑ rb ∈ Finset.antidiagonal n,
            (moduleAction (.of F) U c
              (conjugationCoefficient (.of F) U (x i).hom.hom a.val rb.1)).comp
              (moduleAction (.of F) U c (dividedPower (.of F) U (x i).hom.hom rb.2))) ∧
    (IsEmpty b.support →
      Nonempty (Grp.mk (U.asOver (Spec (.of F))) ≅ Grp.trivial (Over (Spec (.of F)))) ∧
      {a : fullDual (.of F) U | finiteOrder (.of F) U a} =
        Set.range (algebraMap F (fullDual (.of F) U)) ∧
      infinitesimalAlgebra (.of F) U = ⊥) := by
  sorry

end AlgebraicGeometry.BorelDistributions
