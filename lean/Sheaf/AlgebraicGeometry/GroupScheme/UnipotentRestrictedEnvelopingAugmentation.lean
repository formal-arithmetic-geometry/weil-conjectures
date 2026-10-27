module

public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import Sheaf.AlgebraicGeometry.GroupScheme.AffineGroupDistributionCalculus
public import Sheaf.Algebra.Lie.RestrictedEnvelopingAlgebra
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections
import Sheaf.Algebra.Lie.RestrictedPBWBasis

/-! # The restricted enveloping algebra of a Borel unipotent radical

Source: Milne, Algebraic Groups (2017), Theorem 10.40, Sections 10l and 11h,
Theorem 21.11 and Sections 21.29--21.32; Mathieu, Section 1, pp.148--152.
(blueprint: lem-sfb-unipotent-restricted-enveloping-augmentation)

The tangent functionals are characterized by the actual dual-number tangent points.
The p-operation is characterized by iteration of the corresponding invariant operators.
The algebra is the existing tensor quotient, and the augmentation and module actions
are characterized on its generators. All these maps are conclusions, not hypotheses.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj TensorProduct

namespace AlgebraicGeometry.BorelDistributions

/-- The left-invariant operator `(id tensor a) Delta` associated with a coordinate functional:
the existing differentiated action `moduleAction` of def-sfb-affine-group-distribution-calculus
for the regular coaction `Delta` of the coordinate ring on itself.
Source: Milne, Section 11h, p.223.
(blueprint: lem-sfb-unipotent-restricted-enveloping-augmentation) -/
abbrev leftInvariantOperator (F : Type u) [Field F] (U : Scheme.{u})
    [U.Over (Spec (.of F))] [GrpObj (U.asOver (Spec (.of F)))] [IsAffine U]
    (a : fullDual (.of F) U) : Module.End F Γ(U, ⊤) :=
  moduleAction (.of F) U Coalgebra.comul a

/-- The restricted enveloping algebra of the radical has dimension `p^N`, nilpotent
augmentation ideal, and the canonical differentiated action on every rational module.
The empty positive-root system and the trivial radical are included.
Source: Milne, Theorem 10.40 and Corollary 10.41, p.207; Section 10l, pp.207--208;
Section 11h, p.223; Theorem 21.11 and Sections 21.29--21.32, pp.428--435.
Mathieu, Section 1, pp.148--152.
(blueprint: lem-sfb-unipotent-restricted-enveloping-augmentation)

Proof plan:
1. Use lem-sfb-reductive-borel-pair-structure and
   lem-sfb-regular-cocharacter-borel-description to choose a regular cocharacter
   positive on the Borel roots. The differential of the projection to T is identity
   on Lie(T) and kills all nonzero character spaces, by comparison of Laurent
   monomials. Thus Lie(U) is the sum of the positive-root spaces. By
   lem-sfb-reductive-rank-one-reflections each is one dimensional; choose an
   ordered basis e_alpha indexed by the N positive roots.
2. Apply lem-sfb-restricted-rational-differentiation. The tangent functionals are
   the epsilon coefficients of the actual dual-number tangent points, and their
   left-invariant operators determine the restricted operation by pth iteration.
   Torus conjugation preserves it. Hence e_alpha^[p] has character p alpha,
   which is not a root by reducedness, and is zero. Brackets have character
   alpha+beta. Character comparisons, not differentials, work also at bad primes.
3. Apply lem-sfb-restricted-pbw-basis. The ordered monomials with exponents less
   than p form a basis; their number is p^N. Basis bracket and p-relations
   generate the defining tensor ideal.
4. Grade each e_alpha by the positive integer d_alpha given by the cocharacter.
   The bracket relations and e_alpha^p=0 are homogeneous. The tensor quotient
   therefore has a nonnegative grading. Its homogeneous PBW basis has degrees
   at most D=(p-1) sum d_alpha; degree zero is precisely the scalars.
5. Sending every generator to zero kills all relations, giving the augmentation.
   Its kernel is the positive-degree part. Every product of D+1 such elements
   vanishes, so its ideal power is zero with h=D+1>=1. For a trivial radical,
   the Lie algebra is zero, the tensor quotient is F, and the kernel is zero.
6. For an arbitrary rational coaction apply
   lem-sfb-restricted-rational-differentiation: `(id tensor x) alpha` preserves
   brackets and sends x^[p] to the pth operator power. The tensor universal
   property and quotient give the stated unital algebra action. No finiteness
   restriction is imposed on the module. -/
theorem unipotent_restricted_enveloping_augmentation
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
    : ∃ (d : GrpObj.Lie (U.asOver (Spec (.of F))) →ₗ[F] fullDual (.of F) U)
      (q : GrpObj.Lie (U.asOver (Spec (.of F))) →
        GrpObj.Lie (U.asOver (Spec (.of F)))),
      (∀ (x : GrpObj.Lie (U.asOver (Spec (.of F)))) (f : Γ(U, ⊤)),
        d x f = ((Scheme.ΓSpecIso (.of (DualNumber F))).hom
          ((GrpObj.tangentPoint x).left.appTop f)).snd) ∧
      (∀ x : GrpObj.Lie (U.asOver (Spec (.of F))),
        leftInvariantOperator F U (d (q x)) = leftInvariantOperator F U (d x) ^ p) ∧
      LieAlgebra.IsRestrictedOperation F p q ∧
      Module.finrank F
        (RestrictedEnvelopingAlgebra F (GrpObj.Lie (U.asOver (Spec (.of F)))) p q) =
        p ^ Nat.card {α : Φ // b.IsPos α} ∧
      ∃ ε : RestrictedEnvelopingAlgebra F
          (GrpObj.Lie (U.asOver (Spec (.of F)))) p q →ₐ[F] F,
        (∀ x : GrpObj.Lie (U.asOver (Spec (.of F))),
          ε (RestrictedEnvelopingAlgebra.ι F p q x) = 0) ∧
        (∃ h : ℕ, 1 ≤ h ∧ RingHom.ker ε.toRingHom ^ h = ⊥) ∧
        (∀ (W : Type v) [AddCommGroup W] [Module F W]
          (c : W →ₗ[F] W ⊗[F] Γ(U, ⊤)), IsCoordinateCoaction (.of F) U c →
          ∃ ρ : RestrictedEnvelopingAlgebra F
              (GrpObj.Lie (U.asOver (Spec (.of F)))) p q →ₐ[F] Module.End F W,
            (∀ x : GrpObj.Lie (U.asOver (Spec (.of F))),
              ρ (RestrictedEnvelopingAlgebra.ι F p q x) = moduleAction (.of F) U c (d x)) ∧
            ∀ x : GrpObj.Lie (U.asOver (Spec (.of F))),
              ρ (RestrictedEnvelopingAlgebra.ι F p q (q x)) =
                ρ (RestrictedEnvelopingAlgebra.ι F p q x) ^ p) ∧
        (Nonempty (Grp.mk (U.asOver (Spec (.of F))) ≅
            Grp.trivial (Over (Spec (.of F)))) →
          Nonempty (RestrictedEnvelopingAlgebra F
              (GrpObj.Lie (U.asOver (Spec (.of F)))) p q ≃ₐ[F] F) ∧
            RingHom.ker ε.toRingHom = ⊥) := by
  sorry

end AlgebraicGeometry.BorelDistributions
