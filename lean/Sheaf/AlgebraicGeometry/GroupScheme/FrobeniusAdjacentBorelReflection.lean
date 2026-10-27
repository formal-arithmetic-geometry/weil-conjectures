/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections
public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations
public import Sheaf.AlgebraicGeometry.GroupScheme.AffineFrobeniusKernelDistributions
import Sheaf.AlgebraicGeometry.GroupScheme.StandardParabolicLeviCharts
import Sheaf.AlgebraicGeometry.GroupScheme.BorelRootProductCoordinates

/-! # Moving a Frobenius-kernel highest vector across a simple-root wall

Source: the finite-kernel calculation attached to Milne, Algebraic Groups (2017),
Theorem 21.11, pp.428--430, formula (135), p.431, and Theorem 21.91, pp.453--454.
Milne supplies the geometry; the distribution calculation is agent-formulated.
(blueprint: lem-sfb-frobenius-adjacent-borel-reflection)

Kernel inclusions and top coefficients are specified by their exact canonical
characterizations. Thus no rational S-action on the arbitrary vector space V is
assumed. The conjugated Borel is presented by an isomorphism over conjugation;
its torus projection is transported by the same conjugation automorphism of T.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj TensorProduct

namespace AlgebraicGeometry.BorelDistributions

/-- A highest vector for B_r of coroot weight p^r-1 becomes a highest vector for
its adjacent Borel under the top negative-root coefficient. The top positive-root
coefficient recovers a nonzero scalar multiple of the original vector.
Source: agent-formulated finite-kernel lemma using Milne, Theorem 21.11,
formula (135), Theorems 21.68 and 21.91; Jantzen II.3.18 and II.9 motivate its use.
(blueprint: lem-sfb-frobenius-adjacent-borel-reflection)

Proof plan, following the nine steps of the node:
1. Finite-dimensional coordinate duality identifies every unital Dist(S_r)-module
   with a counital coassociative S_r-coaction, even for infinite-dimensional V.
   The B_r eigenvector condition becomes its character coaction identity, so U_r
   fixes w over every algebra (def-sfb-affine-group-distribution-calculus).
2. Use lem-sfb-opposite-root-sl2-parametrizations for compatible parameters y±.
   Each arbitrary x± differs by a nonzero scalar a±. Consequently its jth coefficient
   is a±^j times the compatible coefficient. Put m=q-1.
3. Apply lem-sfb-standard-parabolic-levi-charts to the singleton simple root.
   Its radical R and rank-one Levi give B'=R U_-alpha T and kernel product
   B'_r=R_r U_-alpha,r T_r. Reflection permutes the other positive roots, by
   lem-sfb-reductive-rank-one-reflections and the same-sign simple-root expansion
   of lem-sfb-reductive-borel-pair-structure. The ordered product is an isomorphism
   by lem-sfb-borel-root-product-coordinates, including on these kernels.
4. R_r fixes w and is normalized by U_-alpha,r. Apply conjugation to the universal
   negative-root point over D[t]/(t^q). Coefficient extraction shows R_r fixes F_m w.
5. The root conjugation formula (lem-sfb-reductive-root-subgroup-parametrizations)
   shows on all T_r-points that F_m w has character mu-m alpha, using full
   characters on nonreduced algebras rather than differentials of weights.
6. Compare the coefficient of t^m in y_-(s)y_-(t)w=y_-(s+t)w in
   F[s,t]/(s^q,t^q). Since the expansion has degree at most m, its top coefficient
   is independent of s. Therefore U_-alpha,r fixes F_m w.
7. The product in step 3 now gives the required B'_r character identity. Its
   unipotent factors lie in the conjugated radical, and its torus projection is
   exactly the transported projection used here. Finite duality gives eigenvectors.
8. In F[u,v]/(u^q,v^q), set a=1+uv. The SL2 Gauss identity is
   y_+(u)y_-(v)=y_-(v/a)h(a)y_+(u/a). Since a^q=1, every factor lies in its kernel.
   The highest-vector condition and coroot weight m give h(a)w=a^m w. Comparing
   the coefficient of u^m v^m gives E_m F_m w=w, with no factorial division.
9. Return to x±: kappa=(a+ a-)^m is a unit, and recovery implies that w' is
   nonzero whenever w is. This includes p=2, every r>=1 and w=0. -/
theorem frobenius_adjacent_borel_reflection
    (F : Type u) [Field F] [IsAlgClosed F]
    (S T B : Grp (Over (Spec (.of F))))
    [IsAffine S.X.left] [IsAffine B.X.left]
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
    (α : b.support) (r : ℕ) (hr : 1 ≤ r)
    (n : RankOneRoots.normalizer iT) (σ : T ≅ T)
    (hσ : σ.hom.hom.hom ≫ iT.hom.hom =
      (toUnit T.X ≫ n.val) * iT.hom.hom * (toUnit T.X ≫ n.val)⁻¹)
    (hreflection : ∀ χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
      σ.inv.hom.hom ≫ χ.toMul.hom.hom =
        χ.toMul.hom.hom / α.val.val.toMul.hom.hom ^
          (P.toLinearMap χ (P.coroot α.val)))
    (B' : Grp (Over (Spec (.of F)))) [IsAffine B'.X.left]
    (iB' : B' ⟶ S) (e : B ≅ B')
    (he : e.hom.hom.hom ≫ iB'.hom.hom =
      (toUnit B.X ≫ n.val) * iB.hom.hom * (toUnit B.X ≫ n.val)⁻¹)
    [ModObj T.X B'.X]
    (hconjB' : γ[T.X,B'.X] =
      ((σ.inv ≫ jT ≫ e.hom).hom.hom ⊗ₘ 𝟙 B'.X) ≫ GrpObj.conj B'.X)
    (xp xm : Grp.mk (StandardGroupSchemes.additive F) ⟶ S)
    (hxp : IsClosedSubgroupScheme xp.hom.hom ∧ TorusCharacterTangent.IsStable T S xp ∧
      (GrpObj.differential xp.hom.hom).toLinearMap.range =
        TorusCharacterTangent.weightSpace T S α.val.val.toMul)
    (hxm : IsClosedSubgroupScheme xm.hom.hom ∧ TorusCharacterTangent.IsStable T S xm ∧
      (GrpObj.differential xm.hom.hom).toLinearMap.range =
        TorusCharacterTangent.weightSpace T S (-α.val.val).toMul)
    (Sr Br Br' : Grp (Over (Spec (.of F))))
    [IsAffine Sr.X.left] [IsAffine Br.X.left] [IsAffine Br'.X.left]
    (iSr : Sr ⟶ S) (iBr : Br ⟶ B) (iBr' : Br' ⟶ B')
    (hSr : IsFrobeniusKernel iSr (p ^ r))
    (hBr : IsFrobeniusKernel iBr (p ^ r))
    (hBr' : IsFrobeniusKernel iBr' (p ^ r))
    [FiniteDimensional F (RationalHighestWeight.coordinateAlgebra Sr)]
    (kB : Br ⟶ Sr) (kB' : Br' ⟶ Sr)
    (hkB : kB ≫ iSr = iBr ≫ iB) (hkB' : kB' ≫ iSr = iBr' ≫ iB')
    (dp dm : fullDual (.of F) Sr.X.left)
    (hdp : push iSr dp = dividedPower (.of F) S.X.left xp.hom.hom (p ^ r - 1))
    (hdm : push iSr dm = dividedPower (.of F) S.X.left xm.hom.hom (p ^ r - 1))
    (mu : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
    (hmu : P.toLinearMap mu (P.coroot α.val) = (p ^ r : ℕ) - (1 : ℤ))
    (V : Type v) [AddCommGroup V] [Module F V]
    (ρ : fullDual (.of F) Sr.X.left →ₐ[F] Module.End F V) (w : V)
    (hw : ∀ z : fullDual (.of F) Br.X.left,
      ρ (push kB z) w =
        z ((RationalHighestWeight.coordinateMap iBr)
          (RationalHighestWeight.characterElement (πT ≫ mu.toMul))) • w) :
    (∀ χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
      (χ ≠ 0 ∧ TorusCharacterTangent.weightSpace T B' χ.toMul ≠ ⊥) ↔
        (∃ β : Φ, b.IsPos β ∧ β ≠ α.val ∧ χ = β.val) ∨ χ = -α.val.val) ∧
    (∀ z : fullDual (.of F) Br'.X.left,
      ρ (push kB' z) (ρ dm w) =
        z ((RationalHighestWeight.coordinateMap iBr')
          (RationalHighestWeight.characterElement
            (e.inv ≫ πT ≫ σ.hom ≫ (mu - (p ^ r - 1) • α.val.val).toMul))) • (ρ dm w)) ∧
    (∃ κ : Fˣ, ρ dp (ρ dm w) = (κ : F) • w) ∧
    (w ≠ 0 → ρ dm w ≠ 0) := by
  sorry

end AlgebraicGeometry.BorelDistributions
