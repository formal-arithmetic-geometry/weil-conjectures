/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q85
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.RationalHighestWeightData
public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
import Sheaf.AlgebraicGeometry.GmRepresentationWeightBasis

/-! # Highest weights and contragredients of simple rational modules

Source: Milne, Algebraic Groups (2017), Theorems 22.18--22.19, pp.467--468,
and the contragredient paragraph following 22.31, p.471.
(blueprint: lem-sfb-simple-module-dual-highest-weight)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped TensorProduct MonObj
namespace AlgebraicGeometry.RationalHighestWeight

/-- Simple rational modules have highest lines, their duals have opposition highest
weight, and equal highest weights determine an equivariant linear isomorphism.
Source: Milne, Theorems 22.18--22.19 and p.471.
(blueprint: lem-sfb-simple-module-dual-highest-weight)

The longest Weyl element is represented by n and its induced automorphism e of T.
The equation he fixes the action as conjugation by n inverse; hlongest says it sends
the actual positive character roots in Lie(B) to their negatives. Multiplicative
character notation renders -w0(lam) as (e.hom followed by lam) inverse.

Proof:
1. Decompose rational torus modules into character spaces by applying
   lem-sfb-gm-representation-weight-basis to each split torus factor. Coassociativity
   gives the coefficient projections and the counit their sum, including on subspaces.
2. The radical from lem-sfb-reductive-borel-pair-structure is unipotent. Apply
   lem-sfb-unipotent-rational-representation-fixed-vector and
   lem-sfb-geometric-unipotence-invariant-descent over F to get a nonzero U-invariant.
   Normality makes the invariant subspace T-stable, so it contains a weight vector.
3. Simplicity makes that vector cyclic. By lem-sfb-primitive-cyclic-weight-bound
   its weight space is its line and all weights lie below its weight. Applying the
   bound to another invariant weight vector forces the same weight, by independence
   of simple roots. Hence all U-invariants form this one-dimensional character line.
4. The inverse-transpose action, using the coordinate antipode, defines the dual
   coaction characterized by IsContragredient. A proper nonzero dual submodule has a
   proper nonzero stable annihilator in V, contradicting simplicity. Its positive
   dimension equals that of V, so the dual is simple.
5. A normalizer representative carries the weight-mu space to the weight-w(mu)
   space. Thus weights are Weyl invariant. Since w0 reverses positive roots,
   w0(lambda) is the least weight. Dual weights are their negatives, so the greatest
   dual weight is -w0(lambda), which step 3 identifies with its highest weight.
6. For two simple modules with weight lambda, generate a submodule of their direct
   sum by a pair of nonzero highest vectors. The cyclic weight bound makes its
   lambda-space the diagonal line. Its projections are surjective by simplicity;
   their kernels cannot contain either full summand, because that would contradict
   the diagonal line description. Both projections are isomorphisms. Their composite
   gives the required linear equivalence, and the coaction square gives equivariance.
-/
theorem simple_module_dual_highest_weight
    {F : Type u} [Field F] [IsAlgClosed F]
    (G T B U : Grp (Over (Spec (.of F))))
    [IsAffine G.X.left] [IsAffine T.X.left] [IsAffine U.X.left]
    (hG : IsSemisimpleGroupScheme G.X)
    (iT : T ⟶ G) (iB : B ⟶ G) (j : T ⟶ B) (iU : U ⟶ B)
    (hT : ReductiveTorusCentralizer.IsMaximalTorus iT)
    (hsplit : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    (hB : IsBorelGroupScheme iB.hom.hom) (hj : j ≫ iB = iT)
    (hUclosed : IsClosedSubgroupScheme iU.hom.hom)
    (hUnormal : IsNormalSubgroupScheme iU.hom.hom)
    (hUsmooth : Smooth U.X.hom) (hUconnected : ConnectedSpace U.X.left)
    (hUunipotent : SolvableGroupStructure.IsUnipotent U)
    (hUmax : ∀ (N : Grp (Over (Spec (.of F)))) (iN : N ⟶ B),
      IsClosedSubgroupScheme iN.hom.hom → IsNormalSubgroupScheme iN.hom.hom →
      Smooth N.X.hom → ConnectedSpace N.X.left →
      SolvableGroupStructure.IsUnipotent N → ∃ f : N ⟶ U, f ≫ iU = iN)
    [IsCommMonObj (StandardGroupSchemes.multiplicative F)]
    [ModObj T.X B.X]
    (hconj : γ[T.X,B.X] =
      (fst T.X B.X ≫ j.hom.hom) * snd T.X B.X * (fst T.X B.X ≫ j.hom.hom)⁻¹)
    (Φplus : Set (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
    (hΦplus : ∀ χ, χ ∈ Φplus ↔
      χ ≠ 1 ∧ TorusCharacterTangent.weightSpace T B χ ≠ ⊥)
    (n : 𝟙_ (Over (Spec (.of F))) ⟶ G.X) (e : T ≅ T)
    (he : e.hom.hom.hom ≫ iT.hom.hom =
      (toUnit T.X ≫ n⁻¹) * iT.hom.hom * (toUnit T.X ≫ n))
    (hlongest : (fun χ ↦ e.hom ≫ χ) '' Φplus = (fun χ ↦ χ⁻¹) '' Φplus)
    {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (c : V →ₗ[F] V ⊗[F] coordinateAlgebra G)
    (hcoassoc : HopfAction.Coassociative F (coordinateAlgebra G) V c)
    (hcounit : HopfAction.Counital F (coordinateAlgebra G) V c)
    (hsimple : IsSimple c) :
    ∃ lam : T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F),
      HasHighestWeight c iT (iU ≫ iB) lam ∧
      (∃ d : Module.Dual F V →ₗ[F] Module.Dual F V ⊗[F] coordinateAlgebra G,
        HopfAction.Coassociative F (coordinateAlgebra G) (Module.Dual F V) d ∧
        HopfAction.Counital F (coordinateAlgebra G) (Module.Dual F V) d ∧
        IsContragredient c d ∧ IsSimple d ∧
        HasHighestWeight d iT (iU ≫ iB) ((e.hom ≫ lam)⁻¹)) ∧
      ∀ (W : Type w) [AddCommGroup W] [Module F W] [FiniteDimensional F W]
        (cW : W →ₗ[F] W ⊗[F] coordinateAlgebra G),
        HopfAction.Coassociative F (coordinateAlgebra G) W cW →
        HopfAction.Counital F (coordinateAlgebra G) W cW → IsSimple cW →
        HasHighestWeight cW iT (iU ≫ iB) lam →
        ∃ f : V ≃ₗ[F] W,
          f.toLinearMap.rTensor (coordinateAlgebra G) ∘ₗ c = cW ∘ₗ f.toLinearMap := by
  sorry

end AlgebraicGeometry.RationalHighestWeight
