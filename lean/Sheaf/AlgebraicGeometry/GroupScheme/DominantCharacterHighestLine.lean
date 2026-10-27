/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.BorelPairRootDatumNormalization
public import Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces
public import Sheaf.AlgebraicGeometry.GroupScheme.RationalHighestWeightData
import Sheaf.AlgebraicGeometry.GroupScheme.SimplyConnectedCharacterLattice
import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousLineBundleSections
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Dominant characters on Borel-stable rational lines

Source: Milne, Algebraic Groups (2017), Theorems 22.2--22.3, Proposition 22.17,
Theorem 22.20 and its proof, pp.463--470; positive roots as in 21.35.
(blueprint: lem-sfb-dominant-character-highest-line)

The eigenvector identity is stated on coordinate coactions. This is the universal
identity over every commutative test algebra, not just an identity on F-points.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped TensorProduct MonObj

namespace AlgebraicGeometry.RationalHighestWeight

/-- Every dominant character occurs on a Borel-stable line in a nonzero
finite-dimensional rational representation. The root and coroot lattices and
the positive base are those of the specified Borel pair, pinned to conjugation
weights and actual composition of characters and cocharacters. The simple
reflections are pinned to normalizer conjugation by hact and hs, including on
central characters. The radical, projection and Weyl-compatible root data are
furnished by canonical_reductive_borel_pair_structure.

Source: Milne, Theorems 22.2--22.3 and 22.20, Proposition 22.17 and
Lemmas 22.24--22.26, pp.463--470; 21.35 for the positive-root convention.
(blueprint: lem-sfb-dominant-character-highest-line)

The first tensor equality says b(v tensor 1) = lambda(p(b))(v tensor 1)
over every commutative F-algebra: evaluate its F[B] factor at b. Conversely
the universal B-valued point recovers the equality. The last two clauses give
stability of Fv and triviality of the full scheme-theoretic U-action on that line.

Proof plan:
1. For a semisimple simply connected group, use
   lem-sfb-simply-connected-character-lattice for fundamental characters. By
   lem-sfb-fundamental-ray-regular-power a positive power of each big-cell
   character function is regular. By lem-sfb-normal-big-cell-character-functions
   the function is integral over the normal coordinate ring and hence regular.
   It is nonzero, U-fixed, and has the fundamental T-character. The decomposition
   B = U semidirect T gives its B-character over every test algebra.
2. By lem-sfb-homogeneous-line-bundle-sections the corresponding section space
   is the global sections of an invertible coherent sheaf on the proper finite-type
   flag quotient from lem-sfb-reductive-borel-pair-structure. Apply lem-pc-coherent-hi
   in degree zero over Spec F to obtain a finite-dimensional rational module
   containing the nonzero function. No complete reducibility is used.
3. Expand the dominant character in fundamental characters with nonnegative
   integral coefficients. Tensor the modules and vectors with these multiplicities;
   multiply Hopf coefficients for the tensor coaction. Linear forms taking each
   vector to 1 prove the tensor vector nonzero. Its B-character is the prescribed
   product. Empty tensor products are F and 1, so rank zero is included.
4. For general G, use lem-sfb-reductive-torus-simply-connected-cover and
   lem-sfb-central-isogeny-borel-root-compatibility to pull the Borel pair and
   character to Z times S. Smoothness, connectedness and finite type of this
   product follow from lem-trf-split-lattice-torus-projection,
   lem-trf-smooth-composition and
   lem-weil-pbc-geometrically-connected-product-components. Pairing compatibility
   makes the S-character dominant. Tensor its module with the one-dimensional
   Z-character. The central scheme-theoretic kernel fixes the resulting vector.
5. Apply lem-sfb-central-kernel-cyclic-representation-descent to the cyclic
   submodule. Test the B-character equality after the faithfully flat lift of
   any B(A)-point to the covering Borel. Faithful flatness detects equality;
   the zero algebra is immediate. In coaction form this is the first tensor
   equality. Linearity gives stability of Fv, and p restricted to U is 1, so
   the restricted U-coaction fixes v and hence Fv. For the trivial group take F, 1.
-/
theorem dominant_character_highest_line
    {F : Type u} [Field F] [IsAlgClosed F]
    (G T B U : Grp (Over (Spec (.of F))))
    [IsAffine G.X.left] [IsAffine B.X.left] [IsAffine U.X.left]
    (hG : ReductiveTorusCentralizer.IsReductive G)
    (iT : T ⟶ G) (iB : B ⟶ G) (j : T ⟶ B) (iU : U ⟶ B) (p : B ⟶ T)
    (hT : ReductiveTorusCentralizer.IsMaximalTorus iT)
    (hsplit : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    (hB : IsBorelGroupScheme iB.hom.hom) (hj : j ≫ iB = iT)
    (hUclosed : IsClosedSubgroupScheme iU.hom.hom)
    (hUnormal : IsNormalSubgroupScheme iU.hom.hom)
    (hUsmooth : Smooth U.X.hom) (hUconnected : ConnectedSpace U.X.left)
    (hUunipotent : SolvableGroupStructure.IsUnipotent U)
    (hUmax : ∀ (N : Grp (Over (Spec (.of F)))) (iN : N ⟶ B),
      IsClosedSubgroupScheme iN.hom.hom → IsNormalSubgroupScheme iN.hom.hom →
      Smooth N.X.hom → ConnectedSpace N.X.left → SolvableGroupStructure.IsUnipotent N →
      ∃ f : N ⟶ U, f ≫ iU = iN)
    (hp : j ≫ p = 𝟙 T)
    (hker : IsPullback iU.hom.hom (toUnit U.X) p.hom.hom η[T.X])
    (hdecomp : IsIso ((fst U.X T.X ≫ iU.hom.hom) * (snd U.X T.X ≫ j.hom.hom)))
    [IsCommMonObj T.X] [IsCommMonObj (StandardGroupSchemes.multiplicative F)]
    (aG : ModObj T.X G.X) (aB : ModObj T.X B.X)
    (haG : aG.smul = (iT.hom.hom ⊗ₘ 𝟙 G.X) ≫ CategoryTheory.GrpObj.conj G.X)
    (haB : aB.smul = (j.hom.hom ⊗ₘ 𝟙 B.X) ≫ CategoryTheory.GrpObj.conj B.X)
    (Φ : Finset (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))))
    (P : RootDatum Φ
      (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)))
    (b : P.Base)
    (hroot : ∀ α : Φ, P.root α = α.val)
    (hpair : ∀ (χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (ν : Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)),
      ν.toMul.hom.hom ≫ χ.toMul.hom.hom =
        (𝟙 (StandardGroupSchemes.multiplicative F)) ^ (P.toLinearMap χ ν))
    (hweights : ∀ χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
      χ ∈ Φ ↔ χ ≠ 0 ∧ @TorusCharacterTangent.weightSpace F _ T G aG χ.toMul ≠ ⊥)
    (hpositive : ∀ α : Φ,
      b.IsPos α ↔ @TorusCharacterTangent.weightSpace F _ T B aB α.val.toMul ≠ ⊥)
    (act : RankOneRoots.Weyl iT →* Aut T)
    (hact : ∀ (n : RankOneRoots.normalizer iT) (A : Over (Spec (.of F))) (t : A ⟶ T.X),
      t ≫ (act (QuotientGroup.mk n)).hom.hom.hom ≫ iT.hom.hom =
        (toUnit A ≫ n.val) * (t ≫ iT.hom.hom) * (toUnit A ≫ n.val)⁻¹)
    (s : b.support → RankOneRoots.Weyl iT)
    (hs : ∀ (α : b.support) (χ : RankOneRoots.Character T),
      (act (s α)).inv ≫ χ = (P.reflection α.val (Additive.ofMul χ)).toMul)
    (lam : T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))
    (hdominant : ∀ α : b.support, 0 ≤ P.toLinearMap (Additive.ofMul lam) (P.coroot α)) :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module F V) (_ : FiniteDimensional F V)
      (c : V →ₗ[F] V ⊗[F] coordinateAlgebra G),
      HopfAction.Coassociative F (coordinateAlgebra G) V c ∧
      HopfAction.Counital F (coordinateAlgebra G) V c ∧
      ∃ v : V, v ≠ 0 ∧
        (coordinateMap iB).toLinearMap.lTensor V (c v) =
          v ⊗ₜ[F] characterElement (p ≫ lam) ∧
        IsStable ((coordinateMap iB).toLinearMap.lTensor V ∘ₗ c) (F ∙ v) ∧
        v ∈ invariants c (iU ≫ iB) := by
  sorry

end AlgebraicGeometry.RationalHighestWeight
