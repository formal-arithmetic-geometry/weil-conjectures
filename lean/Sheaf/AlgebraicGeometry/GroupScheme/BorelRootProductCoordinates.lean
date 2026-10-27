/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Data.List.OfFn

/-! # Ordered root coordinates on a Borel unipotent radical

Source: Milne, Algebraic Groups (2017), Theorem 21.68(a), p.445,
and Remark 21.69, p.446 (blueprint: lem-sfb-borel-root-product-coordinates).

Positive roots are the nontrivial adjoint characters occurring in Lie(B), exactly
as identified by reductive_borel_pair_structure. An injective Fin r enumeration
with the stated image permits every order. Products are products of underlying
F-schemes, and the map is the ordered product in their group-valued Hom functors.
The conjugation actions in the conclusion are pinned by the subgroup inclusions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- Multiplication of the positive root groups in any order is a torus-equivariant
isomorphism onto the unipotent radical of the chosen Borel.
Source: Milne, Theorem 21.68(a), p.445, and Remark 21.69, p.446
(blueprint: lem-sfb-borel-root-product-coordinates).

Proof plan, following the node:
1. By lem-sfb-regular-cocharacter-borel-description choose a regular cocharacter
   defining B. Its pairing with every listed root is strictly positive, since
   lem-sfb-reductive-borel-pair-structure identifies positivity with Lie(B) weights.
2. The conjugation formula of lem-sfb-reductive-root-subgroup-parametrizations
   extends the cocharacter orbit on each root group across zero, with value one.
   Thus each root group lies in the limit subgroup of
   lem-sfb-cocharacter-limit-smooth-structure, hence in the maximal unipotent
   radical U. This gives the homomorphisms k and their factorization equalities.
3. Differentiate the splitting B = U semidirect T from
   lem-sfb-reductive-borel-pair-structure. The torus projection kills every nonzero
   positive character weight, by comparing Laurent coefficients. Therefore Lie(U)
   is exactly the direct sum of the listed root weight spaces.
4. The root parametrizations identify the product with affine r-space, smooth,
   connected and affine. Multiplication intertwines conjugation, preserves the
   identity, and its differential is the sum of the root tangent inclusions:
   products of dual-number infinitesimals have no cross terms. Step 3 makes
   this differential an isomorphism. Normalization induces the displayed actions
   on U and on the factors; their composites with the inclusions are conjugation.
5. Apply lem-sfb-positive-weight-equivariant-inverse to this multiplication map
   and the chosen cocharacter: all source tangent weights are strictly positive.
   Hence the map is an isomorphism. The calculation of step 4 gives the displayed
   equivariance on every test scheme. If r = 0, the product is the terminal
   F-scheme Spec F and its multiplication map is the unit. The same argument
   with the empty tangent-weight family identifies U with the trivial group.
   No order or characteristic restriction has been used. -/
theorem borel_root_product_coordinates
    {F : Type u} [Field F] [IsAlgClosed F]
    (G T B : Grp (Over (Spec (.of F))))
    (hG : ReductiveTorusCentralizer.IsReductive G)
    (iT : T ⟶ G) (hT : ReductiveTorusCentralizer.IsMaximalTorus iT)
    (hsplit : ∃ n : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F n))
    (iB : B ⟶ G) (hB : IsBorelGroupScheme iB.hom.hom)
    (j : T ⟶ B) (hj : j ≫ iB = iT)
    (aG : ModObj T.X G.X) (aB : ModObj T.X B.X)
    (haG : aG.smul = (iT.hom.hom ⊗ₘ 𝟙 G.X) ≫ GrpObj.conj G.X)
    (haB : aB.smul = (j.hom.hom ⊗ₘ 𝟙 B.X) ≫ GrpObj.conj B.X)
    (U : Grp (Over (Spec (.of F)))) (iU : U ⟶ B)
    (hUclosed : IsClosedSubgroupScheme iU.hom.hom)
    (hUnormal : IsNormalSubgroupScheme iU.hom.hom)
    (hUsmooth : Smooth U.X.hom) (hUconn : ConnectedSpace U.X.left)
    (hUunip : SolvableGroupStructure.IsUnipotent U)
    (hUmax : ∀ (N : Grp (Over (Spec (.of F)))) (iN : N ⟶ B),
      IsClosedSubgroupScheme iN.hom.hom → IsNormalSubgroupScheme iN.hom.hom →
      Smooth N.X.hom → ConnectedSpace N.X.left → SolvableGroupStructure.IsUnipotent N →
      ∃ f : N ⟶ U, f ≫ iU = iN)
    (r : ℕ) (α : Fin r → (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
    (hαinj : Function.Injective α)
    (hαpos : ∀ χ : T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F),
      (∃ i : Fin r, α i = χ) ↔ χ.hom.hom ≠ 1 ∧
        @TorusCharacterTangent.weightSpace F _ T G aG χ ≠ ⊥ ∧
        @TorusCharacterTangent.weightSpace F _ T B aB χ ≠ ⊥)
    (R : Fin r → Grp (Over (Spec (.of F)))) (iR : ∀ i : Fin r, R i ⟶ G)
    (hR : ∀ i : Fin r,
      IsClosedSubgroupScheme (iR i).hom.hom ∧ Smooth (R i).X.hom ∧
      ConnectedSpace (R i).X.left ∧ @TorusCharacterTangent.IsStable F _ T G aG _ (iR i) ∧
      (GrpObj.differential (iR i).hom.hom).toLinearMap.range =
        @TorusCharacterTangent.weightSpace F _ T G aG (α i)) :
    ∃ k : ∀ i : Fin r, R i ⟶ U,
      (∀ i : Fin r, k i ≫ iU ≫ iB = iR i) ∧
      IsIso ((List.ofFn (fun i : Fin r ↦
        Pi.π (fun l : Fin r ↦ (R l).X) i ≫ (k i).hom.hom)).prod) ∧
      ∃ (aU : ModObj T.X U.X) (aR : ∀ i : Fin r, ModObj T.X (R i).X),
        aU.smul ≫ iU.hom.hom = (j.hom.hom ⊗ₘ iU.hom.hom) ≫ GrpObj.conj B.X ∧
        (∀ i : Fin r, (aR i).smul ≫ (iR i).hom.hom =
          (iT.hom.hom ⊗ₘ (iR i).hom.hom) ≫ GrpObj.conj G.X) ∧
        ∀ (W : Over (Spec (.of F))) (t : W ⟶ T.X) (x : ∀ i : Fin r, W ⟶ (R i).X),
          (List.ofFn (fun i : Fin r ↦
            (lift t (x i) ≫ (aR i).smul) ≫ (k i).hom.hom)).prod =
          lift t ((List.ofFn (fun i : Fin r ↦ x i ≫ (k i).hom.hom)).prod) ≫ aU.smul := by
  sorry

end AlgebraicGeometry
