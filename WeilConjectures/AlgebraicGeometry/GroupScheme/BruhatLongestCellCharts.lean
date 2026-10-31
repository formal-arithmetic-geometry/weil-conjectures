/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import WeilConjectures.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections
import WeilConjectures.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations
import WeilConjectures.AlgebraicGeometry.GroupScheme.HomogeneousOrbitQuotientGeometry
import Mathlib.RingTheory.KrullDimension.Polynomial
import WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.Regular

/-! # Bruhat strata and longest-cell flag charts

Source: Milne, Algebraic Groups (2017), 21.70--21.80, pp.446--450,
and 21.84--21.86, pp.451--452.
(blueprint: lem-sfb-bruhat-longest-cell-charts)

Every chart and multiplication is an isomorphism over the base field. Subgroup
intersection is tested on every scheme, including nonreduced test schemes.
Geometric-point factorization expresses the partition after algebraically closed
extensions; the strata themselves are smooth immersed schemes over F.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- Bruhat decomposition, its longest cell, and a finite affine trivializing cover
of the right Borel torsor. The positive roots are the nontrivial character weights
on Lie(B), using its specified conjugation action. The supplied radical is
characterized by exactly the maximality condition in reductive_borel_pair_structure.
The quotient is any presentation with that theorem's right-torsor kernel pair.

Source: Milne, 21.70--21.80, pp.446--450, and 21.84--21.86, pp.451--452.
(blueprint: lem-sfb-bruhat-longest-cell-charts)

Proof plan:
1. Apply lem-sfb-reductive-rank-one-reflections for finite W and its conjugation
   action, and lem-sfb-rho-regular-weyl-orbit for the unique positive-root reversing
   involution. Representatives exist by surjectivity of the quotient map.
   The flag geometry node supplies a separating positive cocharacter. Apply
   lem-sfb-regular-cocharacter-borel-description to its negative; its Borel has
   the same roots as n₀Bn₀⁻¹. The scheme intersection is T by
   lem-sfb-unipotent-root-intersection-products, since their common root set is empty.
2. Apply lem-sfb-projective-attracting-cells to the flag variety and its finite
   reduced fixed points from lem-sfb-flag-torus-fixed-geometry. The tangent weights
   give dimension |Φ⁺ ∖ wΦ⁺|; the w₀-cell is open dense. These attracting strata
   exhaust the flag scheme after every algebraically closed extension.
3. By lem-sfb-borel-root-product-coordinates and the equivariance in
   lem-sfb-reductive-root-subgroup-parametrizations, positive-cocharacter conjugation
   contracts V to 1. The identity λ(t)(uy)=(λ(t)uλ(t)⁻¹)λ(t)y proves that each
   attracting stratum is V-invariant, containing the orbit of n_wB. This holds on
   all test algebras, hence for the schemes, not just their rational points.
4. The torsor identity identifies the stabilizer as H_w=V∩n_wBn_w⁻¹.
   Its root factors are Φ⁺∩wΦ⁺ by the intersection-products node. Root coordinates,
   root parametrizations, and lem-sf-noetherian-polynomial-dimension compute the
   dimensions of V and H_w. By lem-sfb-smooth-group-orbit-geometry the orbit has
   the dimension of the attracting affine space. It is closed there by
   lem-sfb-kostant-rosenlicht-affine-orbits. By lem-wf-affine-dimension-drop it
   cannot be a proper closed subset of that affine space. Both structures are reduced.
   This repairs the equality missing in the printed proof of Milne 21.71.
5. Set V^w=V∩n_wB⁻n_w⁻¹. Its root factors complement those of H_w.
   Order them first in the root product to get V^w×H_w≅V. Projection to V^w is
   right-H_w-invariant, so lem-sfb-homogeneous-orbit-quotient-geometry identifies
   V^w≅V/H_w≅Y_w. For w₀ all positive factors occur, so V^w₀=V.
6. Pull Y_w back along π to define C_w. The inverse to multiplication sends g
   to (u,(un_w)⁻¹g), where u is the unique V^w-coordinate of π(g); the torsor
   identity places the second coordinate in B. This proves the scheme isomorphism.
   Base change gives immersions and the partition; smoothness follows from
   smoothness of V^w and B, lem-pc-proper-base-change and lem-trf-smooth-composition.
7. Root coordinates give V≅A^N. The longest flag cell has section un₀. Every
   rational flag lifts to G(F) by the homogeneous quotient node, so its translates
   cover rational flags. A nonempty closed complement would have a closed point
   by lem-sc-lft-over-field-jacobson-space and F-residue field by
   lem-weil-pbc-closed-point-residue-field-base. Hence the translates cover Q.
   Properness makes Q quasi-compact, giving a finite subcover. Translate the
   section and its right-multiplication trivialization on each chart.
8. After every field extension, G is smooth, connected and nonempty: use
   lem-pc-proper-base-change, lem-sfb-solvable-normal-subgroup-products and its
   identity section. Apply lem-weil-pbc-smooth-scheme-over-field-regular and
   lem-sc-regular-connected-integral. The surjective torsor makes Q irreducible
   and nonempty after base change; the affine-space charts make it reduced.
   Finally the nonempty open longest stratum in integral G is dense. This also
   covers Φ=∅: V=1, Q=Spec F, and the single stratum is G=B=T. -/
theorem bruhat_longest_cell_charts
    {F : Type u} [Field F] [IsAlgClosed F]
    (G T B V : Grp (Over (Spec (.of F))))
    (hG : ReductiveTorusCentralizer.IsReductive G)
    (iT : T ⟶ G) (hT : ReductiveTorusCentralizer.IsMaximalTorus iT)
    (hsplit : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    (iB : B ⟶ G) (hB : IsBorelGroupScheme iB.hom.hom)
    (j : T ⟶ B) (hj : j ≫ iB = iT)
    (iV : V ⟶ B)
    (hV : IsClosedSubgroupScheme iV.hom.hom ∧ IsNormalSubgroupScheme iV.hom.hom ∧
      Smooth V.X.hom ∧ ConnectedSpace V.X.left ∧ SolvableGroupStructure.IsUnipotent V ∧
      ∀ (U : Grp (Over (Spec (.of F)))) (iU : U ⟶ B),
        IsClosedSubgroupScheme iU.hom.hom → IsNormalSubgroupScheme iU.hom.hom →
        Smooth U.X.hom → ConnectedSpace U.X.left → SolvableGroupStructure.IsUnipotent U →
        ∃ f : U ⟶ V, f ≫ iV = iU)
    (Q : Over (Spec (.of F))) (π : G.X ⟶ Q)
    (hπflat : Flat π.left) (hπsurj : Surjective π.left)
    (hπinv : (fst G.X B.X * (snd G.X B.X ≫ iB.hom.hom)) ≫ π = fst G.X B.X ≫ π)
    (hπtorsor : IsPullback (fst G.X B.X)
      (fst G.X B.X * (snd G.X B.X ≫ iB.hom.hom)) π π)
    (aB : ModObj T.X B.X)
    (haB : aB.smul = (j.hom.hom ⊗ₘ 𝟙 B.X) ≫ GrpObj.conj B.X)
    (Φplus : Finset (RankOneRoots.Character T))
    (hΦplus : ∀ χ : RankOneRoots.Character T, χ ∈ Φplus ↔
      χ.hom.hom ≠ 1 ∧ @TorusCharacterTangent.weightSpace F _ T B aB χ ≠ ⊥) :
    Finite (RankOneRoots.Weyl iT) ∧
    ∃ (act : RankOneRoots.Weyl iT →* Aut T),
      (∀ (n : RankOneRoots.normalizer iT) (A : Over (Spec (.of F))) (t : A ⟶ T.X),
        t ≫ (act (QuotientGroup.mk n)).hom.hom.hom ≫ iT.hom.hom =
          (toUnit A ≫ n.val) * (t ≫ iT.hom.hom) * (toUnit A ≫ n.val)⁻¹) ∧
    ∃ (w₀ : RankOneRoots.Weyl iT),
      (Set.image (fun χ : RankOneRoots.Character T ↦ (act w₀).inv.hom.hom ≫ χ.hom.hom)
          (Φplus : Set _) = Set.image (fun χ : RankOneRoots.Character T ↦ χ.hom.hom⁻¹)
            (Φplus : Set _)) ∧
      (∀ w : RankOneRoots.Weyl iT,
        Set.image (fun χ : RankOneRoots.Character T ↦ (act w).inv.hom.hom ≫ χ.hom.hom)
            (Φplus : Set _) = Set.image (fun χ : RankOneRoots.Character T ↦ χ.hom.hom⁻¹)
              (Φplus : Set _) → w = w₀) ∧
      w₀ * w₀ = 1 ∧
    ∃ (n : RankOneRoots.Weyl iT → RankOneRoots.normalizer iT),
      (∀ w, QuotientGroup.mk (n w) = w) ∧
    ∃ (C Vw : RankOneRoots.Weyl iT → Over (Spec (.of F)))
      (c : ∀ w, C w ⟶ G.X) (v : ∀ w, Vw w ⟶ V.X)
      (e : ∀ w, Vw w ⊗ B.X ≅ C w),
      (∀ w, IsImmersion (c w).left ∧ Smooth (C w).hom ∧ IsImmersion (v w).left ∧
        (e w).hom ≫ c w =
          (fst (Vw w) B.X ≫ v w ≫ iV.hom.hom ≫ iB.hom.hom) *
          (toUnit (Vw w ⊗ B.X) ≫ (n w).val) * (snd (Vw w) B.X ≫ iB.hom.hom)) ∧
      (∀ x : G.X.left, ∃! w, x ∈ Set.range (c w).left) ∧
      (∀ (K : Type u) [Field K] [Algebra F K] [IsAlgClosed K]
        (g : StandardGroupSchemes.affine F K ⟶ G.X),
        ∃! w, ∃ z : StandardGroupSchemes.affine F K ⟶ C w, z ≫ c w = g) ∧
      IsOpenImmersion (c w₀).left ∧ DenseRange (c w₀).left ∧ IsIso (v w₀) ∧
      Nonempty (V.X ≅ StandardGroupSchemes.affine F (MvPolynomial (Fin Φplus.card) F)) ∧
      GeometricallyIntegral G.X.hom ∧ GeometricallyIntegral Q.hom ∧
      ∀ n₀ : RankOneRoots.normalizer iT, QuotientGroup.mk n₀ = w₀ →
        (∀ A : Over (Spec (.of F)),
          {g : A ⟶ G.X | g ∈ RankOneRoots.pointImage iB A ∧
            ∃ b : A ⟶ B.X, g = (toUnit A ≫ n₀.val) * (b ≫ iB.hom.hom) *
              (toUnit A ≫ n₀.val)⁻¹} = (RankOneRoots.pointImage iT A : Set _)) ∧
        (∃ (D : Over (Spec (.of F))) (d : D ⟶ Q) (eD : V.X ≅ D),
          IsOpenImmersion d.left ∧ DenseRange d.left ∧
          eD.hom ≫ d =
            ((iV.hom.hom ≫ iB.hom.hom) * (toUnit V.X ≫ n₀.val)) ≫ π) ∧
        ∃ (m : ℕ) (a : Fin m → (𝟙_ (Over (Spec (.of F))) ⟶ G.X))
          (D : Fin m → Over (Spec (.of F))) (d : ∀ k, D k ⟶ Q)
          (eD : ∀ k, V.X ≅ D k) (s : ∀ k, D k ⟶ G.X),
          (∀ k, IsOpenImmersion (d k).left ∧
            (eD k).hom ≫ d k =
              ((toUnit V.X ≫ a k) * (iV.hom.hom ≫ iB.hom.hom) *
                (toUnit V.X ≫ n₀.val)) ≫ π ∧
            s k ≫ π = d k ∧
            IsPullback ((fst (D k) B.X ≫ s k) * (snd (D k) B.X ≫ iB.hom.hom))
              (fst (D k) B.X) π (d k)) ∧
          ∀ x : Q.left, ∃ k, x ∈ Set.range (d k).left := by
  sorry

end AlgebraicGeometry
