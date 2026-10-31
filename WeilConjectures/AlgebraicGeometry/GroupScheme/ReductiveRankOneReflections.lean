/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Order.SupIndep
import WeilConjectures.AlgebraicGeometry.ReductiveTorusSelfCentralizer
import WeilConjectures.AlgebraicGeometry.MultiplicativeTypeLargestSubtorus
import WeilConjectures.AlgebraicGeometry.PerfectSolvableUnipotentTorus

/-! # Rank-one subgroups and normalizer reflections

Source: Milne, Algebraic Groups (2017), Propositions 21.1--21.2, pp.424--425;
Theorem 21.11(a)--(e), pp.428--430
(blueprint: lem-sfb-reductive-rank-one-reflections).

Characters are written multiplicatively. Thus x - <x,ν>α is x / α^<x,ν>.
All weight spaces use actual torus characters, not their differentials.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.RankOneRoots

/-- The character weight decomposition and integral coroot reflections of a reductive
algebraic group, with the rank-one SL2 construction and its functoriality.
Source: Milne, Propositions 21.1--21.2 and Theorem 21.11(a)--(e), pp.424--430
(blueprint: lem-sfb-reductive-rank-one-reflections).

Proof plan:
1. Use lem-sfb-multiplicative-character-antiduality and
   lem-sfb-gm-representation-weight-basis successively in the split torus coordinates.
   The zero weight is Lie(C_G(T)) by the dual-number definition of the centralizer;
   lem-sfb-reductive-torus-self-centralizer identifies it with Lie(T).
2. Use lem-sfb-torus-normalizer-components and the self-centralizer to get finite W.
   Conjugation acts on characters by n⁻¹tn and on cocharacters by nνn⁻¹; composing
   preserves the integer pairing. Conjugation on Lie(G) carries g_α to g_(nα).
3. Write α = ma with a primitive integral character. By character antiduality and
   lem-sfb-multiplicative-type-largest-subtorus, T_α is the codimension-one torus
   a = 1. The weights trivial on it are exactly X ∩ Qα. Dual numbers identify
   Lie(C_G(T_α)) with Lie(T) plus the weight spaces on that rational line.
4. Apply lem-sfb-reductive-torus-fixed-subgroup. Construct the radical R by maximal
   dimension using lem-sfb-solvable-normal-subgroup-products. The theorem
   lem-sfb-perfect-solvable-unipotent-torus and reductivity make R a torus;
   lem-sfb-connected-action-torus-rigidity makes it central, containing T_α.
5. By lem-sfb-reductive-semisimple-rank-formula the semisimple rank is at most one.
   Rank zero would make T central in G_α, hence G_α ⊆ C_G(T) = T, contradicting
   its nonzero α-weight space. Therefore its semisimple rank is one.
6. Apply lem-sfb-split-rank-one-classification. The SL2, PGL2 and GL2 models have
   weights respectively ±2χ, ±χ and ±(e₁-e₂), each with one-dimensional weight space.
   The diagonal and central factors have weight zero, also in characteristic two.
   Comparing with step 3 proves the dimension and rational-line assertions.
7. In these models the map from SL2 has central kernel (respectively 1, μ₂, 1)
   and image the derived group. For PGL2, adjoining c with c² = det(g)⁻¹ is a
   faithfully flat rank-two extension, also in characteristic two. The upper
   unitriangular map is an isomorphism onto the root subgroup. The diagonal map
   factors through T and defines the asserted coroot cocharacter.
8. Normalizing matrices are diagonal or antidiagonal. For PGL2 lift a rational
   point to GL2 and normalize the full inverse-image diagonal torus. Thus the local
   normalizer quotient has exactly one nonidentity element. Its inclusion in the
   global quotient is injective because both denominators are T(F).
9. The antidiagonal representative inverts the SL2 diagonal coordinate and swaps
   the GL2 diagonal coordinates. On an integral character basis this is precisely
   x ↦ x - <x,α∨>α, with <α,α∨> = 2. Central-factor characters are fixed.
10. Two such cocharacters have difference pairing trivially with every character:
    α is nonzero and X is torsion free. Perfectness gives uniqueness. Conjugating
    T_α, G_α and the unique local reflection gives the corresponding objects for
    nα; pairing preservation and uniqueness then give coroot equivariance. -/
theorem reductive_rankOne_reflections
    {F : Type u} [Field F] [IsAlgClosed F]
    (G T : Grp (Over (Spec (.of F)))) (i : T ⟶ G)
    (hG : ReductiveTorusCentralizer.IsReductive G)
    (hT : ReductiveTorusCentralizer.IsMaximalTorus i) :
    ∃ (a : ModObj T.X G.X)
      (pairing : Character T → Cocharacter T → ℤ)
      (act : Weyl i →* Aut T),
      a.smul = adjointMap i ∧
      (∀ (χ : Character T) (ν : Cocharacter T),
        ν.hom.hom ≫ χ.hom.hom =
          (𝟙 (StandardGroupSchemes.multiplicative F)) ^ pairing χ ν) ∧
      (roots T G a).Finite ∧
      iSupIndep (weight T G a) ∧ (⨆ χ : Character T, weight T G a χ) = ⊤ ∧
      weight T G a 0 = (GrpObj.differential i.hom.hom).toLinearMap.range ∧
      Finite (Weyl i) ∧
      (∀ (n : normalizer i) (A : CommAlgCat.{u} F)
        (t : StandardGroupSchemes.affine F A ⟶ T.X),
        t ≫ (act (QuotientGroup.mk n)).hom.hom.hom ≫ i.hom.hom =
          (toUnit (StandardGroupSchemes.affine F A) ≫ n.val) * (t ≫ i.hom.hom) *
            (toUnit (StandardGroupSchemes.affine F A) ≫ n.val)⁻¹) ∧
      (∀ (w : Weyl i) (χ : Character T) (ν : Cocharacter T),
        pairing ((act w).inv ≫ χ) (ν ≫ (act w).hom) = pairing χ ν) ∧
      (∀ (w : Weyl i) (χ : Character T),
        (act w).inv ≫ χ ∈ roots T G a ↔ χ ∈ roots T G a) ∧
      ∃ (coroot : {α // α ∈ roots T G a} → Cocharacter T)
        (reflection : {α // α ∈ roots T G a} → Weyl i),
        (∀ α : {α // α ∈ roots T G a},
          pairing α.val (coroot α) = 2 ∧
          (∀ x : Character T,
            (act (reflection α)).inv.hom.hom ≫ x.hom.hom =
              x.hom.hom / α.val.hom.hom ^ pairing x (coroot α)) ∧
          (∀ ν : Cocharacter T,
            (∀ x : Character T,
              (act (reflection α)).inv.hom.hom ≫ x.hom.hom =
                x.hom.hom / α.val.hom.hom ^ pairing x ν) → ν = coroot α) ∧
          Module.finrank F (weight T G a α.val) = 1 ∧
          (∀ χ : Character T,
            (χ ∈ roots T G a ∧ ∃ m n : ℤ, n ≠ 0 ∧ χ.hom.hom ^ n = α.val.hom.hom ^ m) ↔
              χ = α.val ∨ χ.hom.hom = α.val.hom.hom⁻¹) ∧
          ∃ (S H : Grp (Over (Spec (.of F))))
            (s : S ⟶ Grp.mk (CategoryTheory.GrpObj.ker α.val.hom.hom))
            (h : H ⟶ G) (j : T ⟶ H) (v : SL2Hom H)
            (dG : Grp (Over (Spec (.of F)))) (d : dG ⟶ H)
            (upper : Grp.mk (StandardGroupSchemes.additive F) ⟶ H),
            MultiplicativeType.IsLargestSubtorus s ∧
            IsClosedSubgroupScheme h.hom.hom ∧ j ≫ h = i ∧
            ReductiveTorusCentralizer.IsReductive H ∧ HasSemisimpleRankOne H ∧
            (∀ A : CommAlgCat.{u} F,
              ReductiveTorusCentralizer.centralizerPoints
                (Grp.homMk (s.hom.hom ≫ CategoryTheory.GrpObj.kerι α.val.hom.hom) ≫ i) A =
                (pointImage h (StandardGroupSchemes.affine F A) : Set _)) ∧
            (∀ A : CommAlgCat.{u} F, (v.app A).ker ≤ Subgroup.center _) ∧
            IsDerivedGroupScheme d.hom.hom ∧ v.IsImage d ∧
            IsClosedSubgroupScheme upper.hom.hom ∧
            @TorusCharacterTangent.IsStable F _ T G a _ (upper ≫ h) ∧
            (GrpObj.differential (upper ≫ h).hom.hom).toLinearMap.range =
              weight T G a α.val ∧
            (∀ (A : CommAlgCat.{u} F)
              (p : StandardGroupSchemes.affine F A ⟶ StandardGroupSchemes.additive F)
              (g : Matrix.SpecialLinearGroup (Fin 2) A),
              g.val = !![1, (Scheme.ΓSpecIso (.of A)).hom
                (p.left.appTop ((Scheme.ΓSpecIso (.of (Polynomial F))).inv Polynomial.X));
                0, 1] → v.app A g = p ≫ upper.hom.hom) ∧
            (∀ (A : CommAlgCat.{u} F)
              (z : StandardGroupSchemes.affine F A ⟶ StandardGroupSchemes.multiplicative F)
              (g : Matrix.SpecialLinearGroup (Fin 2) A),
              g.val = !![multiplicativeValue A z, 0; 0, multiplicativeValue A z⁻¹] →
                v.app A g = z ≫ (coroot α).hom.hom ≫ j.hom.hom) ∧
            ∃ (localReflection : Weyl j) (nH : normalizer j) (nG : normalizer i),
              localReflection ≠ 1 ∧
              (∀ w : Weyl j, w ≠ 1 → w = localReflection) ∧
              QuotientGroup.mk nH = localReflection ∧
              nG.val = nH.val ≫ h.hom.hom ∧ QuotientGroup.mk nG = reflection α) ∧
        ∀ (w : Weyl i) (α β : {α // α ∈ roots T G a}),
          β.val = (act w).inv ≫ α.val → coroot β = coroot α ≫ (act w).hom := by
  sorry

end AlgebraicGeometry.RankOneRoots
