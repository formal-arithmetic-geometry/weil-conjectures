/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q50
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import Sheaf.AlgebraicGeometry.GroupScheme.BruhatLongestCellCharts
public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations
import Sheaf.AlgebraicGeometry.GroupScheme.BorelRootProductCoordinates

/-! # Simple Bruhat double-coset products

Source: Milne, Algebraic Groups (2017), Proposition 21.75 (T3), p.448;
Brion--Kumar, Frobenius Splitting Methods, Section 2.1 (4), p.62, and
Section 2.2, p.64 (blueprint: lem-sfb-simple-bruhat-double-coset-product).

The helpers express the minimum simple-word length and the specialization of
Mathlib's double coset to the actual Borel subgroup on test-scheme points.
The nonempty reduced-product assertion uses the ordinary subset monoid; the
empty-word convention is stated separately as D(1) = B, not as {1} = B.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj Pointwise

namespace AlgebraicGeometry

/-- Minimum length of a word in the specified simple reflections with product w.
For the Weyl group in the theorem below every element has such a word. The infimum
is a real construction, also defined on a family which does not generate.
Source: Milne, Appendix C.10--C.11, p.610.
(blueprint: lem-sfb-simple-bruhat-double-coset-product) -/
def simpleBruhatWordLength {I : Type v} {W : Type w} [Group W]
    (s : I → W) (x : W) : ℕ :=
  sInf {m | ∃ l : List I, l.length = m ∧ (l.map s).prod = x}

/-- The Borel double coset of a specified normalizer representative on A-points.
This specializes DoubleCoset.doubleCoset; its point sets are the existing pointImage.
Source: Milne, Proposition 21.75, p.448.
(blueprint: lem-sfb-simple-bruhat-double-coset-product) -/
def simpleBruhatDoubleCoset {F : Type u} [Field F]
    {G T B : Grp (Over (Spec (.of F)))} (iT : T ⟶ G) (iB : B ⟶ G)
    (n : RankOneRoots.normalizer iT) (A : Over (Spec (.of F))) : Set (A ⟶ G.X) :=
  DoubleCoset.doubleCoset (toUnit A ≫ n.val)
    (RankOneRoots.pointImage iB A) (RankOneRoots.pointImage iB A)

/-- Left multiplication by a simple Bruhat double coset gives one or two double
cosets according to the length change. These are the only possible changes.
Nonempty reduced words multiply to their double coset, and D(1) is the Borel.

Source: Milne, Proposition 21.75 (T3), p.448, and Appendix C.10--C.22,
pp.610--612; Brion--Kumar, Section 2.1 (4), p.62, and Section 2.2, p.64.
(blueprint: lem-sfb-simple-bruhat-double-coset-product)

Proof plan:
1. Apply semisimpleGroupScheme_isReductive. The nodes
   lem-sfb-weyl-reflection-realization and lem-sfb-simple-root-reflection-generation
   identify W with the root-reflection group and give a simple word for each w.
   Average a positive definite form over finite W. Simple reflections permute
   the positive roots other than their own root, by the sign expansions of
   lem-sfb-reductive-borel-pair-structure and reducedness.
2. Reversing words preserves length. By lem-sfb-root-sign-word-deletion, a negative
   inverse image of the simple root deletes one letter. Applying this to sw in
   the positive case proves exactly the two changes, including w = 1.
3. Use lem-sfb-reductive-root-subgroup-parametrizations to conjugate root groups.
   In lem-sfb-opposite-root-sl2-parametrizations choose the antidiagonal SL2 matrix
   n = [[0,-1],[1,0]]. It represents the simple reflection by its coroot action,
   has square in T and interchanges the opposite root groups. Representatives
   differing by T give the same double coset.
4. By lem-sfb-borel-root-product-coordinates write B = V U_alpha T, with V the
   ordered product of the other positive root groups. Then n V n^-1 is in B.
   Both inclusions give D_s D_w = B U_(-alpha) n n_w B. This set is B-biinvariant
   and contains n n_w, hence contains D_(sw).
5. If w^-1(alpha) is positive, conjugation by (n n_w)^-1 sends U_(-alpha) into B.
   The displayed product is then D_(sw), giving the increasing case.
6. If w^-1(alpha) is negative, the SL2 identity
   x_-(a) = x_+(a^-1) n diag(a,a^-1) x_+(a^-1), for a nonzero,
   puts each nonzero root parameter in D_w, while zero gives D_(sw).
   The root parametrization is bijective; taking a = 1 and B-biinvariance give
   all of D_w, proving the reverse inclusion as well. No characteristic is excluded.
7. Each suffix of a reduced word is reduced. Induct on nonempty word length and
   use the increasing formula. Finally n_1 is in T, so D_1 = B. In rank zero
   there are no simple reflections and only this identity remains. -/
theorem simple_bruhat_double_coset_product
    {F : Type u} [Field F] [IsAlgClosed F]
    (G T B : Grp (Over (Spec (.of F)))) (hG : IsSemisimpleGroupScheme G.X)
    (hsc : ∀ (G' : Over (Spec (.of F))) [GrpObj G'],
      IsSemisimpleGroupScheme G' → ∀ (f : G' ⟶ G.X) [IsMonHom f],
      Surjective f.left → IsFinite (GrpObj.ker f).hom →
      (∀ (A : Type u) [CommRing A] [Algebra F A]
        (x : StandardGroupSchemes.affine F A ⟶ GrpObj.ker f)
        (g : StandardGroupSchemes.affine F A ⟶ G'),
        (x ≫ GrpObj.kerι f) * g = g * (x ≫ GrpObj.kerι f)) → IsIso f)
    (iT : T ⟶ G) (hT : ReductiveTorusCentralizer.IsMaximalTorus iT)
    (hsplit : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    (iB : B ⟶ G) (hB : IsBorelGroupScheme iB.hom.hom)
    (j : T ⟶ B) (hj : j ≫ iB = iT)
    [IsCommMonObj T.X] [IsCommMonObj (StandardGroupSchemes.multiplicative F)]
    (aG : ModObj T.X G.X) (aB : ModObj T.X B.X)
    (haG : aG.smul = (iT.hom.hom ⊗ₘ 𝟙 G.X) ≫ GrpObj.conj G.X)
    (haB : aB.smul = (j.hom.hom ⊗ₘ 𝟙 B.X) ≫ GrpObj.conj B.X)
    (Φ : Finset (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))))
    (D : RootDatum Φ
      (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)))
    (base : D.Base) (hred : D.IsReduced)
    (hroot : ∀ α : Φ, D.root α = α.val)
    (hpair : ∀ (χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (ν : Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)),
      ν.toMul.hom.hom ≫ χ.toMul.hom.hom =
        (𝟙 (StandardGroupSchemes.multiplicative F)) ^ (D.toLinearMap χ ν))
    (hΦ : ∀ χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
      χ ∈ Φ ↔ χ ≠ 0 ∧ @TorusCharacterTangent.weightSpace F _ T G aG χ.toMul ≠ ⊥)
    (hpos : ∀ α : Φ,
      base.IsPos α ↔ @TorusCharacterTangent.weightSpace F _ T B aB α.val.toMul ≠ ⊥)
    (act : RankOneRoots.Weyl iT →* Aut T)
    (hact : ∀ (n : RankOneRoots.normalizer iT) (A : Over (Spec (.of F))) (t : A ⟶ T.X),
      t ≫ (act (QuotientGroup.mk n)).hom.hom.hom ≫ iT.hom.hom =
        (toUnit A ≫ n.val) * (t ≫ iT.hom.hom) * (toUnit A ≫ n.val)⁻¹)
    (s : base.support → RankOneRoots.Weyl iT)
    (hs : ∀ (α : base.support) (χ : RankOneRoots.Character T),
      (act (s α)).inv ≫ χ = (D.reflection α.val (Additive.ofMul χ)).toMul)
    (n : RankOneRoots.Weyl iT → RankOneRoots.normalizer iT)
    (hn : ∀ w, QuotientGroup.mk (n w) = w)
    (K : Type u) [Field K] [Algebra F K] [IsAlgClosed K] :
    (∀ (α : base.support) (w : RankOneRoots.Weyl iT),
      (simpleBruhatWordLength s (s α * w) = simpleBruhatWordLength s w + 1 ∨
        simpleBruhatWordLength s (s α * w) + 1 = simpleBruhatWordLength s w) ∧
      (simpleBruhatWordLength s (s α * w) = simpleBruhatWordLength s w + 1 →
        simpleBruhatDoubleCoset iT iB (n (s α)) (StandardGroupSchemes.affine F K) *
          simpleBruhatDoubleCoset iT iB (n w) (StandardGroupSchemes.affine F K) =
        simpleBruhatDoubleCoset iT iB (n (s α * w)) (StandardGroupSchemes.affine F K)) ∧
      (simpleBruhatWordLength s (s α * w) + 1 = simpleBruhatWordLength s w →
        simpleBruhatDoubleCoset iT iB (n (s α)) (StandardGroupSchemes.affine F K) *
          simpleBruhatDoubleCoset iT iB (n w) (StandardGroupSchemes.affine F K) =
        simpleBruhatDoubleCoset iT iB (n (s α * w)) (StandardGroupSchemes.affine F K) ∪
          simpleBruhatDoubleCoset iT iB (n w) (StandardGroupSchemes.affine F K))) ∧
    (∀ l : List base.support, l ≠ [] →
      l.length = simpleBruhatWordLength s (l.map s).prod →
      (l.map (fun α ↦ simpleBruhatDoubleCoset iT iB (n (s α))
        (StandardGroupSchemes.affine F K))).prod =
      simpleBruhatDoubleCoset iT iB (n (l.map s).prod) (StandardGroupSchemes.affine F K)) ∧
    simpleBruhatDoubleCoset iT iB (n 1) (StandardGroupSchemes.affine F K) =
      (RankOneRoots.pointImage iB (StandardGroupSchemes.affine F K) : Set _) := by
  sorry

end AlgebraicGeometry
