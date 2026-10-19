/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import Sheaf.AlgebraicGeometry.PicardExternalCupCochain
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

import Sheaf.AlgebraicGeometry.PicardExternalCupLeftCechComparison
import WeilConjectures.Algebra.Homology.TensorKunnethNat
import Sheaf.AlgebraicGeometry.ModuleCechComparisonIsoAffine
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import Sheaf.AlgebraicGeometry.PicardKunnethResolutionModel
import Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import Sheaf.Paper.CechComparisonMapNaturality
import Sheaf.Paper.CechCupProduct
import Sheaf.Paper.CechCupPullbackCompat
import Sheaf.Paper.CechRefinementCochainMap
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Short exact comparison complexes for external cup in the left coefficient

Source: Stacks Project, Varieties, Tag 0BED, lemma-kunneth, the short exact
coefficient diagram following equation-kunneth-on-cech (33.29.1.1).
(blueprint: lem-sc-picard-external-cup-left-comparison-complexes).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

private theorem extend_negative
    {k : Type w} [Field k] (C : CochainComplex (ModuleCat.{w} k) ℕ)
    (p : ℤ) (hp : p < 0) :
    IsZero ((C.extend ComplexShape.embeddingUpNat).X p) := by
  apply HomologicalComplex.isZero_extend_X
  intro n hn
  change (n : ℤ) = p at hn
  omega

private theorem tensor_negative
    {k : Type w} [Field k] (A B : CochainComplex (ModuleCat.{w} k) ℤ)
    (hA : ∀ p : ℤ, p < 0 → IsZero (A.X p))
    (hB : ∀ p : ℤ, p < 0 → IsZero (B.X p))
    (n : ℤ) (hn : n < 0) :
    IsZero ((HomologicalComplex.mapBifunctor A B
      (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat.{w} k))
        (ComplexShape.up ℤ)).X n) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  change p + q = n at hpq
  have hz : IsZero
      (((CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat.{w} k)).obj
        (A.X p)).obj (B.X q)) := by
    by_cases hp : p < 0
    · exact (CategoryTheory.MonoidalCategory.tensorRight (B.X q)).map_isZero (hA p hp)
    · exact (CategoryTheory.MonoidalCategory.tensorLeft (A.X p)).map_isZero
        (hB q (by omega))
  simp only [Category.comp_id, comp_zero]
  exact hz.eq_zero_of_src _

set_option linter.unusedVariables false in
/-- Construct the morphism of short exact comparison complexes before taking a
long exact sequence. No specified external-cup map or cohomological degree is an
input. The chosen normalized maps describe the three components on homology.

Source: Stacks Project, Varieties, Tag 0BED, lemma-kunneth, short exact coefficient
sequence diagram after equation-kunneth-on-cech; Cohomology, Tags 01FD, 07MB, 0FKV.
(blueprint: lem-sc-picard-external-cup-left-comparison-complexes).

Proof:
1. Choose finite affine covers U of X and V of Y. The affine-diagonal criterion
makes all finite intersections affine. Use their product cover W of X times Y.
On each affine intersection the quasi-coherent sequence S is exact on sections:
sections preserve kernels, and quasi-coherent cokernel sections are the module
cokernel. The affine pullback and tensor section formulas identify product
coefficient sections with tensor products over k of the two factor sections.
Pullback preserves quasi-coherence; its adjunction identifies the standard
pullback with tensorPullback. Tensor-product quasi-coherence makes all the external
coefficients quasi-coherent, so the affine comparisons apply to them as well.
Tensoring over a field preserves short exact sequences. Products over the finite
cover index sets and the finite sums in each total degree preserve exactness.
Thus the tensor-total Cech complexes form A, and the product Cech complexes form
B, both short exact. Extend these natural-index complexes by zero to integers.
Their terms in negative degrees are zero, including those of the middle and
quotient coefficients required here.
2. Refine the two pulled-back covers to W and apply the signed Cech cup map.
The formulas commute with the coefficient maps S.f and S.g; hence their three
components form a short-complex morphism phi from A to B. This is a cochain-level
construction, before any connecting homomorphism is taken.
3. In each natural degree compare affine Cech cohomology to module cohomology
and then to the fixed scalar resolution model. Scalar restriction is exact. For
A, use tensor Kunneth on both the Cech and scalar complexes, with the factor
comparison isomorphisms. This gives a1,a2,a3 and b1,b2,b3. The refinement and cup
compatibility squares identify the transported component of phi on every pair
of factor cycles with externalCup. Tensor Kunneth supplies the corresponding
total cycle. Factor homology projections are surjective and pure tensors span
each summand, so this determines the transported map on all classes.
4. Choose normalized d1,d2,d3 using picardExternalCupCochain_exists. Their
normalization gives exactly the same formula on the spanning tensor cycles.
Consequently each transported component of phi is H(dj), giving the three
stated equalities simultaneously in every natural degree. These are arbitrary
existential witnesses used in a proof, not data defining a library object.
No invertibility of a cup map, cohomological bound, or five lemma is used. Empty
covers and zero coefficients give zero complexes and satisfy the same formulas. -/
theorem picardExternalCup_left_comparison_complexes
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (G : Y.Modules) [G.IsQuasicoherent]
 :
    ∃ (d1 : picardExternalTotal f g S.X₁ G ⟶
        picardScalarModel (pullback.fst f g ≫ f) (externalCupCoefficients f g S.X₁ G))
      (d2 : picardExternalTotal f g S.X₂ G ⟶
        picardScalarModel (pullback.fst f g ≫ f) (externalCupCoefficients f g S.X₂ G))
      (d3 : picardExternalTotal f g S.X₃ G ⟶
        picardScalarModel (pullback.fst f g ≫ f) (externalCupCoefficients f g S.X₃ G)),
      IsPicardExternalCupCochain f g S.X₁ G d1 ∧
      IsPicardExternalCupCochain f g S.X₂ G d2 ∧
      IsPicardExternalCupCochain f g S.X₃ G d3 ∧
      ∃ (A B : ShortComplex (CochainComplex (ModuleCat.{w} k) ℤ))
        (hA : A.ShortExact) (hB : B.ShortExact) (φ : A ⟶ B),
        (∀ p : ℤ, p < 0 →
          IsZero (A.X₂.X p) ∧ IsZero (A.X₃.X p) ∧
          IsZero (B.X₂.X p) ∧ IsZero (B.X₃.X p)) ∧
        ∀ n : ℕ,
          ∃ (a1 : A.X₁.homology (n : ℤ) ≅ (picardExternalTotal f g S.X₁ G).homology
              (n : ℤ))
            (a2 : A.X₂.homology (n : ℤ) ≅ (picardExternalTotal f g S.X₂ G).homology
              (n : ℤ))
            (a3 : A.X₃.homology (n : ℤ) ≅ (picardExternalTotal f g S.X₃ G).homology
              (n : ℤ))
            (b1 : B.X₁.homology (n : ℤ) ≅
              (picardScalarModel (pullback.fst f g ≫ f)
                (externalCupCoefficients f g S.X₁ G)).homology (n : ℤ))
            (b2 : B.X₂.homology (n : ℤ) ≅
              (picardScalarModel (pullback.fst f g ≫ f)
                (externalCupCoefficients f g S.X₂ G)).homology (n : ℤ))
            (b3 : B.X₃.homology (n : ℤ) ≅
              (picardScalarModel (pullback.fst f g ≫ f)
                (externalCupCoefficients f g S.X₃ G)).homology (n : ℤ)),
            HomologicalComplex.homologyMap φ.τ₁ (n : ℤ) ≫ b1.hom =
              a1.hom ≫ HomologicalComplex.homologyMap d1 (n : ℤ) ∧
            HomologicalComplex.homologyMap φ.τ₂ (n : ℤ) ≫ b2.hom =
              a2.hom ≫ HomologicalComplex.homologyMap d2 (n : ℤ) ∧
            HomologicalComplex.homologyMap φ.τ₃ (n : ℤ) ≫ b3.hom =
              a3.hom ≫ HomologicalComplex.homologyMap d3 (n : ℤ) := by
  obtain ⟨d1, hd1⟩ := picardExternalCupCochain_exists f g S.X₁ G
  obtain ⟨d2, hd2⟩ := picardExternalCupCochain_exists f g S.X₂ G
  obtain ⟨d3, hd3⟩ := picardExternalCupCochain_exists f g S.X₃ G
  obtain ⟨hA, hB⟩ := picardExternalCup_left_cech_exact f g S hS G
  obtain ⟨θ, hθ⟩ := picardExternalCup_left_cech_comparison f g G
  let A := S.map (picardLeftTensorCechFunctor f g G)
  let B := S.map (picardLeftProductCechFunctor f g G)
  let φ : A ⟶ B := S.mapNatTrans θ
  refine ⟨d1, d2, d3, hd1, hd2, hd3, A, B, hA, hB, φ, ?_, ?_⟩
  · intro p hp
    have hT (F : X.Modules) :
        IsZero (((picardLeftTensorCechFunctor f g G).obj F).X p) := by
      exact tensor_negative _ _ (extend_negative _) (extend_negative _) p hp
    have hP (F : X.Modules) :
        IsZero (((picardLeftProductCechFunctor f g G).obj F).X p) := by
      exact extend_negative _ p hp
    exact ⟨hT S.X₂, hT S.X₃, hP S.X₂, hP S.X₃⟩
  · intro n
    obtain ⟨a1, b1, h1⟩ := hθ S.X₁ inferInstance d1 hd1 n
    obtain ⟨a2, b2, h2⟩ := hθ S.X₂ inferInstance d2 hd2 n
    obtain ⟨a3, b3, h3⟩ := hθ S.X₃ inferInstance d3 hd3 n
    exact ⟨a1, a2, a3, b1, b2, b3, h1, h2, h3⟩

end AlgebraicGeometry.Scheme.Modules
