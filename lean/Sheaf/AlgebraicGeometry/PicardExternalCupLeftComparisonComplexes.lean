/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import Sheaf.AlgebraicGeometry.PicardExternalCupCochain
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Sheaf.Algebra.Homology.TensorKunnethNat
import Sheaf.AlgebraicGeometry.ModuleCechComparisonIsoAffine
import Sheaf.AlgebraicGeometry.ModulePullbackAffineSections
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import Sheaf.AlgebraicGeometry.PicardKunnethResolutionModel
import Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
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
              a3.hom ≫ HomologicalComplex.homologyMap d3 (n : ℤ) := by sorry

end AlgebraicGeometry.Scheme.Modules
