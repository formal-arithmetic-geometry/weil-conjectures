/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.AlgebraicGeometry.PicardExternalCupCochain
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Homology.ExactSequence

import Sheaf.AlgebraicGeometry.PicardExternalCupLeftComparisonComplexes
import Sheaf.Algebra.Homology.TensorKunnethNat
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! # The external-cup five-term homology ladder in the left coefficient

Source: Stacks Project, Varieties, Tag 0BED, lemma-kunneth, paragraph on short
exact coefficient sequences after equation-kunneth-on-cech.
(blueprint: lem-sc-picard-external-cup-left-homology-ladder).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

private theorem normalized_homology_eq
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules)
    (c d : picardExternalTotal f g F G ⟶
      picardScalarModel (pullback.fst f g ≫ f) (externalCupCoefficients f g F G))
    (hc : IsPicardExternalCupCochain f g F G c)
    (hd : IsPicardExternalCupCochain f g F G d) (n : ℕ) :
    HomologicalComplex.homologyMap c (n : ℤ) =
      HomologicalComplex.homologyMap d (n : ℤ) := by
  classical
  obtain ⟨e, he⟩ := HomologicalComplex.tensor_kunneth_nat
    (picardScalarModel f F) (picardScalarModel g G)
    (picardScalarModel_negative f F) (picardScalarModel_negative g G) n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := e.surjective x
  have H :
      (HomologicalComplex.homologyMap c (n : ℤ)).hom.comp e.toLinearMap =
        (HomologicalComplex.homologyMap d (n : ℤ)).hom.comp e.toLinearMap := by
    apply DirectSum.linearMap_ext
    intro i
    ext a b
    obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective
      ((picardScalarModel f F).homologyπ (i.val.1 : ℤ))).mp inferInstance a
    obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective
      ((picardScalarModel g G).homologyπ (i.val.2 : ℤ))).mp inferInstance b
    obtain ⟨z, hz, hez⟩ := he i a b
    change HomologicalComplex.homologyMap c (n : ℤ) (e (DirectSum.lof k _ _ i _)) =
      HomologicalComplex.homologyMap d (n : ℤ) (e (DirectSum.lof k _ _ i _))
    simp only [TensorProduct.mk_apply] at *
    rw [hez]
    apply (picardScalarModelEquiv (pullback.fst f g ≫ f)
      (externalCupCoefficients f g F G) n).injective
    exact (hc n i a b z hz).trans (hd n i a b z hz).symm
  exact LinearMap.congr_fun H x

private theorem isIso_of_comparison_square
    {k : Type w} [Field k] {A B C D : ModuleCat.{w} k}
    (u : A ⟶ B) (v : C ⟶ D) (a : A ≅ C) (b : B ≅ D)
    (h : u ≫ b.hom = a.hom ≫ v) (hv : IsIso v) : IsIso u := by
  have := hv
  apply (isIso_comp_right_iff u b.hom).mp
  rw [h]
  infer_instance

/-- A short exact sequence of quasi-coherent left coefficients gives an exact
five-term ladder centered at any specified normalized external-cup homology map.
The outer maps inherit invertibility from the middle and quotient comparisons;
no invertibility of the central map, acyclicity, or cohomological bound is assumed.
Source: Stacks Project, Varieties, Tag 0BED, lemma-kunneth, the short exact
sequence paragraph after equation-kunneth-on-cech.
(blueprint: lem-sc-picard-external-cup-left-homology-ladder).

Proof: Choose finite affine covers of X and Y and their product cover. Affine
finite intersections follow from the affine diagonals. Apply sections on these
intersections to S. Exactness of affine sections on quasi-coherent modules gives
short exact sequences of Cech complexes. The affine pullback and tensor section
formulas give the corresponding product-coefficient sequence; tensoring over the
field is exact. The signed refinement and cup maps therefore form a morphism
between the two short exact sequences of complexes. The natural long exact
homology sequences commute also at the connecting maps, since they come from a
morphism of short exact complexes. Compare affine Cech homology with module
cohomology, naturally in coefficients, and compare the resolution scalar models.
Tensor Kunneth and the cycle formula identify the transported source homology
with the homology of picardExternalTotal. Every factor homology class has a cycle
representative, and elementary tensors span each summand, so normalization
identifies each of the three specified maps on all homology classes. For n>0 take
the segment
H^(n-1)(E) -> H^(n-1)(Q) -> H^n(F) -> H^n(E) -> H^n(Q) in each row,
with E=S.X₂ and Q=S.X₃; here the source row is tensor-total homology and the
target row is product-coefficient homology. For n=0 replace the first two terms
by zero objects and begin at H^0(F). Both rows are exact at their three interior
terms. The central comparison is conjugate to homologyMap c by the two model
comparison isomorphisms. The four outer comparisons are conjugates of
homologyMap cE and homologyMap cQ in degrees n-1 and n, respectively; in the
initial segment the first two are identities of zero objects. Consequently
invertibility of cE in every natural degree implies invertibility at positions
0 and 3, and the corresponding hypothesis on cQ gives positions 1 and 4.
We return this diagram and its identifications without applying the five lemma.
This construction includes empty schemes and zero coefficients; it does not
assume that the quotient has vanishing degree-zero cohomology. -/
theorem picardExternalCupCochain_left_homology_ladder
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (G : Y.Modules) [G.IsQuasicoherent]
    (cE : picardExternalTotal f g S.X₂ G ⟶
      picardScalarModel (pullback.fst f g ≫ f) (externalCupCoefficients f g S.X₂ G))
    (hcE : IsPicardExternalCupCochain f g S.X₂ G cE)
    (cQ : picardExternalTotal f g S.X₃ G ⟶
      picardScalarModel (pullback.fst f g ≫ f) (externalCupCoefficients f g S.X₃ G))
    (hcQ : IsPicardExternalCupCochain f g S.X₃ G cQ)
    (c : picardExternalTotal f g S.X₁ G ⟶
      picardScalarModel (pullback.fst f g ≫ f) (externalCupCoefficients f g S.X₁ G))
    (hc : IsPicardExternalCupCochain f g S.X₁ G c) (n : ℕ) :
    ∃ (R₁ R₂ : ComposableArrows (ModuleCat.{w} k) 4) (φ : R₁ ⟶ R₂)
      (e₁ : R₁.obj' 2 ≅ (picardExternalTotal f g S.X₁ G).homology (n : ℤ))
      (e₂ : R₂.obj' 2 ≅
        (picardScalarModel (pullback.fst f g ≫ f)
          (externalCupCoefficients f g S.X₁ G)).homology (n : ℤ)),
      R₁.Exact ∧ R₂.Exact ∧
      ((∀ r : ℕ, IsIso (HomologicalComplex.homologyMap cE (r : ℤ))) →
        IsIso (ComposableArrows.app' φ 0) ∧ IsIso (ComposableArrows.app' φ 3)) ∧
      ((∀ r : ℕ, IsIso (HomologicalComplex.homologyMap cQ (r : ℤ))) →
        IsIso (ComposableArrows.app' φ 1) ∧ IsIso (ComposableArrows.app' φ 4)) ∧
      ComposableArrows.app' φ 2 ≫ e₂.hom =
        e₁.hom ≫ HomologicalComplex.homologyMap c (n : ℤ) := by
  obtain ⟨d1, d2, d3, hd1, hd2, hd3, A, B, hA, hB, ψ, hneg, hmodel⟩ :=
    picardExternalCup_left_comparison_complexes k X Y f g S hS G
  have h₂ (r : ℕ) (hE : IsIso (HomologicalComplex.homologyMap cE (r : ℤ))) :
      IsIso (HomologicalComplex.homologyMap ψ.τ₂ (r : ℤ)) := by
    obtain ⟨a1, a2, a3, b1, b2, b3, h1, h2, h3⟩ := hmodel r
    rw [← normalized_homology_eq f g S.X₂ G cE d2 hcE hd2 r] at h2
    exact isIso_of_comparison_square _ _ a2 b2 h2 hE
  have h₃ (r : ℕ) (hQ : IsIso (HomologicalComplex.homologyMap cQ (r : ℤ))) :
      IsIso (HomologicalComplex.homologyMap ψ.τ₃ (r : ℤ)) := by
    obtain ⟨a1, a2, a3, b1, b2, b3, h1, h2, h3⟩ := hmodel r
    rw [← normalized_homology_eq f g S.X₃ G cQ d3 hcQ hd3 r] at h3
    exact isIso_of_comparison_square _ _ a3 b3 h3 hQ
  have hprev₂ (hE : ∀ r : ℕ, IsIso (HomologicalComplex.homologyMap cE (r : ℤ))) :
      IsIso (HomologicalComplex.homologyMap ψ.τ₂ ((n : ℤ) - 1)) := by
    cases n with
    | zero =>
      obtain ⟨hA2, hA3, hB2, hB3⟩ := hneg (-1) (by norm_num)
      exact ((A.X₂.sc (-1)).isZero_homology_of_isZero_X₂ hA2).isIso
        ((B.X₂.sc (-1)).isZero_homology_of_isZero_X₂ hB2) _
    | succ r =>
      rw [show ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) by omega]
      exact h₂ r (hE r)
  have hprev₃ (hQ : ∀ r : ℕ, IsIso (HomologicalComplex.homologyMap cQ (r : ℤ))) :
      IsIso (HomologicalComplex.homologyMap ψ.τ₃ ((n : ℤ) - 1)) := by
    cases n with
    | zero =>
      obtain ⟨hA2, hA3, hB2, hB3⟩ := hneg (-1) (by norm_num)
      exact ((A.X₃.sc (-1)).isZero_homology_of_isZero_X₂ hA3).isIso
        ((B.X₃.sc (-1)).isZero_homology_of_isZero_X₂ hB3) _
    | succ r =>
      rw [show ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) by omega]
      exact h₃ r (hQ r)
  let hij : (ComplexShape.up ℤ).Rel ((n : ℤ) - 1) (n : ℤ) := by
    change (n : ℤ) - 1 + 1 = (n : ℤ)
    omega
  let R₁ := (HomologicalComplex.HomologySequence.composableArrows₅ hA
    ((n : ℤ) - 1) (n : ℤ) hij).δ₀
  let R₂ := (HomologicalComplex.HomologySequence.composableArrows₅ hB
    ((n : ℤ) - 1) (n : ℤ) hij).δ₀
  let φ : R₁ ⟶ R₂ := ComposableArrows.δ₀Functor.map
    (HomologicalComplex.HomologySequence.mapComposableArrows₅ ψ hA hB
      ((n : ℤ) - 1) (n : ℤ) hij)
  obtain ⟨a1, a2, a3, b1, b2, b3, h1, h2, h3⟩ := hmodel n
  refine ⟨R₁, R₂, φ, a1, b1, ?_, ?_, ?_, ?_, ?_⟩
  · exact (HomologicalComplex.HomologySequence.composableArrows₅_exact hA
      ((n : ℤ) - 1) (n : ℤ) hij).δ₀
  · exact (HomologicalComplex.HomologySequence.composableArrows₅_exact hB
      ((n : ℤ) - 1) (n : ℤ) hij).δ₀
  · intro hE
    exact ⟨hprev₂ hE, h₂ n (hE n)⟩
  · intro hQ
    exact ⟨hprev₃ hQ, h₃ n (hQ n)⟩
  · change HomologicalComplex.homologyMap ψ.τ₁ (n : ℤ) ≫ b1.hom =
      a1.hom ≫ HomologicalComplex.homologyMap c (n : ℤ)
    rw [normalized_homology_eq f g S.X₁ G c d1 hc hd1 n]
    exact h1

end AlgebraicGeometry.Scheme.Modules
