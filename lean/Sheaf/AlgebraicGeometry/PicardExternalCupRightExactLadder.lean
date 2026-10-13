/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.AlgebraicGeometry.PicardExternalCupCochain
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Homology.ExactSequence

import Sheaf.Algebra.Homology.TensorKunnethNat
import Sheaf.AlgebraicGeometry.PicardExternalCupRightCechDiagram
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! # Exact homology ladders for external cup in the right coefficient

Source: Stacks Project, Varieties, Tag 0BED, the short exact sequence argument
following equation 33.29.1.1, applied in the right variable.
(blueprint: lem-sc-picard-external-cup-right-exact-ladder).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

private theorem normalized_homology_unique
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
  let A := picardScalarModel f F
  let B := picardScalarModel g G
  obtain ⟨e, he⟩ := HomologicalComplex.tensor_kunneth_nat A B
    (picardScalarModel_negative f F) (picardScalarModel_negative g G) n
  apply ModuleCat.hom_ext
  apply (LinearMap.cancel_right e.surjective).mp
  apply DirectSum.linearMap_ext
  intro i
  apply TensorProduct.ext'
  intro a b
  obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective (A.homologyπ (i.val.1 : ℤ))).mp
    inferInstance a
  obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective (B.homologyπ (i.val.2 : ℤ))).mp
    inferInstance b
  obtain ⟨z, hz, hez⟩ := he i a b
  change HomologicalComplex.homologyMap c (n : ℤ)
      (e (DirectSum.lof k _ _ i
        (TensorProduct.tmul k (A.homologyπ (i.val.1 : ℤ) a)
          (B.homologyπ (i.val.2 : ℤ) b)))) =
    HomologicalComplex.homologyMap d (n : ℤ)
      (e (DirectSum.lof k _ _ i
        (TensorProduct.tmul k (A.homologyπ (i.val.1 : ℤ) a)
          (B.homologyπ (i.val.2 : ℤ) b))))
  rw [hez]
  apply (picardScalarModelEquiv (pullback.fst f g ≫ f)
    (externalCupCoefficients f g F G) n).injective
  exact (hc n i a b z hz).trans (hd n i a b z hz).symm

/-- The external-cup comparison gives an exact five-term homology ladder for a
short exact sequence of right coefficients. Its middle vertical arrow is the
specified comparison on the first coefficient, conjugated by isomorphisms. If
the comparisons for the other two coefficients are invertible in all natural
degrees, the four outside arrows of this ladder are invertible. This statement
constructs the ladder; it does not assert invertibility of the middle arrow.

Source: Stacks Project, Varieties, Tag 0BED, the short exact sequence paragraph
following equation 33.29.1.1, applied in the right variable.
(blueprint: lem-sc-picard-external-cup-right-exact-ladder).

Proof:
1. Choose finite affine covers of X and Y and their product cover. Affine diagonal
makes finite intersections affine. Sections on these intersections preserve the
quasi-coherent sequence S. Tensoring vector spaces over k is exact. The finite
sums in each total degree therefore give a short exact sequence of tensor-total
Cech complexes. The affine pullback and tensor section formulas also give a short
exact sequence of product Cech complexes for the external coefficients.
2. Refinement and the signed Cech cup pairing are natural in S, so the map of
33.29.1.1 gives a morphism of the two short exact sequences. Their long exact
homology sequences form a commuting ladder, including the connecting arrows.
Take its five-term segment with the first coefficient in the middle; its other
terms are the middle and quotient coefficients in degrees n-1 and n. For n=0,
replace the first two terms by zero, using nonnegativity of the Cech complexes.
3. Transport the middle objects to the scalar models by the affine Cech and
resolution comparisons to obtain eA and eB. Tensor Kunneth's cycle formula,
surjectivity of factor homology projections, and the normalizations hc1, hc2,
hc3 identify the transported vertical maps with homology of the specified maps:
pure tensors span each tensor summand. This proves the middle-arrow equation.
4. The same identification shows that the outside vertical arrows are conjugate
to homology of c2 and c3 in degrees n-1 and n. If these maps are invertible in
every natural degree, so are the outside arrows. In degree zero the first two
arrows are maps between zero objects and are invertible directly. No induction
or cohomological bound is used. Empty covers, zero coefficients, and n=0 cause
no exception: all negative terms and their homology are zero. -/
theorem picardExternalCupCochain_right_exact_ladder
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    (F : X.Modules) [F.IsQuasicoherent]
    (S : ShortComplex Y.Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (c1 : picardExternalTotal f g F S.X₁ ⟶
      picardScalarModel (pullback.fst f g ≫ f) (externalCupCoefficients f g F S.X₁))
    (hc1 : IsPicardExternalCupCochain f g F S.X₁ c1)
    (c2 : picardExternalTotal f g F S.X₂ ⟶
      picardScalarModel (pullback.fst f g ≫ f) (externalCupCoefficients f g F S.X₂))
    (hc2 : IsPicardExternalCupCochain f g F S.X₂ c2)
    (c3 : picardExternalTotal f g F S.X₃ ⟶
      picardScalarModel (pullback.fst f g ≫ f) (externalCupCoefficients f g F S.X₃))
    (hc3 : IsPicardExternalCupCochain f g F S.X₃ c3)
    (n : ℕ) :
    ∃ (A B : ComposableArrows (ModuleCat.{w} k) 4) (φ : A ⟶ B)
      (eA : A.obj' 2 ≅ (picardExternalTotal f g F S.X₁).homology (n : ℤ))
      (eB : B.obj' 2 ≅
        (picardScalarModel (pullback.fst f g ≫ f)
          (externalCupCoefficients f g F S.X₁)).homology (n : ℤ)),
      A.Exact ∧ B.Exact ∧
      ComposableArrows.app' φ 2 =
        eA.hom ≫ HomologicalComplex.homologyMap c1 (n : ℤ) ≫ eB.inv ∧
      ((∀ m : ℕ, IsIso (HomologicalComplex.homologyMap c2 (m : ℤ))) →
        (∀ m : ℕ, IsIso (HomologicalComplex.homologyMap c3 (m : ℤ))) →
        IsIso (ComposableArrows.app' φ 0) ∧ IsIso (ComposableArrows.app' φ 1) ∧
          IsIso (ComposableArrows.app' φ 3) ∧ IsIso (ComposableArrows.app' φ 4)) := by
  classical
  obtain ⟨d1, d2, d3, T, U, ψ, a1, b1, a2, b2, a3, b3,
    hd1, hd2, hd3, hT, hU, hneg, h1, h2, h3⟩ :=
    picardExternalCup_right_cech_diagram k X Y f g F S hS
  let i : ℤ := (n : ℤ) - 1
  have hij : (ComplexShape.up ℤ).Rel i (n : ℤ) := by
    change i + 1 = (n : ℤ)
    dsimp [i]
    omega
  let A := (HomologicalComplex.HomologySequence.composableArrows₅ hT i (n : ℤ) hij).δ₀
  let B := (HomologicalComplex.HomologySequence.composableArrows₅ hU i (n : ℤ) hij).δ₀
  let φ : A ⟶ B := ComposableArrows.δ₀Functor.map
    (HomologicalComplex.HomologySequence.mapComposableArrows₅ ψ hT hU i (n : ℤ) hij)
  refine ⟨A, B, φ, a1 n, b1 n,
    (HomologicalComplex.HomologySequence.composableArrows₅_exact hT i (n : ℤ) hij).δ₀,
    (HomologicalComplex.HomologySequence.composableArrows₅_exact hU i (n : ℤ) hij).δ₀,
    ?_, ?_⟩
  · change HomologicalComplex.homologyMap ψ.τ₁ (n : ℤ) = _
    rw [h1, normalized_homology_unique f g F S.X₁ d1 c1 hd1 hc1 n]
  · intro hc2iso hc3iso
    have h₂ (m : ℕ) : IsIso (HomologicalComplex.homologyMap ψ.τ₂ (m : ℤ)) := by
      have := hc2iso m
      rw [h2, normalized_homology_unique f g F S.X₂ d2 c2 hd2 hc2 m]
      infer_instance
    have h₃ (m : ℕ) : IsIso (HomologicalComplex.homologyMap ψ.τ₃ (m : ℤ)) := by
      have := hc3iso m
      rw [h3, normalized_homology_unique f g F S.X₃ d3 c3 hd3 hc3 m]
      infer_instance
    have hi₂ : IsIso (HomologicalComplex.homologyMap ψ.τ₂ i) := by
      cases n with
      | zero =>
        obtain ⟨hT₂, _, hU₂, _⟩ := hneg (-1) (by omega)
        exact hT₂.isIso hU₂ _
      | succ m =>
        have hi : i = (m : ℤ) := by dsimp [i]; omega
        rw [hi]
        exact h₂ m
    have hi₃ : IsIso (HomologicalComplex.homologyMap ψ.τ₃ i) := by
      cases n with
      | zero =>
        obtain ⟨_, hT₃, _, hU₃⟩ := hneg (-1) (by omega)
        exact hT₃.isIso hU₃ _
      | succ m =>
        have hi : i = (m : ℤ) := by dsimp [i]; omega
        rw [hi]
        exact h₃ m
    exact ⟨hi₂, hi₃, h₂ n, h₃ n⟩

end AlgebraicGeometry.Scheme.Modules
