/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.AlgebraicGeometry.PicardExternalCupCochain
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Homology.ExactSequence

/-! # Exact homology ladders for external cup in the right coefficient

Source: Stacks Project, Varieties, Tag 0BED, the short exact sequence argument
following equation 33.29.1.1, applied in the right variable.
(blueprint: lem-sc-picard-external-cup-right-exact-ladder).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

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
          IsIso (ComposableArrows.app' φ 3) ∧ IsIso (ComposableArrows.app' φ 4)) := by sorry

end AlgebraicGeometry.Scheme.Modules
