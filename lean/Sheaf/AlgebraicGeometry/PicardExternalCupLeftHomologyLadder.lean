/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.AlgebraicGeometry.PicardExternalCupCochain
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Homology.ExactSequence

/-! # The external-cup five-term homology ladder in the left coefficient

Source: Stacks Project, Varieties, Tag 0BED, lemma-kunneth, paragraph on short
exact coefficient sequences after equation-kunneth-on-cech.
(blueprint: lem-sc-picard-external-cup-left-homology-ladder).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

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
        e₁.hom ≫ HomologicalComplex.homologyMap c (n : ℤ) := by sorry

end AlgebraicGeometry.Scheme.Modules
