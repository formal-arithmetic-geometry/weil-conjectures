/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.AlgebraicGeometry.PicardExternalCupCochain
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Homology.HomologySequence
import Sheaf.Algebra.Homology.TensorKunnethNat
import Sheaf.AlgebraicGeometry.AffineModuleCechComparisonNatural
import Sheaf.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import Sheaf.AlgebraicGeometry.ModuleCechComparisonIsoAffine
import Sheaf.AlgebraicGeometry.ModulePullbackAffineSections
import Sheaf.AlgebraicGeometry.PicardKunnethResolutionModel
import Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import Sheaf.Paper.CechComparisonMapNaturality
import Sheaf.Paper.CechCupPullbackCompat

/-! # Short exact Cech comparison in the right coefficient

Source: Stacks Project, Varieties, Tag 0BED, lemma-kunneth, the diagram following
equation-kunneth-on-cech, applied to the right coefficient.
(blueprint: lem-sc-picard-external-cup-right-cech-diagram).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- There is a morphism of short exact complexes realizing external cup for a
short exact sequence of right coefficients. The chosen normalized maps are
identified with its homology maps by model comparison isomorphisms. No long
exact sequence, five-term row, or invertibility assertion is part of this result.

Source: Stacks Project, Varieties, Tag 0BED, lemma-kunneth, the diagram following
equation-kunneth-on-cech and its right-variable analogue.
(blueprint: lem-sc-picard-external-cup-right-cech-diagram).

Proof: Choose finite affine covers U of X and V of Y; the products give W.
The affine diagonals make every finite intersection affine. Applying sections
on these intersections to S preserves its exactness: the obstruction to
surjectivity lies in positive cohomology of the first quasi-coherent term,
which vanishes on affines. Form T from the tensor total of the scalar Cech
complex of F on U and the three scalar Cech complexes on V. Tensoring over k
is exact; each total degree is a finite sum, hence T is short exact degreewise.
Form U from the product-cover Cech complexes of the three external coefficient
sheaves. On each product intersection, the affine pullback and tensor section
formulas identify sections with the tensor of the two factor sections. Thus
this sequence too is short exact degreewise, even if F is not flat over O_X.
The refinement maps and signed cup pairing are natural in the right coefficient,
so they give a morphism psi:T -> U. Extend both complexes by zero to integers.
Every negative term, and therefore every negative homology object, is zero.
The natural affine Cech-to-cohomology comparisons and the scalar resolution
comparisons identify U's three homologies with the scalar product models.
For T use the tensor Kunneth comparison on both tensor totals and the natural
factor comparison isomorphisms; this gives its three model isomorphisms.
Choose the normalized maps d1,d2,d3 by picardExternalCupCochain_exists.
To verify the displayed homology equations, lift both factor classes to cycles.
Refinement followed by the signed cup map is pullback followed by sheaf cup
under the Cech comparisons. The normalization of each d gives the same value.
Tensor Kunneth's cycle formula and pure-tensor spanning show equality on all
homology classes. This comparison asserts no invertibility of these maps.
The construction works with empty covers, zero coefficients and natural degree
zero; its negative homologies remain zero in every such case. -/
theorem picardExternalCup_right_cech_diagram
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    (F : X.Modules) [F.IsQuasicoherent]
    (S : ShortComplex Y.Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    :
    ∃ (d1 : picardExternalTotal f g F S.X₁ ⟶
      picardScalarModel (pullback.fst f g ≫ f)
        (externalCupCoefficients f g F S.X₁)),
    ∃ (d2 : picardExternalTotal f g F S.X₂ ⟶
      picardScalarModel (pullback.fst f g ≫ f)
        (externalCupCoefficients f g F S.X₂)),
    ∃ (d3 : picardExternalTotal f g F S.X₃ ⟶
      picardScalarModel (pullback.fst f g ≫ f)
        (externalCupCoefficients f g F S.X₃)),
    ∃ (T U : ShortComplex (CochainComplex (ModuleCat.{w} k) ℤ)) (ψ : T ⟶ U)
      (a1 : ∀ n : ℕ, T.X₁.homology (n : ℤ) ≅
        (picardExternalTotal f g F S.X₁).homology (n : ℤ))
      (b1 : ∀ n : ℕ, U.X₁.homology (n : ℤ) ≅
        (picardScalarModel (pullback.fst f g ≫ f)
          (externalCupCoefficients f g F S.X₁)).homology (n : ℤ))
      (a2 : ∀ n : ℕ, T.X₂.homology (n : ℤ) ≅
        (picardExternalTotal f g F S.X₂).homology (n : ℤ))
      (b2 : ∀ n : ℕ, U.X₂.homology (n : ℤ) ≅
        (picardScalarModel (pullback.fst f g ≫ f)
          (externalCupCoefficients f g F S.X₂)).homology (n : ℤ))
      (a3 : ∀ n : ℕ, T.X₃.homology (n : ℤ) ≅
        (picardExternalTotal f g F S.X₃).homology (n : ℤ))
      (b3 : ∀ n : ℕ, U.X₃.homology (n : ℤ) ≅
        (picardScalarModel (pullback.fst f g ≫ f)
          (externalCupCoefficients f g F S.X₃)).homology (n : ℤ)),
      IsPicardExternalCupCochain f g F S.X₁ d1 ∧
      IsPicardExternalCupCochain f g F S.X₂ d2 ∧
      IsPicardExternalCupCochain f g F S.X₃ d3 ∧
      T.ShortExact ∧ U.ShortExact ∧
      (∀ i : ℤ, i < 0 → IsZero (T.X₂.homology i) ∧ IsZero (T.X₃.homology i) ∧
        IsZero (U.X₂.homology i) ∧ IsZero (U.X₃.homology i)) ∧
      (∀ n : ℕ, HomologicalComplex.homologyMap ψ.τ₁ (n : ℤ) =
        (a1 n).hom ≫ HomologicalComplex.homologyMap d1 (n : ℤ) ≫ (b1 n).inv) ∧
      (∀ n : ℕ, HomologicalComplex.homologyMap ψ.τ₂ (n : ℤ) =
        (a2 n).hom ≫ HomologicalComplex.homologyMap d2 (n : ℤ) ≫ (b2 n).inv) ∧
      (∀ n : ℕ, HomologicalComplex.homologyMap ψ.τ₃ (n : ℤ) =
        (a3 n).hom ≫ HomologicalComplex.homologyMap d3 (n : ℤ) ≫ (b3 n).inv) := by sorry

end AlgebraicGeometry.Scheme.Modules
