/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q130
-/
module

public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Algebra.MvPolynomial.Eval

import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.RingTheory.KrullIntersectionLocalization
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Topology.NoetherianSpace

/-!
# Global homogeneous coordinates from positive tangent weights

Source: Milne, Algebraic Groups (2017), Theorem 13.41, pp.269--270, with the coordinate
construction of Lemmas 13.35--13.36, pp.267--268
(blueprint: lem-sfb-positive-weight-luna-coordinates).

The six auxiliary constructions are the actual evaluation, scalar coordinate, restriction,
pullback, maximal ideal and coordinate map occurring in this statement. Global sections use
Mathlib's `algΓ`; cotangent spaces use `Ideal.Cotangent`, with no replacement quotient.
The final map is an actual morphism over `Spec F`, built from `MvPolynomial.aeval`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry

variable (F : Type u) [Field F] (Z : Over (Spec (.of F)))

/-- Evaluation of a global function at the supplied rational point, using the canonical
identification of global sections of `Spec F` with `F`.
Source: Milne, Lemma 13.35, p.267 (blueprint: lem-sfb-positive-weight-luna-coordinates). -/
noncomputable def lunaPointEvaluation
    (z : 𝟙_ (Over (Spec (.of F))) ⟶ Z) :
    ((algΓ (.of F)).obj Z).unop →+* F :=
  (Scheme.ΓSpecIso (.of F)).hom.hom.comp z.left.appTop.hom

/-- The value of the standard invertible Laurent coordinate on an `F`-point of the
canonical multiplicative group. Thus this is the scalar usually denoted `t`.
Source: Milne, Example 13.37, p.268 (blueprint: lem-sfb-positive-weight-luna-coordinates). -/
noncomputable def lunaPointScalar
    (t : 𝟙_ (Over (Spec (.of F))) ⟶ StandardGroupSchemes.multiplicative F) : F :=
  (lunaPointEvaluation F (StandardGroupSchemes.multiplicative F) t)
    ((Scheme.ΓSpecIso (.of (LaurentPolynomial F))).inv (LaurentPolynomial.T 1))

/-- Restriction of the given scheme action to a rational point of the multiplicative group.
The left unitor identifies `Z` with `Spec F × Z` before applying `(t, id)`.
Source: Milne, Lemma 13.36, p.268 (blueprint: lem-sfb-positive-weight-luna-coordinates). -/
noncomputable def lunaActionAt
    (μ : StandardGroupSchemes.multiplicative F ⊗ Z ⟶ Z)
    (t : 𝟙_ (Over (Spec (.of F))) ⟶ StandardGroupSchemes.multiplicative F) : Z ⟶ Z :=
  (λ_ Z).inv ≫ (t ⊗ₘ 𝟙 Z) ≫ μ

/-- Pullback of global functions by the actual restricted action. This is precomposition
by `u ↦ t u`, so dualizing its cotangent map gives the differentiated point action,
with the same character exponent in the coordinate equation.
Source: Milne, Example 13.37, p.268 (blueprint: lem-sfb-positive-weight-luna-coordinates). -/
noncomputable def lunaActionPullback
    (μ : StandardGroupSchemes.multiplicative F ⊗ Z ⟶ Z)
    (t : 𝟙_ (Over (Spec (.of F))) ⟶ StandardGroupSchemes.multiplicative F) :
    ((algΓ (.of F)).obj Z).unop →ₐ[F] ((algΓ (.of F)).obj Z).unop :=
  ((algΓ (.of F)).map (lunaActionAt F Z μ t)).unop.hom

/-- The ideal `m = ker(ev_z)` in the actual global coordinate algebra.
Source: Milne, Lemma 13.35 and Theorem 13.41, pp.267,269
(blueprint: lem-sfb-positive-weight-luna-coordinates). -/
noncomputable def lunaMaximalIdeal
    (z : 𝟙_ (Over (Spec (.of F))) ⟶ Z) :
    Ideal ((algΓ (.of F)).obj Z).unop :=
  RingHom.ker (lunaPointEvaluation F Z z)

/-- The morphism to `Spec F[T₁,...,T_d]` whose coordinate algebra map is exactly
`T_i ↦ a_i`. It is the image of `MvPolynomial.aeval a` under the standard relative
Gamma-Spec adjunction, including when `d = 0`.
Source: Milne, Lemmas 13.35--13.36, pp.267--268
(blueprint: lem-sfb-positive-weight-luna-coordinates). -/
noncomputable def lunaCoordinateMap (d : ℕ)
    (a : Fin d → ((algΓ (.of F)).obj Z).unop) :
    Z ⟶ StandardGroupSchemes.affine F (MvPolynomial (Fin d) F) :=
  (algΓAlgSpecAdjunction (.of F)).homEquiv Z (op (CommAlgCat.of F (MvPolynomial (Fin d) F)))
    (CommAlgCat.ofHom (MvPolynomial.aeval a)).op

/-- Every supplied homogeneous cotangent basis gives global affine coordinates when all
weights of the differentiated action at a fixed point are strictly positive.
Source: Milne, Theorem 13.41, pp.269--270, and Lemmas 13.35--13.36, pp.267--268
(blueprint: lem-sfb-positive-weight-luna-coordinates).

The tangent-weight condition is written on a basis of the actual dual of `m/m²`.
For `y = μ_t^* x` in `m`, the equation on each functional is exactly
`(dμ_t v)([x]) = v([μ_t^* x]) = t^w v([x])`. Fixedness guarantees that every pullback
of an element of `m` again lies in `m`; the quantified `y` only avoids a subtype cast.
Over an algebraically closed field the rational points of the split torus detect its
characters. Hence these eigenvector equations express its character subspaces.

Proof (the eight steps of the DAG):
1. `lem-weil-pbc-lft-affine-pairs` makes the global coordinate algebra finitely generated.
   `lem-wf-affine-noetherian-components` makes it Noetherian. Smoothness gives regularity
   by `lem-weil-pbc-smooth-scheme-over-field-regular`; connectedness and the rational point
   give integrality by `lem-sc-regular-connected-integral`. By `def-pc-integral-scheme`
   the coordinate ring is a domain, and `lem-weil-pbc-spec-domain-stalks-function-field`
   identifies its localization at `m` with the regular local ring at the point.
2. `lem-weil-pbc-fibre-product-affine-spectra` and the canonical group law of `def-sc-gm-ga`
   turn the action into a Laurent coaction. By the fully faithful affine spectrum
   construction `def-weil-affine-spectrum`, the scheme action laws become counit and
   coassociativity. Comparing Laurent coefficients decomposes the algebra into its
   integer-weight subspaces. Multiplication adds weights and fixedness makes `m`
   homogeneous, containing every nonzero-weight subspace.
3. Differentiate the supplied coordinate equations. The basis dual to the classes of
   the `a_i` consists of tangent eigenvectors of weights `n_i`. Positivity forces
   every `n_i > 0`; this also fixes the sign convention.
4. Products of `j` supplied classes span `m^j/m^(j+1)`: reduce each factor modulo `m²`
   and every algebra coefficient modulo `m`. Thus these quotients have only positive
   weights for `j ≥ 1`; for an empty basis every such quotient is zero.
5. Apply `lem-weil-pbc-krull-intersection-localization` to `A`, `m`, `A`, and the prime
   `m`. It gives an element outside `m` whose powers annihilate elements of the
   intersection of the powers of `m`. The domain property cancels these nonzero
   powers, so that intersection is zero.
6. A nonpositive-weight element of `m` has zero class in each successive quotient,
   hence belongs to every power and vanishes. Thus negative components vanish,
   the degree-zero subspace is exactly `F`, and `m` is the positive-degree part.
7. `lem-sfb-positive-graded-regular-polynomial` now applies to this nonnegative grading,
   the regular localization and the supplied homogeneous basis and lifts. It makes
   the actual evaluation homomorphism `MvPolynomial.aeval a` an algebra isomorphism,
   also for `d = 0`.
8. Apply affine spectrum to this evaluation map and its inverse. The resulting
   isomorphism is exactly `lunaCoordinateMap`, by its construction and the adjunction.
   No step restricts the characteristic; the empty-variable case gives `Z ≅ Spec F`.
-/
theorem positive_weight_luna_coordinates [IsAlgClosed F] [IsAffine Z.left]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [Smooth Z.hom]
    [ConnectedSpace Z.left]
    (μ : StandardGroupSchemes.multiplicative F ⊗ Z ⟶ Z)
    (hunit : (MonObj.one ⊗ₘ 𝟙 Z) ≫ μ = (λ_ Z).hom)
    (hassoc : (MonObj.mul ⊗ₘ 𝟙 Z) ≫ μ =
      (α_ _ _ Z).hom ≫ (𝟙 _ ⊗ₘ μ) ≫ μ)
    (z : 𝟙_ (Over (Spec (.of F))) ⟶ Z)
    (hfixed : (𝟙 _ ⊗ₘ z) ≫ μ =
      CartesianMonoidalCategory.snd _ (𝟙_ (Over (Spec (.of F)))) ≫ z)
    (hpositive : ∃ (r : ℕ)
      (b : Module.Basis (Fin r) F (Module.Dual F (lunaMaximalIdeal F Z z).Cotangent))
      (w : Fin r → ℤ),
      (∀ i : Fin r, 0 < w i) ∧
      ∀ (t : 𝟙_ (Over (Spec (.of F))) ⟶ StandardGroupSchemes.multiplicative F)
        (x y : lunaMaximalIdeal F Z z),
        (y : ((algΓ (.of F)).obj Z).unop) = lunaActionPullback F Z μ t x →
        ∀ i : Fin r,
          b i ((lunaMaximalIdeal F Z z).toCotangent y) =
            lunaPointScalar F t ^ w i * b i ((lunaMaximalIdeal F Z z).toCotangent x))
    (d : ℕ) (a : Fin d → lunaMaximalIdeal F Z z)
    (hbasis : ∃ b : Module.Basis (Fin d) F (lunaMaximalIdeal F Z z).Cotangent,
      ∀ i : Fin d, b i = (lunaMaximalIdeal F Z z).toCotangent (a i))
    (n : Fin d → ℤ)
    (hhomogeneous : ∀
      (t : 𝟙_ (Over (Spec (.of F))) ⟶ StandardGroupSchemes.multiplicative F) (i : Fin d),
      lunaActionPullback F Z μ t (a i) =
        lunaPointScalar F t ^ n i • (a i : ((algΓ (.of F)).obj Z).unop)) :
    IsIso (lunaCoordinateMap F Z d (fun i ↦ (a i : ((algΓ (.of F)).obj Z).unop))) := by
  sorry

end AlgebraicGeometry
