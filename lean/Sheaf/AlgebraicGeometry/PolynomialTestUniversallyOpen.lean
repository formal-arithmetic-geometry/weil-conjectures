module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Testing universal openness with polynomial extensions

Source: Stacks Project, Tag 0F31, lemma-test-universally-open, implication (3) to (1),
specialized to affine schemes.
(blueprint: lem-sfb-polynomial-test-universally-open)
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry

/-- If every finite polynomial extension of a commutative ring map induces an open
map on spectra, the original affine scheme morphism is universally open.

Source: Stacks Project, Tag 0F31, lemma-test-universally-open, implication (3) to (1).
(blueprint: lem-sfb-polynomial-test-universally-open)

Proof:
1. For any commutative A-algebra B, the affine fibre-product theorem
   (lem-weil-pbc-fibre-product-affine-spectra) identifies the base change with
   Spec(B tensor_A C). By lem-weil-pbc-spec-localization-away-basic-open, it suffices
   to show that the image of every principal open D(g) is open.
2. Express g as a finite sum of pure tensors b_i tensor c_i, using
   def-weil-pbc-module-tensor-product, absorbing scalar coefficients into b_i.
   Put R = A[t_1,...,t_n], S = C[t_1,...,t_n], and h = sum_i c_i t_i.
   Evaluation gives e : R -> B and k : S -> B tensor_A C sending t_i to b_i
   and b_i tensor 1, respectively; k(h) = g. The square commutes on coefficients
   and variables, by def-weil-pbc-mv-polynomial-ring. For n = 0, h = g = 0.
3. This ring square is a pushout: compatible maps from S and B to a ring E
   restrict to compatible maps from C and B. The tensor universal property
   (lem-weil-pbc-algebra-tensor-pushout-universal-property) gives the unique map
   B tensor_A C -> E. Its composites have the required values on coefficients
   and variables, hence give the original maps by polynomial uniqueness.
   By lem-weil-pbc-fibre-product-affine-spectra the spectral square is cartesian.
4. By hypothesis the image U of D(h) in Spec R is open. By
   lem-weil-pbc-basic-open-pullback, the inverse image of D(h) is D(g).
   The arbitrary-subset identity lem-weil-pbc-base-change-image identifies the
   image of D(g) with the inverse image of U under Spec(e), hence it is open.
   No flatness or finite-presentation hypothesis on e is used.
5. Every open is a union of principal opens, and images preserve unions, so
   every affine base change is open.
6. For any scheme T over Spec A, cover T by affine opens W_j using
   lem-weil-pbc-affine-opens-basis. By lem-weil-pbc-open-immersion-base-change
   and lem-weil-pbc-base-change-image the corresponding pullbacks identify with
   the inverse images of W_j as open subschemes of the full pullback.
   By def-pc-fibre-product their projections are the affine base changes of
   step 5. The image of an open subset is therefore open on each W_j and hence
   open in T. This includes empty T and arbitrary infinite affine covers. -/
theorem universallyOpen_specMap_of_isOpenMap_mvPolynomial
    {A C : Type u} [CommRing A] [CommRing C] (φ : A →+* C)
    (h : ∀ n : ℕ, IsOpenMap
      (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin n) φ)))) :
    UniversallyOpen (Spec.map (CommRingCat.ofHom φ)) := by
  sorry

end AlgebraicGeometry
