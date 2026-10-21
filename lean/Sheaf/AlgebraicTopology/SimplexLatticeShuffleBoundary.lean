module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # The signed lattice-path shuffle on unnormalized simplices

Source: the universal combinatorial input to paragraph (3) of
`sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`
in the main-20261015 blueprint. The combinatorial proof is agent-written, as recorded in
(blueprint: lem-sfb-simplex-lattice-shuffle-boundary).

The free functor and alternating-face complex retain every degenerate simplex.
The lattice paths are monotone pairs whose coordinate sum is the vertex index.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Simplicial Opposite
open scoped TensorProduct BigOperators

noncomputable section

namespace AlgebraicTopology.SimplexLatticeShuffle

/-- Unnormalized integral chains on a standard simplex, using Mathlib's free modules and
alternating-face complex. Source: universal shuffle input, paragraph (3)
(blueprint: lem-sfb-simplex-lattice-shuffle-boundary). -/
def simplexChains (p : ℕ) : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  AlternatingFaceMapComplex.obj (Δ[p] ⋙ ModuleCat.free ℤ)

/-- Unnormalized integral chains on a product of standard simplices; repetitions are retained.
Source: universal shuffle input, paragraph (3)
(blueprint: lem-sfb-simplex-lattice-shuffle-boundary). -/
def productChains (p q : ℕ) : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  AlternatingFaceMapComplex.obj ((Δ[p] ⊗ Δ[q] : SSet.{0}) ⋙ ModuleCat.free ℤ)

/-- A lattice path has one horizontal or vertical step at each position: monotonicity and
coordinate sum equal to the position enforce this, including the endpoints. Source:
universal shuffle input, paragraph (3)
(blueprint: lem-sfb-simplex-lattice-shuffle-boundary). -/
def LatticePath (a b : ℕ) :=
  {w : Fin (a + b + 1) → Fin (a + 1) × Fin (b + 1) //
    Monotone w ∧ ∀ k, (w k).1.val + (w k).2.val = k.val}

/-- The sign counts vertical steps preceding horizontal steps, hence is the sign of the
permutation listing horizontal positions and then vertical positions, both increasingly.
Source: universal shuffle input, paragraph (3), proof step 2
(blueprint: lem-sfb-simplex-lattice-shuffle-boundary). -/
def pathSign {a b : ℕ} (w : LatticePath a b) : ℤ :=
  (-1) ^ (Finset.univ.filter (fun ij : Fin (a + b) × Fin (a + b) =>
    ij.1 < ij.2 ∧ (w.val ij.1.castSucc).2 < (w.val ij.1.succ).2 ∧
      (w.val ij.2.castSucc).1 < (w.val ij.2.succ).1)).card

/-- Postcompose the two coordinate strings of a path with the input strings. Source:
universal shuffle input, paragraph (3), displayed shuffle formula
(blueprint: lem-sfb-simplex-lattice-shuffle-boundary). -/
def pathSimplex {p q a b : ℕ} (u : (Δ[p] : SSet.{0}) _⦋a⦌)
    (v : (Δ[q] : SSet.{0}) _⦋b⦌) (w : LatticePath a b) :
    (Δ[p] ⊗ Δ[q] : SSet.{0}) _⦋a + b⦌ :=
  (SSet.stdSimplex.objMk
      ((SSet.stdSimplex.asOrderHom u).comp
        { toFun := fun k => w.val k |>.1
          monotone' := fun _ _ h => (w.property.1 h).1 }),
    SSet.stdSimplex.objMk
      ((SSet.stdSimplex.asOrderHom v).comp
        { toFun := fun k => w.val k |>.2
          monotone' := fun _ _ h => (w.property.1 h).2 }))

/-- The explicitly signed sum over all paths, extended linearly on pairs of basis strings
and transported along Mathlib's canonical free-module tensor isomorphism. Source:
universal shuffle input, paragraph (3), displayed shuffle formula
(blueprint: lem-sfb-simplex-lattice-shuffle-boundary). -/
def shuffle (p q a b : ℕ) :
    (simplexChains p).X a ⊗[ℤ] (simplexChains q).X b →ₗ[ℤ]
      (productChains p q).X (a + b) :=
  letI : Fintype (LatticePath a b) := Fintype.ofFinite
    {w : Fin (a + b + 1) → Fin (a + 1) × Fin (b + 1) //
      Monotone w ∧ ∀ k, (w k).1.val + (w k).2.val = k.val}
  (Finsupp.linearCombination ℤ (fun uv : (Δ[p] : SSet.{0}) _⦋a⦌ ×
      (Δ[q] : SSet.{0}) _⦋b⦌ =>
    ∑ w : LatticePath a b,
      pathSign w • ModuleCat.freeMk (R := ℤ) (pathSimplex uv.1 uv.2 w))).comp
    (ModuleCat.FreeMonoidal.μIso ℤ _ _).hom.hom

/-- Horizontal boundary contribution, zero when the horizontal degree is zero. The
isomorphism only identifies equal natural-number degrees. Source: universal shuffle
input, paragraph (3), boundary formula
(blueprint: lem-sfb-simplex-lattice-shuffle-boundary). -/
def horizontalBoundary (p q : ℕ) : (a b : ℕ) →
    (simplexChains p).X a ⊗[ℤ] (simplexChains q).X b →ₗ[ℤ]
      (productChains p q).X (a + b - 1)
  | 0, _ => 0
  | a + 1, b =>
    ((productChains p q).XIsoOfEq (by omega : a + b = a + 1 + b - 1)).hom.hom.comp
      ((shuffle p q a b).comp (TensorProduct.map
        ((simplexChains p).d (a + 1) a).hom LinearMap.id))

/-- Vertical boundary contribution, zero when the vertical degree is zero; the tensor
sign is supplied in the theorem. Source: universal shuffle input, paragraph (3)
(blueprint: lem-sfb-simplex-lattice-shuffle-boundary). -/
def verticalBoundary (p q : ℕ) : (a b : ℕ) →
    (simplexChains p).X a ⊗[ℤ] (simplexChains q).X b →ₗ[ℤ]
      (productChains p q).X (a + b - 1)
  | _, 0 => 0
  | a, b + 1 =>
    ((productChains p q).XIsoOfEq (by omega : a + b = a + (b + 1) - 1)).hom.hom.comp
      ((shuffle p q a b).comp (TensorProduct.map LinearMap.id
        ((simplexChains q).d (b + 1) b).hom))

/-- Each vertex is sent to one, extended linearly. Source: universal shuffle input,
paragraph (3), augmentations (blueprint: lem-sfb-simplex-lattice-shuffle-boundary). -/
def augmentation {X : Type} : (X →₀ ℤ) →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (fun _ : X => (1 : ℤ))

/-- Postcomposition by a monotone map of standard simplices on unnormalized chains.
Source: universal shuffle input, paragraph (3), naturality clause
(blueprint: lem-sfb-simplex-lattice-shuffle-boundary). -/
def simplexMap {p p' : ℕ} (f : Fin (p + 1) →o Fin (p' + 1)) :
    simplexChains p ⟶ simplexChains p' :=
  AlternatingFaceMapComplex.map
    (Functor.whiskerRight (SSet.stdSimplex.map (SimplexCategory.Hom.mk f))
      (ModuleCat.free ℤ))

/-- Postcomposition in both coordinates on product-simplex chains. Source: universal
shuffle input, paragraph (3), naturality clause
(blueprint: lem-sfb-simplex-lattice-shuffle-boundary). -/
def productMap {p p' q q' : ℕ} (f : Fin (p + 1) →o Fin (p' + 1))
    (g : Fin (q + 1) →o Fin (q' + 1)) : productChains p q ⟶ productChains p' q' :=
  AlternatingFaceMapComplex.map (Functor.whiskerRight
    (SSet.stdSimplex.map (SimplexCategory.Hom.mk f) ⊗ₘ
      SSet.stdSimplex.map (SimplexCategory.Hom.mk g)) (ModuleCat.free ℤ))

/-- The signed shuffle commutes with boundary, preserves augmentation, and commutes with
all monotone postcompositions, including noninjective ones.

Source: the agent-written universal shuffle calculation in paragraph (3) of the
main-20261015 direct-image proof (blueprint: lem-sfb-simplex-lattice-shuffle-boundary).

Proof: the free alternating-face complexes are Mathlib's unnormalized complexes;
deleting positions i<j in either order has opposite signs, and edge boundaries have
augmentation 1-1=0. Encode a path by horizontal/vertical letters; its sign is minus one
to the number of vertical-before-horizontal inversions. Expand the boundary as labeled
(path, deleted vertex) terms. At an interior mixed corner, swap its two letters: the
surviving string is unchanged and the signs are opposite. At an HH corner, collapse the
two moves; if the omitted horizontal vertex is i and t vertical moves precede it, the
removed move has t inversions and the face index is i+t, giving sign (-1)^i. At an
initial H there is no removed inversion; at a terminal H there are b, giving (-1)^a.
At a VV corner of coordinates (i,j), collapsing a move removes a-i inversions and the
face index is i+j, giving (-1)^(a+j). An initial V removes a inversions; a terminal V
removes none, giving respectively (-1)^a and (-1)^(a+b). Splitting each shorter move,
or adjoining the endpoint letter, inverts these reindexings. These cases exhaust all
terms. Repetitions never affect the labeled cancellations. If a=0 or b=0 omit that
factor's term; if a=b=0 both sides are zero. Linearity extends the calculation from
basis pairs. The empty path has sign one and preserves augmentation. Finally, each
path vertex postcomposes to (f(u_Ak),g(v_Bk)), with the same sign, so summing proves
naturality even when postcomposition identifies generators. -/
theorem shuffle_boundary_augmentation_naturality :
    (∀ (p q a b : ℕ),
      ((productChains p q).d (a + b) (a + b - 1)).hom.comp (shuffle p q a b) =
        horizontalBoundary p q a b + (-1 : ℤ) ^ a • verticalBoundary p q a b) ∧
    (∀ (p q : ℕ) (u : (simplexChains p).X 0) (v : (simplexChains q).X 0),
      augmentation (shuffle p q 0 0 (u ⊗ₜ[ℤ] v)) = augmentation u * augmentation v) ∧
    (∀ (p p' q q' a b : ℕ) (f : Fin (p + 1) →o Fin (p' + 1))
      (g : Fin (q + 1) →o Fin (q' + 1)),
      ((productMap f g).f (a + b)).hom.comp (shuffle p q a b) =
        (shuffle p' q' a b).comp (TensorProduct.map
          ((simplexMap f).f a).hom ((simplexMap g).f b).hom)) := by
  sorry

end AlgebraicTopology.SimplexLatticeShuffle
