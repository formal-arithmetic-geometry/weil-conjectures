/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.Geometry.Manifold.Sheaf.Smooth
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Smooth manifolds with open dimension strata

Source: Demailly, Complex Analytic and Differential Geometry, I §1 and IV §4,
Example (4.12), with the componentwise dimension convention
(blueprint: def-sfb-smooth-dimension-strata).

The open, disjoint dimension strata have ordinary Mathlib smooth structures.
Smooth complex functions are families of smooth functions on these strata.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

/-- Complex multiplication and addition are smooth over the reals.
Source: Demailly, I §1, smooth scalar operations
(blueprint: def-sfb-smooth-dimension-strata).

Proof: in real coordinates complex multiplication is the polynomial map
`((a,b),(c,d)) ↦ (ac-bd,ad+bc)`, and addition is coordinatewise addition.
Both are infinitely differentiable, giving the required Mathlib smooth-ring structure. -/
theorem complex_contMDiffRing : ContMDiffRing (modelWithCornersSelf ℝ ℂ) ∞ ℂ := by
  sorry

attribute [instance] complex_contMDiffRing

/-- A smooth structure with locally varying finite dimension. The open sets indexed by `n`
are disjoint and cover `N`; each is a boundaryless smooth `n`-manifold using Mathlib's
`ChartedSpace` and `IsManifold`. Neither separation nor countability is included.

Source: Demailly, I §1, smooth coordinate atlases, with the componentwise convention of
lem-sfb-smooth-function-modules-acyclic (blueprint: def-sfb-smooth-dimension-strata). -/
class SmoothDimensionStrata (N : Type u) [TopologicalSpace N] where
  /-- The open locus of points of dimension `n`. -/
  piece : ℕ → Opens N
  /-- Different dimensions give disjoint open sets. -/
  disjoint : Pairwise (fun m n ↦ Disjoint (piece m) (piece n))
  /-- The dimension loci cover the space. -/
  covers : ∀ x : N, ∃ n : ℕ, x ∈ piece n
  /-- Each dimension locus carries an ordinary Euclidean atlas. -/
  charted : ∀ n : ℕ, ChartedSpace (EuclideanSpace ℝ (Fin n)) (piece n)
  /-- All transitions of each atlas are smooth. -/
  smooth : ∀ n : ℕ, @IsManifold ℝ _ (EuclideanSpace ℝ (Fin n)) _ _
    (EuclideanSpace ℝ (Fin n)) _ (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      ∞ (piece n) _ (charted n)

attribute [instance_reducible, instance] SmoothDimensionStrata.charted
attribute [instance] SmoothDimensionStrata.smooth

namespace SmoothDimensionStrata

/-- The part of an open set lying in a dimension stratum, with its subspace topology.
Source: Demailly, I §1, restriction of charts (blueprint: def-sfb-smooth-dimension-strata). -/
def openInPiece {N : Type u} [TopologicalSpace N] [D : SmoothDimensionStrata N]
    (n : ℕ) (U : Opens N) : Opens (D.piece n) :=
  Opens.comap ⟨Subtype.val, continuous_subtype_val⟩ U

/-- Smooth complex functions on an open subset, represented on its disjoint dimension strata.
Operations are the existing pointwise operations on Mathlib's bundled smooth maps.
Source: Demailly, IV §4, Example (4.12) (blueprint: def-sfb-smooth-dimension-strata). -/
def complexPresheaf {N : Type u} [TopologicalSpace N] [D : SmoothDimensionStrata N] :
    TopCat.Presheaf RingCat.{u} (TopCat.of N) where
  obj U := RingCat.of (∀ n : ℕ,
    C^∞⟮modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)), D.openInPiece n U.unop;
      modelWithCornersSelf ℝ ℂ, ℂ⟯)
  map f := RingCat.ofHom
    { toFun := fun s n ↦ ContMDiffMap.restrictRingHom
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ ℂ) ℂ (N := D.piece n) (fun _x hx ↦ f.unop.le hx) (s n)
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  map_id := fun _ ↦ rfl
  map_comp := fun _ _ ↦ rfl

/-- The presheaf of smooth complex functions is a sheaf.
Source: Demailly, I §1 and IV §4, Example (4.12)
(blueprint: def-sfb-smooth-dimension-strata).

Proof: restrict a compatible family to each open dimension stratum. Glue its underlying
complex functions uniquely there. Smoothness is local in each Euclidean atlas, so each
glued function is smooth. The disjoint covering then identifies this family with one
function on the original open set. Uniqueness follows pointwise, stratum by stratum. -/
theorem complexPresheaf_isSheaf {N : Type u} [TopologicalSpace N]
    [D : SmoothDimensionStrata N] :
    Presheaf.IsSheaf (Opens.grothendieckTopology N) D.complexPresheaf := by
  sorry

/-- The sheaf `U ↦ C∞(U, ℂ)`, with pointwise ring operations, on a manifold whose dimension
may vary between open components. Its data is the explicit presheaf above.
Source: Demailly, IV §4, Example (4.12) (blueprint: def-sfb-smooth-dimension-strata). -/
def complexSheaf {N : Type u} [TopologicalSpace N] [D : SmoothDimensionStrata N] :
    TopCat.Sheaf RingCat.{u} (TopCat.of N) :=
  ⟨D.complexPresheaf, D.complexPresheaf_isSheaf⟩

end SmoothDimensionStrata
