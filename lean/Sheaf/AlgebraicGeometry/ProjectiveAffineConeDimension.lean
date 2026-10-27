/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
public import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.RingTheory.KrullDimension.PID
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.DimensionLocallyAlgebraic
import Sheaf.AlgebraicGeometry.SchemeProductDimension
import WeilConjectures.AlgebraicGeometry.Dimension
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.DenseCompactification

/-!
# The projection from punctured affine space and dimensions of closed affine cones

Source: Stacks Project, varieties.tex, Tag 0B2R, proof of
lemma-intersection-in-projective-space, the punctured projection and its charts.
(blueprint: lem-sfb-projective-affine-cone-dimension)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveSpace

noncomputable section

/-- The punctured affine `(N+1)`-space, the union of the coordinate nonvanishing opens.
Its complement is the origin, by `AffineSpace.range_zeroSection`.
Source: Stacks Project, Tag 0B2R, punctured-projection paragraph.
(blueprint: lem-sfb-projective-affine-cone-dimension) -/
def affineConePunctured (k : Type u) [Field k] (N : ℕ) :
    (𝔸(ULift.{u} (Fin (N + 1)); Spec (CommRingCat.of k))).Opens :=
  ⨆ i : ULift.{u} (Fin (N + 1)),
    (𝔸(ULift.{u} (Fin (N + 1)); Spec (CommRingCat.of k))).basicOpen
      (AffineSpace.coord (Spec (CommRingCat.of k)) i)

/-- The prescribed chart description of the punctured-affine-space projection.
The map is over `k`, its chart preimages are `D(x_i)`, and the chart coordinate
`u_{j/i}` pulls back to `x_j/x_i`. The last condition is written after multiplying
by the invertible coordinate `x_i`, avoiding any choice of an inverse.
Source: Stacks Project, Tag 0B2R, displayed chart homomorphism.
(blueprint: lem-sfb-projective-affine-cone-dimension) -/
def HasAffineConeCharts (k : Type u) [Field k] (N : ℕ)
    (π : (affineConePunctured k N).toScheme ⟶
      ℙ(ULift.{u} (Fin (N + 1)); Spec (CommRingCat.of k))) : Prop :=
  π ≫ ℙ(ULift.{u} (Fin (N + 1)); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k) =
    (affineConePunctured k N).ι ≫
      𝔸(ULift.{u} (Fin (N + 1)); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k) ∧
  ∀ i : ULift.{u} (Fin (N + 1)),
    π ⁻¹ᵁ standardOpen _ (Spec (CommRingCat.of k)) i =
      (affineConePunctured k N).ι ⁻¹ᵁ
        (𝔸(ULift.{u} (Fin (N + 1)); Spec (CommRingCat.of k))).basicOpen
          (AffineSpace.coord (Spec (CommRingCat.of k)) i) ∧
    ∀ j : {j : ULift.{u} (Fin (N + 1)) // j ≠ i},
      (π ∣_ standardOpen _ (Spec (CommRingCat.of k)) i).appTop
          ((standardOpenIso _ (Spec (CommRingCat.of k)) i).hom.appTop
            (AffineSpace.coord (Spec (CommRingCat.of k)) j)) *
        ((π ⁻¹ᵁ standardOpen _ (Spec (CommRingCat.of k)) i).ι ≫
          (affineConePunctured k N).ι).appTop
            (AffineSpace.coord (Spec (CommRingCat.of k)) i) =
      ((π ⁻¹ᵁ standardOpen _ (Spec (CommRingCat.of k)) i).ι ≫
        (affineConePunctured k N).ι).appTop
          (AffineSpace.coord (Spec (CommRingCat.of k)) j.1)

/-- The affine cone as a subset: adjoin the origin to the image in affine space of
`π⁻¹(Z)`. The image of the zero section over a field is the singleton origin.
Source: Stacks Project, Tag 0B2R, closures of punctured inverse images.
(blueprint: lem-sfb-projective-affine-cone-dimension) -/
def affineConeSet (k : Type u) [Field k] (N : ℕ)
    (π : (affineConePunctured k N).toScheme ⟶
      ℙ(ULift.{u} (Fin (N + 1)); Spec (CommRingCat.of k)))
    (Z : Set ℙ(ULift.{u} (Fin (N + 1)); Spec (CommRingCat.of k))) :
    Set 𝔸(ULift.{u} (Fin (N + 1)); Spec (CommRingCat.of k)) :=
  Set.range (AffineSpace.zeroSection (ULift.{u} (Fin (N + 1)))
    (Spec (CommRingCat.of k))) ∪ (affineConePunctured k N).ι '' (π ⁻¹' Z)

/-- There is a unique punctured projection with the prescribed coordinate maps.
Every closed projective subset has a closed affine cone; a nonempty subset of
finite dimension `d` has a cone of dimension `d+1`, irreducible when the subset is.
The empty projective subset has cone the origin.
Source: Stacks Project, Tag 0B2R, proof of lemma-intersection-in-projective-space.
(blueprint: lem-sfb-projective-affine-cone-dimension)

Proof:
1. Glue the maps `u_{j/i} ↦ x_j/x_i` on the coordinate opens. On overlaps the
   fractions agree, and a coordinate is a unit exactly over its projective chart.
   Morphism gluing and affine extensionality give the map and its uniqueness
   (lem-weil-pbc-projective-space-standard-charts,
   lem-weil-pbc-morphism-into-affine-scheme, lem-weil-pbc-scheme-morphism-gluing).
2. Identify each chart map with the first projection from the product with
   `Spec k[t,t⁻¹]`, by `t ↦ x_i` and `u_{j/i} ↦ x_j/x_i`; the inverse sends
   `x_j` to `u_{j/i}t` (lem-weil-pbc-fibre-product-affine-spectra).
3. For any point of a nonempty `Z`, use its residue field and the scalar line
   `x_i=t`, `x_j=u_{j/i}(z)t`. Its generic point belongs to the punctured inverse
   image and its zero point maps to the origin. Thus the origin is in its closure
   (lem-weil-pbc-spec-irreducible-closed-subsets-primes). No rational point is needed.
4. The inverse image is closed in the punctured open, so its closure adds only
   the origin. For empty `Z` the cone is the origin directly, a closed zero locus.
5. Give `Z` its reduced induced closed subscheme structure. On each chart its
   inverse image has ring `R_i[t,t⁻¹]`, and these are finite-type schemes over `k`
   (lem-weil-pbc-reduced-induced-closed-subscheme,
   lem-weil-pbc-closed-immersion-base-change, def-weil-finite-type-morphism).
6. The punctured affine line is irreducible of dimension one, by the polynomial
   dimension calculation and dimension invariance on nonempty opens
   (lem-zl-spectrum-irreducible-nilradical-prime,
   lem-sc-p1-polynomial-dimension-one, lem-sc-dimension-locally-algebraic,
   lem-weil-pbc-spec-topological-krull-dimension-ring).
   Product dimensions give `dim Y_i = dim Z_i + 1`
   (lem-sfb-scheme-product-dimension, lem-pc-scheme-dimension-local-rings,
   lem-weil-pbc-homeomorphism-krull-dimension).
7. The finite open covers compute dimensions as the maximum of the nonempty
   chart dimensions, giving `dim π⁻¹(Z) = d+1`
   (lem-weil-pbc-open-subspace-dimension-monotone,
   lem-weil-pbc-dimension-bound-open-cover, lem-weil-pbc-scheme-sober).
8. The cone has its reduced finite-type closed subscheme structure. The punctured
   inverse image is dense open, so its dimension equals the cone dimension
   (lem-weil-pbc-dense-open-dimension-comparison and open monotonicity).
9. If `Z` is irreducible, every nonempty reduced chart ring is a domain, as is its
   Laurent ring. Their irreducible inverse-image opens pairwise meet, since points
   in chart overlaps lift over their residue fields with `t=1`. Their union is
   irreducible; its closure, the cone, is irreducible
   (lem-zl-spectrum-irreducible-nilradical-prime, def-weil-irreducible-components).
-/
theorem exists_unique_affineConeProjection (k : Type u) [Field k] (N : ℕ) :
    ∃ π : (affineConePunctured k N).toScheme ⟶
        ℙ(ULift.{u} (Fin (N + 1)); Spec (CommRingCat.of k)),
      HasAffineConeCharts k N π ∧
      (∀ π' : (affineConePunctured k N).toScheme ⟶
          ℙ(ULift.{u} (Fin (N + 1)); Spec (CommRingCat.of k)),
        HasAffineConeCharts k N π' → π' = π) ∧
      (∀ Z : Set ℙ(ULift.{u} (Fin (N + 1)); Spec (CommRingCat.of k)),
        IsClosed Z → IsClosed (affineConeSet k N π Z) ∧
          ∀ d : ℕ, Z.Nonempty → topologicalKrullDim Z = (d : WithBot ℕ∞) →
            topologicalKrullDim (affineConeSet k N π Z) = ((d + 1 : ℕ) : WithBot ℕ∞) ∧
              (IsIrreducible Z → IsIrreducible (affineConeSet k N π Z))) ∧
      affineConeSet k N π ∅ =
        Set.range (AffineSpace.zeroSection (ULift.{u} (Fin (N + 1)))
          (Spec (CommRingCat.of k))) := by
  sorry

end

end AlgebraicGeometry.ProjectiveSpace
