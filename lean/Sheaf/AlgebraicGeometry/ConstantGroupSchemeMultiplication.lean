/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Sheaf.AlgebraicGeometry.ConstantGroupScheme

/-!
# Multiplication of the constant group scheme

Source: Stacks Project, Groupoids, Example 39.5.6 (Tag 03YW), and Schemes,
Section 26.14 (Tag 01JA) (blueprint: lem-weil-pbc-constant-group-scheme-multiplication).
-/

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

variable (T : Scheme.{u}) (E : Type v) [Small.{u} E] [AddCommGroup E]

/-- The pair components of the fibre square are clopen, disjoint and covering; the
componentwise maps glue uniquely to multiplication, with the stated properties.
Source: Stacks Project, Groupoids, Example 39.5.6 (Tag 03YW), and Schemes,
Section 26.14 (Tag 01JA) (blueprint: lem-weil-pbc-constant-group-scheme-multiplication).

Proof:
1. By `lem-weil-pbc-scheme-coproduct-family`, the images of the coprojections are
clopen, disjoint and covering. Pull them back along both projections of the fibre
product (`def-pc-fibre-product`); continuity gives clopenness of their intersections.
Distinct pairs differ in a coordinate, giving disjointness; choosing components for
both projections of a point gives coverage. The pullback relation identifies the
two composites to `T`.
2. Regard each pair component as an open subscheme (`def-weil-open-immersion`).
Compose its inclusion with the base projection and the coprojection indexed by the
sum. These local morphisms agree on overlaps: identical indices give identical maps,
and distinct indices give the empty scheme, an initial object.
3. Apply `lem-weil-pbc-scheme-morphism-gluing` to this open cover and these compatible
local maps to obtain a scheme morphism with the prescribed restrictions, unique among all
scheme morphisms having these restrictions.
4. Its composite with the codiagonal restricts to the base projection on every
component, since the codiagonal composed with a coprojection is the identity.
Gluing uniqueness gives the global equality. The restriction formula on points
also puts the image of each pair component in the component indexed by its sum.
5. For a fixed `d`, all pair components summing to `d` lie in its component preimage.
Conversely choose a pair component containing a point in that preimage. Its image
lies in both the component indexed by the sum and that indexed by `d`. Disjointness
of coproduct components forces the sum to equal `d`, proving the preimage formula.
The cover maps used below are open immersions with image exactly the pair components,
so equality after their composition is equality of restrictions as scheme morphisms.
-/
theorem constantGroupSchemeMultiplication_properties :
    (∀ ij : E × E,
      IsOpen (constantGroupSchemePairComponent T E ij.1 ij.2) ∧
        IsClosed (constantGroupSchemePairComponent T E ij.1 ij.2)) ∧
    (∀ ij ij' : E × E, ij ≠ ij' →
      Disjoint (constantGroupSchemePairComponent T E ij.1 ij.2)
        (constantGroupSchemePairComponent T E ij'.1 ij'.2)) ∧
    (⋃ ij : E × E, constantGroupSchemePairComponent T E ij.1 ij.2 = Set.univ) ∧
    ∃ m : constantGroupSchemeSquare T E ⟶ constantGroupScheme T E,
      (∀ ij : E × E,
        let j := (Scheme.Pullback.openCoverOfLeftRight
          (sigmaOpenCover (fun _ : E => T)) (sigmaOpenCover (fun _ : E => T))
          (constantGroupSchemeProjection T E) (constantGroupSchemeProjection T E)).f ij
        j ≫ m = j ≫ constantGroupSchemeSquareProjection T E ≫
          constantGroupSchemeIncl T E (ij.1 + ij.2)) ∧
      (∀ m' : constantGroupSchemeSquare T E ⟶ constantGroupScheme T E,
        (∀ ij : E × E,
          let j := (Scheme.Pullback.openCoverOfLeftRight
            (sigmaOpenCover (fun _ : E => T)) (sigmaOpenCover (fun _ : E => T))
            (constantGroupSchemeProjection T E) (constantGroupSchemeProjection T E)).f ij
          j ≫ m' = j ≫ constantGroupSchemeSquareProjection T E ≫
            constantGroupSchemeIncl T E (ij.1 + ij.2)) → m' = m) ∧
      m ≫ constantGroupSchemeProjection T E = constantGroupSchemeSquareProjection T E ∧
      (∀ ij : E × E,
        Set.MapsTo (m : constantGroupSchemeSquare T E → constantGroupScheme T E)
          (constantGroupSchemePairComponent T E ij.1 ij.2)
          (constantGroupSchemeComponent T E (ij.1 + ij.2))) ∧
      (∀ d : E,
        m ⁻¹' (constantGroupSchemeComponent T E d) =
          ⋃ ij : {ij : E × E // ij.1 + ij.2 = d},
            constantGroupSchemePairComponent T E ij.1.1 ij.1.2) := by
  sorry

end AlgebraicGeometry
