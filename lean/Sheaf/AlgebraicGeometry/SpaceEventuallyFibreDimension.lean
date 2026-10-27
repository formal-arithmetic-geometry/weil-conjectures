/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.IsLimit
import Sheaf.SecPurity.QcMapAffineEtaleNeighbourhood
import Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra
import Sheaf.AlgebraicGeometry.LimitFibreDimensionBound
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal
import WeilConjectures.AlgebraicGeometry.DimensionPreservedFieldExtension
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Eventual geometric fibre dimension bounds for algebraic spaces

Source: Stacks Project, spaces-limits.tex, Tag 0D4K, Situation 084W;
spaces-morphisms.tex, Tags 06LR and 04NS
(blueprint: lem-sfb-space-eventually-fibre-dimension).

The geometric fibres of the base changes are written as single presheaf pullbacks
along the composite geometric points. Pullback pasting identifies these with the
fibres of the stage and limiting families, without choosing new models of the spaces.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A bound on every geometric fibre of a finitely presented algebraic space over
an affine inverse limit holds at every sufficiently late stage.
Source: Stacks Project, spaces-limits.tex, Tag 0D4K, Situation 084W, specialized to
an affine base; spaces-morphisms.tex, Tags 06LR and 04NS
(blueprint: lem-sfb-space-eventually-fibre-dimension).

Proof:
1. Quasi-compactness gives a quasi-compact scheme atlas of X₀
   (lem-trf-space-qc-separated-etale-local). Apply
   lem-a1-qc-map-affine-etale-neighbourhood to obtain an affine surjective etale
   chart U₀ → X₀; surjectivity follows by lifting first to the atlas and its pullback.
2. The composite U₀ → T₀ is locally finitely presented by the chart condition
   (def-sbc-locally-finite-presentation), hence locally of finite type
   (def-weil-finite-type-morphism). A map between affines is affine
   (pqf-lem-affine-local-target), hence quasi-compact
   (lem-weil-pbc-affine-morphism-permanence), so it is of finite type.
3. Base change the chart to every stage and the limit. The charts remain surjective
   etale (lem-trf-space-fibre-products-etale-covers); their maps are finite type
   (lem-sfb-finite-type-composition-base-change). The bases and chart sources are affine
   (lem-weil-pbc-limit-affine-transition, lem-weil-pbc-fibre-product-affine-spectra).
   The fibre-product universal property (def-pc-fibre-product) identifies the chart
   limit and all transition comparisons. Quasi-separatedness follows by base change
   of the initial quasi-compact diagonal. The cofinal directed tail has the same limit.
4. For a limiting ordinary base point extend its residue field to an algebraic closure.
   The geometric chart and space have equal dimension
   (lem-sfb-quasiseparated-space-atlas-dimension). The ordinary chart fibre is affine
   finite type (lem-sfb-finite-type-composition-base-change,
   lem-weil-pbc-fibre-product-affine-spectra, lem-pc-affine-finite-type-algebra).
   By pullback pasting (def-pc-fibre-product) and invariance of affine finite-type
   dimension under field extension (lem-weil-pbc-dimension-preserved-field-extension),
   its ordinary fibre dimension is therefore bounded by d.
5. Apply lem-trf-limit-fibre-dimension-bound on the directed tail. Its transition
   comparisons are isomorphisms, hence closed immersions (def-weil-closed-immersion).
   This gives a stage whose ordinary chart fibres all have dimension at most d.
6. Extend each such ordinary fibre to any algebraically closed field. The same affine
   finite-type field-extension theorem and chart-dimension equality from step 4 give
   the bound for every geometric fibre of the space at that stage. No purity is used.
7. Pullback pasting identifies every later family with its base change from this stage
   (def-pc-fibre-product, lem-trf-space-fibre-products-etale-covers). The base-change
   clause of lem-sfb-space-relative-dimension-base-change preserves the geometric
   dimension bound, including empty fibres. -/
theorem eventually_geometric_fibre_dimension_le_of_isLimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over (Spec (.of (ULift.{u} ℤ))))
    [∀ i : I, IsAffine (D.obj (op i)).left]
    (haff : ∀ {i j : I} (hij : i ≤ j), IsAffineHom (D.map (homOfLE hij).op).left)
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (X₀ : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
    (f₀ : X₀.obj.obj ⟶ yoneda.obj (D.obj (op i₀)))
    (hqc : MapIsQuasiCompact f₀)
    (hqs : MapIsQuasiCompact (pullback.diagonal f₀))
    (hlfp : MapToSchemeIsLocally (@LocallyOfFinitePresentation) X₀ (D.obj (op i₀)) f₀)
    (d : ℕ)
    (hdim : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (a : Spec (.of Ω) ⟶ c.pt.left),
      topologicalKrullDim (Point (Limits.pullback f₀ (yoneda.map (Over.homMk
        (U := Over.mk (a ≫ c.pt.hom)) (V := D.obj (op i₀))
        (a ≫ (c.π.app (op i₀)).left) (by simp))))) ≤ (d : WithBot ℕ∞)) :
    ∃ (i : I) (hi : i₀ ≤ i), ∀ (j : I) (hij : i ≤ j),
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (a : Spec (.of Ω) ⟶ (D.obj (op j)).left),
        topologicalKrullDim (Point (Limits.pullback f₀ (yoneda.map (Over.homMk
          (U := Over.mk (a ≫ (D.obj (op j)).hom)) (V := D.obj (op i₀))
          (a ≫ (D.map (homOfLE (le_trans hi hij)).op).left) (by simp))))) ≤
            (d : WithBot ℕ∞) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
