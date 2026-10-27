/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Limits
import Sheaf.AlgebraicGeometry.AlgebraicSpaceCoproduct
import Sheaf.AlgebraicGeometry.FppfSheafCoproductPartition
import Sheaf.AlgebraicGeometry.SpaceChangeBase
import Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Sites.Precoverage
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Algebraicity is fppf local on the base

Source: Stacks Project, Bootstrap, Tag 04SK (`lemma-locally-algebraic-space`),
with Spaces, Tag 02WQ (`lemma-coproduct-algebraic-spaces`)
(blueprint: lem-sfb-fppf-local-algebraic-space).

The local space is written over `T i` by restricting the presheaf along `Over.map`.
Viewing it over `S` gives the sheaf `h_{T i} × F`, exactly as in Tag 04SK.
The explicit coproduct cofan records that the chart coproduct belongs to the big site;
no smallness assumption is imposed on the indexing type independently of that condition.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An fppf sheaf which is an algebraic space over every member of an fppf cover of
its base is an algebraic space, provided the chosen scheme charts have a coproduct
in the big site.

Source: Stacks Project, Bootstrap, Tag 04SK (`lemma-locally-algebraic-space`),
with Spaces, Tag 02WQ (`lemma-coproduct-algebraic-spaces`)
(blueprint: lem-sfb-fppf-local-algebraic-space).

The isomorphisms `e` identify the local spaces with the restrictions of `F`. Over a
scheme `W → T i`, this restriction has value `F(W → T i → S)`. Extending it to `S`
has value the pairs `(W → T i, s ∈ F(W))`, namely `(h_{T i} × F)(W)`.
If the indices and charts lie in the same universe and the big site contains their
scheme coproduct, that coproduct supplies exactly `Vcoprod`, `ι` and `hV` below.

Proof:
1. By lem-sfb-space-change-base-to-integers, view each local space and its supplied
   atlas over `S`; its underlying sheaf is `h_{T i} × F`. Apply
   lem-trf-algebraic-space-coproduct to their coproduct `U`, using the given scheme
   coproduct of the atlases. This is the only use of the chart-size condition.
2. For a scheme test `Z` and a section `a ∈ F(Z)`, put `Z_i = Z ×_S T_i` and
   `P_a = ∐ Z_i` (def-pc-fibre-product, lem-weil-pbc-scheme-coproduct-family).
   By lem-trf-fppf-sheaf-coproduct-partition a section of `h_Z ×_F U` amounts to a
   clopen partition of its test scheme, maps from the pieces to the `T_i`, and
   sections of `F` forced to be the restrictions of `a`. Thus it amounts exactly
   to maps from those pieces to `Z_i`, which glue uniquely to a map to `P_a`.
   These inverse constructions commute with restriction and identify both projections.
3. By lem-trf-fppf-covering-base-change, the maps `Z_i → Z` form an fppf cover.
   On the disjoint open summands of `P_a`, its projection to `Z` is therefore flat
   and locally of finite presentation, and their images cover `Z`. Flatness follows
   on local rings and finite presentation on affine neighbourhoods; no finiteness
   of the family or quasi-compactness is used.
4. Regard `P_a` as a scheme algebraic space (def-trf-scheme-algebraic-space),
   transfer bases by lem-sfb-space-change-base-to-integers, and use
   lem-sfb-space-local-properties-chart-test to compare the scheme and space
   properties. A field-valued point lifts after a common residue-field extension,
   so the projection is also surjective on point classes. The scheme tests from
   steps 2 and 3 satisfy lem-sfb-fppf-space-atlas-bootstrap for `U → F`, giving
   algebraicity of `F`. The final sufficient size condition supplies the cofan
   already used in step 1. -/
theorem isAlgebraicSpace_of_fppf_cover
    {S : Scheme.{u}} (F : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (I : Type v) (T : I → Over S)
    (hcover : Presieve.ofArrows (fun i ↦ (T i).left) (fun i ↦ (T i).hom) ∈
      Scheme.fppfPrecoverage S)
    (Fi : ∀ i, AlgebraicSpace (T i).left)
    (e : ∀ i, (Fi i).obj.obj ≅ (Over.map (T i).hom).op ⋙ F.obj)
    (V : ∀ i, Over (T i).left)
    (p : ∀ i, yoneda.obj (V i) ⟶ (Fi i).obj.obj)
    (hp : ∀ i, AlgebraicSpace.IsEtale (p i) ∧ AlgebraicSpace.IsSurjective (p i))
    (Vcoprod : Over S)
    (ι : ∀ i, (Over.map (T i).hom).obj (V i) ⟶ Vcoprod)
    (hV : Nonempty (IsColimit (Cofan.mk Vcoprod ι))) :
    AlgebraicSpace.IsAlgebraicSpace F := by
  sorry

end AlgebraicGeometry
