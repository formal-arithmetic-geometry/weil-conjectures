/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleStageSectionCocone
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Equality detection for two affine stage sections
Source: Stacks Project, Tags 09YQ, 0EYL, 04HR and 09YN.
(blueprint: lem-weil-pbc-affine-section-same-stage-equality). -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Source: Stacks Project, Tag 09YQ, degree-zero affine argument; Sites Tag 09YN,
its filtered-colimit section formula, using Tags 0EYL and 04HR.
(blueprint: lem-weil-pbc-affine-section-same-stage-equality).

Proof: Restrict the scheme system to the directed upper tail of i₀; the restriction
remains limiting by cofinality. Its limit projections are affine. Tag 0EYL presents
its affine étale limit site as the colimit of the affine stage sites, with finite
coverings. Restrict G to these sites using 04HR and transport its inverse images
using the unit-compatible affine inverse-image comparison. The composition
comparisons identify their limit inverse images with the constant system on the
limit inverse image of G. The tail is nonempty and connected, so this constant
system has that sheaf as colimit. Apply the varying-site formula of 09YN on the
base changes of W₀. The unit equations identify its stage maps and its maps into
limit sections with the canonical comparisons in etaleStageSectionDiagram and
etaleStageSectionCocone. Equality of the two limit images therefore gives equality
of the representatives in the filtered colimit of sets. The elementwise equality
criterion supplies a common later object k and two arrows from j to k. The index
category is thin, so these arrows coincide. This gives one arrow a with the
claimed equality. Empty affine objects have singleton section sets, and the
identity arrow gives the assertion in that case. This is only equality detection
for two sections at a single stage; it neither constructs representatives of
arbitrary limit sections nor supplies a universal property of the cocone. -/
theorem etaleAffineSection_sameStageEquality
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (G : Sheaf (D.obj (op i₀)).smallEtaleTopology (Type (u + 1)))
    (W₀ : (D.obj (op i₀)).Etale) [QuasiCompact W₀.hom] [QuasiSeparated W₀.hom]
    [IsAffine W₀.left]
    (j : Over (op i₀))
    (s t : (etaleStageSectionDiagram D c i₀ G W₀).obj (op j))
    (hst : (etaleStageSectionCocone D c i₀ G W₀).ι.app (op j) s =
      (etaleStageSectionCocone D c i₀ G W₀).ι.app (op j) t) :
    ∃ (k : Over (op i₀)) (a : k ⟶ j),
      (etaleStageSectionDiagram D c i₀ G W₀).map a.op s =
        (etaleStageSectionDiagram D c i₀ G W₀).map a.op t := by sorry

end AlgebraicGeometry
