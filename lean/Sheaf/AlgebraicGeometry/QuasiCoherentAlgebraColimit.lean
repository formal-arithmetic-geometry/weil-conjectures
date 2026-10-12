/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.QuasiCoherentAlgebra
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Filtered.Basic
import Sheaf.AlgebraicGeometry.Coherent
import Sheaf.CategoryTheory.SheafAlgebrasDirectedColimit

/-! # Directed colimits of quasi-coherent algebra sheaves

Source: Stacks Project, Schemes, Lemma 01ID and Section 26.24; Sheaves,
Section 009E and Lemma 0087; Modules, Lemmas 01AH and 01AJ
(blueprint: lem-weil-pbc-quasi-coherent-algebra-colimit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Directed colimits of quasi-coherent algebra sheaves exist in all algebra sheaves,
are quasi-coherent, are the sheafification of the presheaf colimit with its coprojections,
have colimit rings of sections on affine opens, and commute with restriction to opens.
Being a colimit in all algebra sheaves with quasi-coherent vertex also gives the colimit
in their full subcategory of quasi-coherent algebras. Restriction uses the open site
`Over V`, whose objects are precisely the opens contained in `V`.
Source: Stacks Project, Schemes, Lemma 01ID and Section 26.24; Sheaves,
Section 009E and Lemma 0087; Modules, Lemmas 01AH and 01AJ
(blueprint: lem-weil-pbc-quasi-coherent-algebra-colimit).

1. Apply lem-weil-pbc-sheaf-algebras-directed-colimit to construct the presheaf of
   sectionwise colimits and its ring sheafification. The coprojections give a colimit
   in algebra sheaves and, after forgetting multiplication, in modules.
2. Restrict to any open V. By lem-weil-pbc-module-restriction-open-immersion-colimits
   the underlying module cocone remains a colimit. Compare it with the algebra-sheaf
   colimit on V from Step 1: its comparison is an isomorphism of modules, hence of
   algebra sheaves, respecting the restricted coprojections.
3. For affine U = Spec R, identify every restricted stage with the tilde of its
   sections using lem-weil-pbc-affine-tilde-gamma-adjunction. Its left adjoint preserves
   colimits, so the restricted colimit module is the tilde of the module colimit.
4. Take global sections. The unit is an isomorphism and the triangle identity identifies
   the induced bijection with the canonical map. Compare the module colimit with the
   ring colimit: lem-weil-pbc-filtered-colimit-algebras-elementwise represents each ring
   colimit element at a stage, making the comparison surjective; its composite with the
   canonical map is bijective, making it injective too. Thus the affine section cocone
   is a ring colimit.
5. Step 3 and lem-weil-pbc-spec-module-tilde-sections give quasi-coherence locally on
   affine neighbourhoods (pqf-def-coherent). The full subcategory of quasi-coherent
   algebras inherits this colimit, including on every open V. -/
theorem quasiCoherentAlgebra_colimit
    (X : Scheme.{u}) (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (F : I ⥤ X.CommAlgebraSheaf)
    (hF : ∀ i : I, X.IsQuasiCoherentAlgebra (F.obj i)) :
    ∃ (c : Cocone F),
      Nonempty (IsColimit c) ∧ X.IsQuasiCoherentAlgebra c.pt ∧
      (∃ (p : Cocone (F ⋙ Under.forget X.sheaf ⋙
          sheafToPresheaf (Opens.grothendieckTopology X) CommRingCat)),
        Nonempty (IsColimit p) ∧
        ∃ (e : (presheafToSheaf (Opens.grothendieckTopology X) CommRingCat).obj p.pt ≅
            c.pt.right),
          ∀ i : I, p.ι.app i ≫ toSheafify (Opens.grothendieckTopology X) p.pt ≫
            e.hom.hom = (c.ι.app i).right.hom) ∧
      (∀ (U : X.Opens), IsAffineOpen U →
        Nonempty (IsColimit
          (((evaluation X.Opensᵒᵖ CommRingCat).obj (op U)).mapCocone
            ((sheafToPresheaf (Opens.grothendieckTopology X) CommRingCat).mapCocone
              ((Under.forget X.sheaf).mapCocone c))))) ∧
      (∀ (V : X.Opens), Nonempty (IsColimit
        ((Under.post ((Opens.grothendieckTopology X).overPullback CommRingCat V)).mapCocone
          c))) := by
  sorry

end AlgebraicGeometry.Scheme
