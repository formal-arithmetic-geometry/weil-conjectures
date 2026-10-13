/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.Grp.Basic

/-! # Local representatives for a supplied abelian inverse-image adjunction

Source: Stacks Project, Tag 09XN, local description of inverse-image sections.
(blueprint: lem-weil-pbc-etale-abelian-local-unit-representatives). -/

@[expose] public section

universe u
open CategoryTheory Opposite AlgebraicGeometry

/-- Every inverse-image section has unit representatives on an etale cover.
Source: Stacks Project, Tag 09XN, proof of lemma-describe-pullback, paragraph
beginning "By construction"; compatibility with abelian structure and units.
(blueprint: lem-weil-pbc-etale-abelian-local-unit-representatives).

Proof: Form the underlying-set inverse image by the left Kan extension along
base change followed by sheafification. The sheafification unit is locally
surjective. Thus, on an etale covering of T, the section is represented by an
element of the pointwise Kan extension. Its indexing category of pairs (W,a)
is filtered because base change preserves finite limits. Consequently each
colimit element comes from a single section of F(W). The Kan unit followed by
the sheafification unit is the inverse-image adjunction unit, so the image of
that section is precisely the displayed expression. The abelian inverse image
has this underlying set inverse image, with the same unit. Finally compare its
left adjoint with H by uniqueness of left adjoints to the fixed pushforward;
the comparison preserves the specified unit and restriction maps. Transport
both the given section and its local representatives through that comparison.
Extract a covering indexed in Type (u+1) using the small etale topology's cover
criterion. Empty schemes admit the empty cover; no global representative on a
prescribed covering object is asserted. -/
theorem etaleAbelian_local_unit_representatives
    {X T : Scheme.{u + 1}} (p : T ⟶ X)
    (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hH : H ⊣ p.Etale.sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} X.smallEtaleTopology T.smallEtaleTopology)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (t : (H.obj F).obj.obj (op (Scheme.Etale.mk (𝟙 T)))) :
    ∃ (I : Type (u + 1)) (Z : I → T.Etale)
      (z : ∀ i, Z i ⟶ Scheme.Etale.mk (𝟙 T))
      (W : I → X.Etale) (a : ∀ i, Z i ⟶ p.Etale.obj (W i))
      (s : ∀ i, F.obj.obj (op (W i))),
      Sieve.ofArrows Z z ∈ T.smallEtaleTopology (Scheme.Etale.mk (𝟙 T)) ∧
      ∀ i, (H.obj F).obj.map (z i).op t =
        (H.obj F).obj.map (a i).op ((hH.unit.app F).hom.app (op (W i)) (s i)) := by
  sorry
