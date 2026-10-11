/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Continuous

/-!
# Cohomology over corresponding objects of equivalent sites

Source: Stacks Project, Cohomology on Sites, Section 01FT and Lemmas 03F3, 03YU,
with the equivalence-of-sites specialization described in the DAG
(blueprint: lem-weil-pbc-etale-cohomology-invariance-under-site-equivalence).
-/

@[expose] public section

universe u

namespace CategoryTheory

/-- Source: Stacks Project, Cohomology on Sites, Section 01FT and Lemmas 03F3, 03YU
(agent extension to equivalences of sites).
(blueprint: lem-weil-pbc-etale-cohomology-invariance-under-site-equivalence)

The isomorphism of sheaf-to-cohomology-presheaf functors identifies `Sheaf.H' G q W`
with `Sheaf.H' (e_* G) q (e.functor.obj W)`. Its naturality in the sheaf is the outer
natural isomorphism's naturality; naturality in the object is the naturality of each
component isomorphism of presheaves. Here `e_*` is precomposition with `e.inverse`.

Proof:
1. Cover preservation in both directions, together with the unit isomorphism and
   lem-weil-pbc-site-covering-isomorphic-family, gives preservation and reflection
   of coverings. Apply lem-weil-pbc-site-equivalence-is-morphism-of-sites to obtain
   continuous functors and quasi-inverse functors on abelian sheaves. These functors
   are additive because addition is computed sectionwise. Evaluation of the transported
   sheaf at `e(W)` is identified with evaluation at `W` by the sheaf's map of the unit.
   This identification is natural in both the sheaf and the object.
2. An injective resolution of `G` is carried to an injective resolution of `e_* G`
   by lem-weil-pbc-equivalence-injective-resolutions: additive equivalences preserve
   injectives, exact sequences, resolution maps, and homotopies.
3. Evaluating these resolutions gives isomorphic section complexes via the unit,
   compatibly with augmentations and restrictions. Taking degree-q cohomology gives
   the asserted natural isomorphism, with degree zero the identification of sections.
   Use def-weil-pbc-sites-and-cohomology for cohomology over objects. -/
theorem cohomology_site_equivalence
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : Precoverage C) (K : Precoverage D)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [K.HasIsos] [K.IsStableUnderComposition] [K.IsStableUnderBaseChange] [K.HasPullbacks]
    [HasSheafify J.toGrothendieck AddCommGrpCat.{u}]
    [HasSheafify K.toGrothendieck AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf J.toGrothendieck AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf K.toGrothendieck AddCommGrpCat.{u})]
    (e : C ≌ D)
    (hcover : ∀ (W : C) (R : Presieve W), R ∈ J W →
      R.map e.functor ∈ K (e.functor.obj W))
    (hcover_inv : ∀ (V : D) (R : Presieve V), R ∈ K V →
      R.map e.inverse ∈ J (e.inverse.obj V)) :
    ∃ (hi : e.inverse.IsContinuous K.toGrothendieck J.toGrothendieck),
      ∀ q : ℕ, Nonempty
        (Sheaf.cohomologyPresheafFunctor J.toGrothendieck q ≅
          e.inverse.sheafPushforwardContinuous AddCommGrpCat.{u}
            K.toGrothendieck J.toGrothendieck ⋙
          Sheaf.cohomologyPresheafFunctor K.toGrothendieck q ⋙
          (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ AddCommGrpCat.{u}).obj e.functor.op) := by
  sorry

end CategoryTheory
