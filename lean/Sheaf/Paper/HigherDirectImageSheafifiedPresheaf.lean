/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
public import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.AlgebraicGeometry.EtaleSheaves
import Sheaf.AlgebraicGeometry.KInjectiveResolutions
import Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Higher direct images as sheafified cohomology presheaves

Source: Stacks Project, Lemma Tag 072W (lemma-higher-direct-images), and Section 21.2
(equation-cohomology-object-site)
(blueprint: lem-weil-pbc-higher-direct-image-sheafified-presheaf).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- For an arbitrary scheme morphism, `R^q p_* F` is the sheafification of
`V ↦ H^q(V ×_S X,F)`, with restriction induced by base change. Here `H^q(U,F)` is the
`q`-th right derived functor of the abelian-sheaf evaluation `G ↦ G(U)` (as in
lem-weil-pbc-injective-module-abelian-acyclic), and the restriction along `U' ⟶ U` is the
derived map `NatTrans.rightDerived` of evaluation restriction, i.e. the map induced on
`H^q` by the restriction maps `I^•(U) ⟶ I^•(U')` of an injective resolution of `F`.

Source: Stacks Project, Lemma Tag 072W and Section 21.2, equation-cohomology-object-site
(blueprint: lem-weil-pbc-higher-direct-image-sheafified-presheaf).

Proof:
1. Choose an injective resolution of `F` (def-sp-injective-resolutions), using the
Grothendieck property (def-weil-pbc-etale-sheaves, lem-sp-grothendieck-enough-injectives).
It is bounded below and K-injective (lem-weil-pbc-dplus-injective-representative,
def-weil-pbc-kinjective-resolutions), so the derived pushforward is represented by
`p_* I^•` (def-weil-pbc-direct-image). Comparison of resolutions is canonical up to
homotopy (prop-weil-pbc-kinjective-resolutions-exist).
2. Sections of `p_* I^•` over `V` are `I^•(V ×_S X)`, with restrictions along base change
(def-weil-pbc-direct-image, lem-weil-pbc-etale-base-change-finite-limits).
3. The right derived inclusion has value `H^q(I^•(U))` at `U`, since cohomology of
presheaves is sectionwise. This is `H^q(U,F)` with the required restrictions
(def-sp-left-exact-additive, lem-sp-derived-well-defined,
lem-weil-pbc-sheafification-exact).
4. Sheafification is exact and its counit is an isomorphism
(def-weil-pbc-sheafification, lem-weil-pbc-sheafification-exact), so it commutes with
cohomology (lem-weil-pbc-exact-functor-complex-cohomology). Therefore the cohomology sheaf
of `p_* I^•` is the sheafification of its sectionwise cohomology presheaf.
5. Combine these identifications. Their naturality and independence of resolutions
make the comparison canonical. -/
theorem higherDirectImageSheafifiedPresheaf {X S : Scheme.{u}} (p : X ⟶ S)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Nonempty
      ((presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          ((MorphismProperty.Over.pullback @Etale ⊤ p).op ⋙
            { obj := fun U ↦
                ((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
                  (evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj U).rightDerived q).obj F
              map := fun f ↦
                (NatTrans.rightDerived
                  (Functor.whiskerLeft (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
                    ((evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).map f)) q).app F
              map_id := fun U ↦ by
                simp only [CategoryTheory.Functor.map_id, Functor.whiskerLeft_id',
                  NatTrans.rightDerived_id, NatTrans.id_app]
              map_comp := fun f g ↦ by
                simp only [CategoryTheory.Functor.map_comp, Functor.whiskerLeft_comp,
                  NatTrans.rightDerived_comp, NatTrans.comp_app] }) ≅
        (DerivedCategory.Plus.homologyFunctor
          (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
          ((Etale.rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} p).obj
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F))) := by
  sorry

end AlgebraicGeometry
