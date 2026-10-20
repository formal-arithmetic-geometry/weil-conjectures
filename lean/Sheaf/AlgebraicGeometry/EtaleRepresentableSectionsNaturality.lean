/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleOpenCohomologyComparison

/-! # Naturality of free-representable sections

The sections equivalence sends precomposition by a free-representable morphism to
restriction. This public helper is retained when retiring the Sheaf copy of the
generator-coherence module, whose upstream counterpart keeps this helper private.

(blueprint: lem-sbc-abelian-representable-sections-precomp).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
/-- Precomposition with the free-representable map is restriction of sections.
This is naturality of the sheafification and free-abelian adjunctions, followed
by naturality of the universe-lifted Yoneda equivalence. -/
lemma sectionsEquiv_precomp {X : Scheme.{u}} {A B : X.Etale}
    (a : A ⟶ B) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (f : (etaleOpenFreeSheaf X).obj B ⟶ F) :
    EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology A F
      ((etaleOpenFreeSheaf X).map a ≫ f) =
      F.obj.map a.op (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology B F f) := by
  change EtaleOpenComparison.freeSectionsEquiv A F.obj
    ((sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv _ _
      ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map
          (uliftYoneda.map a)) ≫ f)) = _
  rw [Adjunction.homEquiv_naturality_left]
  change uliftYonedaEquiv (((AddCommGrpCat.adj.whiskerRight X.Etaleᵒᵖ).homEquiv _ _)
    (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map (uliftYoneda.map a) ≫
      ((sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv
        _ _ f))) = _
  rw [Adjunction.homEquiv_naturality_left]
  exact (uliftYonedaEquiv_naturality _ a.op).symm

end AlgebraicGeometry.Etale
