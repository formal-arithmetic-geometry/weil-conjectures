/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleOpenObjectCohomologyMap
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective

/-! # Étale cohomology over an open object

Source: Stacks Project, Cohomology on Sites, Lemma 03F3 and Sites, Section 00XZ
(blueprint: def-weil-pbc-etale-open-comparison-data).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

namespace EtaleOpenComparison

/-- Canonical sections construction for the open-cohomology comparison.
Source: Stacks 03F3 and the free-abelian Yoneda adjunction.
(blueprint: def-weil-pbc-etale-open-comparison-data). -/
noncomputable def freeSectionsEquiv
    {C : Type (u + 1)} [Category.{u} C] (W : C)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (uliftYoneda.{u + 1}.obj W ⋙ AddCommGrpCat.free ⟶ F) ≃+ F.obj (Opposite.op W) where
  toEquiv := ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _).trans uliftYonedaEquiv
  map_add' a b := by
    change ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _ (a + b)).app
      (Opposite.op W) (ULift.up (𝟙 W)) = _
    simp only [Adjunction.homEquiv_apply, NatTrans.comp_app,
      Adjunction.whiskerRight_unit_app_app]
    rfl

/-- Canonical sections construction for the open-cohomology comparison.
Source: Stacks 03F3 and the free-abelian Yoneda adjunction.
(blueprint: def-weil-pbc-etale-open-comparison-data). -/
noncomputable def sectionsEquiv
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u + 1}] (W : C)
    (F : Sheaf J AddCommGrpCat.{u + 1}) :
    ((presheafToSheaf J AddCommGrpCat.{u + 1}).obj
      (uliftYoneda.{u + 1}.obj W ⋙ AddCommGrpCat.free) ⟶ F) ≃+ F.obj.obj (Opposite.op W) :=
  ((sheafificationAdjunction J AddCommGrpCat.{u + 1}).homAddEquiv _ F).trans
    (freeSectionsEquiv W F.obj)

/-- Canonical sections construction for the open-cohomology comparison.
Source: Stacks 03F3 and the free-abelian Yoneda adjunction.
(blueprint: def-weil-pbc-etale-open-comparison-data). -/
lemma sectionsEquiv_naturality
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u + 1}] (W : C)
    {F G : Sheaf J AddCommGrpCat.{u + 1}} (f : F ⟶ G)
    (a : (presheafToSheaf J AddCommGrpCat.{u + 1}).obj
      (uliftYoneda.{u + 1}.obj W ⋙ AddCommGrpCat.free) ⟶ F) :
    sectionsEquiv J W G (a ≫ f) =
      f.hom.app (Opposite.op W) (sectionsEquiv J W F a) := by
  dsimp only [sectionsEquiv, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply]
  rw [Adjunction.homEquiv_naturality_right]
  dsimp [freeSectionsEquiv]
  rfl

/-- Canonical sections construction for the open-cohomology comparison.
Source: Stacks 03F3 and the free-abelian Yoneda adjunction.
(blueprint: def-weil-pbc-etale-open-comparison-data). -/
noncomputable abbrev integerSheaf (U : Scheme.{u}) :=
  (constantSheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- Canonical sections construction for the open-cohomology comparison.
Source: Stacks 03F3 and the free-abelian Yoneda adjunction.
(blueprint: def-weil-pbc-etale-open-comparison-data). -/
noncomputable def restrictedSectionsEquiv
    {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (integerSheaf U ⟶
      (Etale.openImmersionRestriction (A := AddCommGrpCat.{u + 1}) j).obj G) ≃+
      G.obj.obj (Opposite.op (Scheme.Etale.mk j)) := by
  let e := ((constantSheafAdj U.smallEtaleTopology AddCommGrpCat.{u + 1}
    (MorphismProperty.Over.mkIdTerminal @Etale U)).homAddEquiv _
      ((Etale.openImmersionRestriction (A := AddCommGrpCat.{u + 1}) j).obj G)).trans
        (AddCommGrpCat.uliftZMultiplesAddEquiv _)
  let i : Scheme.Etale.mk (𝟙 U ≫ j) ≅ Scheme.Etale.mk j :=
    MorphismProperty.Over.isoMk (Iso.refl U) (Category.id_comp j)
  exact e.trans (G.obj.mapIso i.op.symm).addCommGroupIsoToAddEquiv

/-- Canonical sections construction for the open-cohomology comparison.
Source: Stacks 03F3 and the free-abelian Yoneda adjunction.
(blueprint: def-weil-pbc-etale-open-comparison-data). -/
lemma restrictedSectionsEquiv_naturality
    {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {G G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (f : G ⟶ G')
    (a : integerSheaf U ⟶
      (Etale.openImmersionRestriction (A := AddCommGrpCat.{u + 1}) j).obj G) :
    restrictedSectionsEquiv j G'
      (a ≫ (Etale.openImmersionRestriction (A := AddCommGrpCat.{u + 1}) j).map f) =
      f.hom.app (Opposite.op (Scheme.Etale.mk j)) (restrictedSectionsEquiv j G a) := by
  dsimp only [restrictedSectionsEquiv, AddEquiv.trans_apply,
    Adjunction.homAddEquiv_apply]
  rw [Adjunction.homEquiv_naturality_right]
  change G'.obj.map _ (f.hom.app _ _) = f.hom.app _ (G.obj.map _ _)
  exact (NatTrans.naturality_apply f.hom _ _).symm

end EtaleOpenComparison

end AlgebraicGeometry
