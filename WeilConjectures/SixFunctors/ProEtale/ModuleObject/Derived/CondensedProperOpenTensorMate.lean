/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenProper.CondensedOpenProperPasting
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleObjectProjectionMap
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedPullbackCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage

/-!
# Condensed proper/open tensor mate

Source: `literature/blueprint/latest/blueprint/sec-six-functors/
sk-prop-sf-pf-coherence/prop-sf-pf-coherence.proof.md`,
independence of compactification paragraph (blueprint: lem-sf-condensed-proper-open-tensor-mate).

The statement uses the canonical normalized proper/open mate from
`CondensedOpenProper.Pasting`, the canonical module-object projection morphisms, and
explicit open-unit normalization equations for the two open tensor maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The canonical module-object projection morphism with the exact-model pullback
`P_f = D(f^*)` in its target: the published projection map
`R_f K ⊗ L ⟶ R_f (K ⊗ Lf^* L)` followed by `R_f (K ⊗ -)` of the canonical identification
`Lf^* ≅ D(f^*)` (`leftDerivedUpperStarIsoMapDerivedCategory`). The source endpoint is the
published one definitionally.
Source: the canonical-map convention (blueprint: def-sfb-module-object-projection-map). -/
noncomputable def canonicalModuleObjectProjectionMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : CondensedOpenProper.D Λ X) (L : CondensedOpenProper.D Λ Y) :
    ((derivedTensor Λ Y).obj ((CondensedOpenProper.R Λ f).obj K)).obj L ⟶
      (CondensedOpenProper.R Λ f).obj (((derivedTensor Λ X).obj K).obj
        ((CondensedOpenProper.P Λ f).obj L)) :=
  (moduleObjectProjectionMap Λ f K L :
      ((derivedTensor Λ Y).obj ((CondensedOpenProper.R Λ f).obj K)).obj L ⟶
        (CondensedOpenProper.R Λ f).obj (((derivedTensor Λ X).obj K).obj
          ((upperStar Λ f).leftDerivedFunctor.obj L))) ≫
    (CondensedOpenProper.R Λ f).map (((derivedTensor Λ X).obj K).map
      ((leftDerivedUpperStarIsoMapDerivedCategory Λ f).hom.app L))

/-- The pullback identification `P_r P_i ≅ P_v P_p` induced by the commuting square. -/
noncomputable def canonicalPullbackComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {A B C D : Scheme.{u}} {v : A ⟶ B} {r : A ⟶ C} {p : B ⟶ D} {i : C ⟶ D}
    (_sq : CommSq v r p i) (N : CondensedOpenProper.D Λ D) :
    (CondensedOpenProper.P Λ r).obj ((CondensedOpenProper.P Λ i).obj N) ⟶
      (CondensedOpenProper.P Λ v).obj ((CondensedOpenProper.P Λ p).obj N) := by
  exact (CondensedOpenProper.pComp Λ r i).inv.app N ≫
    eqToHom (by rw [_sq.w]) ≫ (CondensedOpenProper.pComp Λ v p).hom.app N

/-- The tensor transport induced by the canonical pullback comparison. -/
noncomputable def canonicalTensorPullbackComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {A B C D : Scheme.{u}} {v : A ⟶ B} {r : A ⟶ C} {p : B ⟶ D} {i : C ⟶ D}
    (_sq : CommSq v r p i) (M : CondensedOpenProper.D Λ A) (N : CondensedOpenProper.D Λ D) :
    ((derivedTensor Λ A).obj M).obj
        ((CondensedOpenProper.P Λ r).obj ((CondensedOpenProper.P Λ i).obj N)) ⟶
      ((derivedTensor Λ A).obj M).obj
        ((CondensedOpenProper.P Λ v).obj ((CondensedOpenProper.P Λ p).obj N)) :=
  ((derivedTensor Λ A).obj M).map (canonicalPullbackComparison Λ _sq N)

/-- The canonical inverse pullback tensor comparison `P_j K ⊗ P_j L ⟶ P_j (K ⊗ L)` for the
exact model `P_j = D(j^*)`: the published inverse of `Lj^*(K ⊗ L) ≅ Lj^* K ⊗ Lj^* L`
(`leftDerivedUpperStarTensorIso`), conjugated by the canonical identification
`Lj^* ≅ D(j^*)` (`leftDerivedUpperStarIsoMapDerivedCategory`) in all three places.
Source: the canonical ringed-derived monoidal comparison
(blueprint: lem-sfb-ringed-derived-monoidal-comparisons). -/
noncomputable def canonicalOpenTensorComparisonInv
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U X : Scheme.{u}} (j : U ⟶ X)
    (K : CondensedOpenProper.D Λ X) (L : CondensedOpenProper.D Λ X) :
    ((derivedTensor Λ U).obj ((CondensedOpenProper.P Λ j).obj K)).obj
        ((CondensedOpenProper.P Λ j).obj L) ⟶
      (CondensedOpenProper.P Λ j).obj (((derivedTensor Λ X).obj K).obj L) :=
  ((derivedTensor Λ U).map ((leftDerivedUpperStarIsoMapDerivedCategory Λ j).inv.app K)).app
      ((CondensedOpenProper.P Λ j).obj L) ≫
    ((derivedTensor Λ U).obj ((upperStar Λ j).leftDerivedFunctor.obj K)).map
      ((leftDerivedUpperStarIsoMapDerivedCategory Λ j).inv.app L) ≫
    (((leftDerivedUpperStarTensorIso Λ j).app K).app L).inv ≫
    (leftDerivedUpperStarIsoMapDerivedCategory Λ j).hom.app (((derivedTensor Λ X).obj K).obj L)

/-- The normalized open tensor map at `j` is characterized by the open-adjunction unit.
Source: the open-unit equation in `lem-sf-open-tensor-normalization`. -/
def openTensorUnitNormalization
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : CondensedOpenProper.D Λ U) (N : CondensedOpenProper.D Λ X)
    (delta : ((derivedTensor Λ X).obj ((CondensedOpenProper.J Λ j).obj M)).obj N ⟶
      (CondensedOpenProper.J Λ j).obj (((derivedTensor Λ U).obj M).obj
        ((CondensedOpenProper.P Λ j).obj N))) : Prop :=
  (((derivedTensor Λ U).map
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit.app M)).app
      ((CondensedOpenProper.P Λ j).obj N) ≫
    canonicalOpenTensorComparisonInv Λ j ((CondensedOpenProper.J Λ j).obj M) N ≫
    (CondensedOpenProper.P Λ j).map delta) =
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit.app
        (((derivedTensor Λ U).obj M).obj ((CondensedOpenProper.P Λ j).obj N))

private theorem monoidal_of_oplax
    {F G : DD ⥤ AA} [F.Monoidal] [G.Monoidal] (t : F ⟶ G)
    (hu : t.app (𝟙_ DD) ≫ Functor.OplaxMonoidal.η G = Functor.OplaxMonoidal.η F)
    (ht : ∀ X Y : DD, Functor.OplaxMonoidal.δ F X Y ≫ (t.app X ⊗ₘ t.app Y) =
      t.app (X ⊗ Y) ≫ Functor.OplaxMonoidal.δ G X Y) : t.IsMonoidal := by
  constructor
  · apply (cancel_mono (Functor.OplaxMonoidal.η G)).1
    rw [Category.assoc, hu, Functor.Monoidal.ε_η, Functor.Monoidal.ε_η]
  · intro X Y
    apply (cancel_mono (Functor.OplaxMonoidal.δ G X Y)).1
    rw [Category.assoc, ← ht, ← Category.assoc, Functor.Monoidal.μ_δ,
      Category.id_comp, Category.assoc, Functor.Monoidal.μ_δ, Category.comp_id]

private theorem oplax_of_monoidal
    {F G : DD ⥤ AA} [F.Monoidal] [G.Monoidal] (t : F ⟶ G) [t.IsMonoidal]
    (K L : DD) :
    Functor.OplaxMonoidal.δ F K L ≫ (t.app K ⊗ₘ t.app L) =
      t.app (K ⊗ L) ≫ Functor.OplaxMonoidal.δ G K L := by
  apply (cancel_epi (Functor.LaxMonoidal.μ F K L)).1
  rw [← Category.assoc, Functor.Monoidal.μ_δ, Category.id_comp,
    ← Category.assoc, NatTrans.IsMonoidal.tensor, Category.assoc,
    Functor.Monoidal.μ_δ, Category.comp_id]

private theorem projection_transport
    {F : DD ⥤ AA} {G : AA ⥤ DD} [F.Monoidal]
    (a : F ⊣ G) {F' : DD ⥤ AA} (e : F ≅ F') (M : AA) (N : DD) :
    letI := Functor.Monoidal.transport e
    ((a.rightAdjointProjectionMap (Functor.OplaxMonoidal.δNatTrans F)).app M).app N ≫
        G.map (𝟙 M ⊗ₘ e.hom.app N) =
      (((a.ofNatIsoLeft e).rightAdjointProjectionMap
        (Functor.OplaxMonoidal.δNatTrans F')).app M).app N := by
  letI := Functor.Monoidal.transport e
  simp only [Adjunction.rightAdjointProjectionMap_app_app, Adjunction.homEquiv_unit,
    Adjunction.ofNatIsoLeft_unit, Adjunction.ofNatIsoLeft_counit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.OplaxMonoidal.δNatTrans_app_app, Functor.Monoidal.transport_δ,
    Functor.map_comp, Category.assoc]
  simp only [curriedTensor_obj_obj, curriedTensor_map_app,
    Iso.hom_inv_id_app_assoc, ← MonoidalCategory.tensorHom_id, ← MonoidalCategory.id_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id_app, Category.comp_id,
    Category.id_comp, ← G.map_comp]
  congr 2
  simp only [Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc, Category.comp_id, Category.id_comp]
  exact congrArg (fun q ↦ Functor.OplaxMonoidal.δ F (G.obj M) N ≫
    (q ⊗ₘ e.hom.app N)) (Category.comp_id (a.counit.app M))

private theorem projection_exchange
    (Pr : CC ⥤ AA) (Rr : AA ⥤ CC) (Pp : DD ⥤ BB) (Rp : BB ⥤ DD)
    (Pi : DD ⥤ CC) (Pv : BB ⥤ AA)
    [Pr.Monoidal] [Pp.Monoidal] [Pi.Monoidal] [Pv.Monoidal]
    (ar : Pr ⊣ Rr) (ap : Pp ⊣ Rp) (theta : Pi ⋙ Pr ≅ Pp ⋙ Pv)
    (htheta : ∀ K L : DD,
      Pr.map (Functor.OplaxMonoidal.δ Pi K L) ≫
          Functor.OplaxMonoidal.δ Pr (Pi.obj K) (Pi.obj L) ≫
          (theta.hom.app K ⊗ₘ theta.hom.app L) =
        theta.hom.app (K ⊗ L) ≫ Pv.map (Functor.OplaxMonoidal.δ Pp K L) ≫
          Functor.OplaxMonoidal.δ Pv (Pp.obj K) (Pp.obj L))
    (F : BB) (N : DD) :
    let beta := (mateEquiv ap ar (TwoSquare.mk Pi Pp Pr Pv theta.hom)).natTrans
    let piP := ap.rightAdjointProjectionMap (Functor.OplaxMonoidal.δNatTrans Pp)
    let piR := ar.rightAdjointProjectionMap (Functor.OplaxMonoidal.δNatTrans Pr)
    Functor.LaxMonoidal.μ Pi (Rp.obj F) N ≫ Pi.map ((piP.app F).app N) ≫
        beta.app (F ⊗ Pp.obj N) =
      (beta.app F ⊗ₘ 𝟙 (Pi.obj N)) ≫ (piR.app (Pv.obj F)).app (Pi.obj N) ≫
        Rr.map ((𝟙 (Pv.obj F) ⊗ₘ theta.hom.app N) ≫
          Functor.LaxMonoidal.μ Pv F (Pp.obj N)) := by
  dsimp only
  let beta := (mateEquiv ap ar (TwoSquare.mk Pi Pp Pr Pv theta.hom)).natTrans
  have hm (K L : DD) :
      Pr.map (Functor.LaxMonoidal.μ Pi K L) ≫ theta.hom.app (K ⊗ L) ≫
          Pv.map (Functor.OplaxMonoidal.δ Pp K L) =
        Functor.OplaxMonoidal.δ Pr (Pi.obj K) (Pi.obj L) ≫
          (theta.hom.app K ⊗ₘ theta.hom.app L) ≫
          Functor.LaxMonoidal.μ Pv (Pp.obj K) (Pp.obj L) := by
    apply (cancel_mono (Functor.OplaxMonoidal.δ Pv (Pp.obj K) (Pp.obj L))).1
    simp only [Category.assoc, Functor.Monoidal.μ_δ, Category.comp_id]
    rw [← htheta, ← Pr.map_comp_assoc, Functor.Monoidal.μ_δ, Pr.map_id, Category.id_comp]
    erw [Category.comp_id]
  have hb (E : BB) : Pr.map (beta.app E) ≫ ar.counit.app (Pv.obj E) =
      theta.hom.app (Rp.obj E) ≫ Pv.map (ap.counit.app E) := by
    exact mateEquiv_counit ap ar (TwoSquare.mk Pi Pp Pr Pv theta.hom) E
  apply (ar.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have hc₁ := ar.counit.naturality (Functor.LaxMonoidal.μ Pv F (Pp.obj N))
  have hc₂ := ar.counit.naturality (𝟙 (Pv.obj F) ⊗ₘ theta.hom.app N)
  dsimp only [Functor.comp_map, Functor.id_map] at hc₁ hc₂
  rw [hb, hc₁, reassoc_of% hc₂]
  erw [ar.map_rightAdjointProjectionMap_app_app_comp_counit_assoc]
  simp only [Functor.OplaxMonoidal.δNatTrans_app_app, curriedTensor_map_app,
    ← MonoidalCategory.tensorHom_id, Category.assoc]
  have hn := theta.hom.naturality
    (((ap.rightAdjointProjectionMap (Functor.OplaxMonoidal.δNatTrans Pp)).app F).app N)
  change Pr.map (Pi.map _) ≫ theta.hom.app (Rp.obj (F ⊗ Pp.obj N)) =
    theta.hom.app (Rp.obj F ⊗ N) ≫ Pv.map (Pp.map _) at hn
  rw [reassoc_of% hn, ← Pv.map_comp]
  erw [ap.map_rightAdjointProjectionMap_app_app_comp_counit
    (Functor.OplaxMonoidal.δNatTrans Pp) F N]
  simp only [Functor.OplaxMonoidal.δNatTrans_app_app, curriedTensor_map_app,
    ← MonoidalCategory.tensorHom_id, Functor.map_comp, Category.assoc]
  rw [reassoc_of% (hm (Rp.obj F) N)]
  have hd := Functor.OplaxMonoidal.δ_natural Pr (beta.app F) (𝟙 (Pi.obj N))
  simp only [CategoryTheory.Functor.map_id] at hd
  dsimp only [Functor.comp_obj] at hd
  rw [← reassoc_of% hd]
  simp only [MonoidalCategory.tensorHom_comp_tensorHom_assoc, Category.comp_id, Category.id_comp]
  erw [hb F]
  rw [← Functor.LaxMonoidal.μ_natural]
  simp only [CategoryTheory.Functor.map_id, MonoidalCategory.tensorHom_comp_tensorHom_assoc,
    Category.comp_id,
    Category.id_comp, Category.assoc]
  rfl

private theorem normalized_tensor_square
    (Pr : CC ⥤ AA) (Rr : AA ⥤ CC) (Pp : DD ⥤ BB) (Rp : BB ⥤ DD)
    (Pi : DD ⥤ CC) (Pv : BB ⥤ AA) (Ji : CC ⥤ DD) (Jv : AA ⥤ BB)
    [Pi.Monoidal] [Pv.Monoidal]
    (ai : Ji ⊣ Pi) (uv : 𝟭 AA ⟶ Jv ⋙ Pv)
    (theta : Pi ⋙ Pr ≅ Pp ⋙ Pv)
    (beta : Rp ⋙ Pi ⟶ Pv ⋙ Rr) (gamma : Rr ⋙ Ji ⟶ Jv ⋙ Rp)
    (piR : ∀ (K : AA) (L : CC), Rr.obj K ⊗ L ⟶ Rr.obj (K ⊗ Pr.obj L))
    (piP : ∀ (K : BB) (L : DD), Rp.obj K ⊗ L ⟶ Rp.obj (K ⊗ Pp.obj L))
    (hgamma : ∀ K : AA,
      ai.unit.app (Rr.obj K) ≫ Pi.map (gamma.app K) ≫ beta.app (Jv.obj K) =
        Rr.map (uv.app K))
    (M : AA) (N : DD)
    (dv : Jv.obj M ⊗ Pp.obj N ⟶ Jv.obj (M ⊗ Pv.obj (Pp.obj N)))
    (di : Ji.obj (Rr.obj M) ⊗ N ⟶ Ji.obj (Rr.obj M ⊗ Pi.obj N))
    (hdv : (uv.app M ⊗ₘ 𝟙 (Pv.obj (Pp.obj N))) ≫
        Functor.LaxMonoidal.μ Pv (Jv.obj M) (Pp.obj N) ≫ Pv.map dv =
      uv.app (M ⊗ Pv.obj (Pp.obj N)))
    (hdi : (ai.unit.app (Rr.obj M) ⊗ₘ 𝟙 (Pi.obj N)) ≫
        Functor.LaxMonoidal.μ Pi (Ji.obj (Rr.obj M)) N ≫ Pi.map di =
      ai.unit.app (Rr.obj M ⊗ Pi.obj N))
    (hnat : (Rr.map (uv.app M) ⊗ₘ 𝟙 (Pi.obj N)) ≫
        piR (Pv.obj (Jv.obj M)) (Pi.obj N) =
      piR M (Pi.obj N) ≫ Rr.map (uv.app M ⊗ₘ 𝟙 (Pr.obj (Pi.obj N))))
    (hproj : Functor.LaxMonoidal.μ Pi (Rp.obj (Jv.obj M)) N ≫
        Pi.map (piP (Jv.obj M) N) ≫ beta.app (Jv.obj M ⊗ Pp.obj N) =
      (beta.app (Jv.obj M) ⊗ₘ 𝟙 (Pi.obj N)) ≫
        piR (Pv.obj (Jv.obj M)) (Pi.obj N) ≫
        Rr.map ((𝟙 (Pv.obj (Jv.obj M)) ⊗ₘ theta.hom.app N) ≫
          Functor.LaxMonoidal.μ Pv (Jv.obj M) (Pp.obj N)))
    [Epi (ai.counit.app (Ji.obj (Rr.obj M) ⊗ N))]
    [IsIso (ai.unit.app (Rr.obj M))]
    [IsIso (beta.app (Jv.obj (M ⊗ Pv.obj (Pp.obj N))))] :
    (gamma.app M ⊗ₘ 𝟙 N) ≫ piP (Jv.obj M) N ≫ Rp.map dv =
      di ≫ Ji.map (piR M (Pi.obj N)) ≫ gamma.app (M ⊗ Pr.obj (Pi.obj N)) ≫
        (Jv ⋙ Rp).map (𝟙 M ⊗ₘ theta.hom.app N) := by
  apply (cancel_epi (ai.counit.app (Ji.obj (Rr.obj M) ⊗ N))).1
  apply (ai.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc,
    ai.right_triangle_components_assoc]
  apply (cancel_epi ((ai.unit.app (Rr.obj M) ⊗ₘ 𝟙 (Pi.obj N)) ≫
    Functor.LaxMonoidal.μ Pi (Ji.obj (Rr.obj M)) N)).1
  apply (cancel_mono (beta.app (Jv.obj (M ⊗ Pv.obj (Pp.obj N))))).1
  simp only [Category.assoc]
  have hleft :
      ((ai.unit.app (Rr.obj M) ⊗ₘ 𝟙 (Pi.obj N)) ≫
        Functor.LaxMonoidal.μ Pi (Ji.obj (Rr.obj M)) N) ≫
        Pi.map ((gamma.app M ⊗ₘ 𝟙 N) ≫ piP (Jv.obj M) N ≫ Rp.map dv) ≫
        beta.app (Jv.obj (M ⊗ Pv.obj (Pp.obj N))) =
      piR M (Pi.obj N) ≫ Rr.map
        ((𝟙 M ⊗ₘ theta.hom.app N) ≫ uv.app (M ⊗ Pv.obj (Pp.obj N))) := by
    have hb := beta.naturality dv
    dsimp only [Functor.comp_map, Functor.comp_obj] at hb
    simp only [Functor.map_comp, Category.assoc]
    rw [hb]
    rw [← Functor.LaxMonoidal.μ_natural_assoc]
    simp only [Functor.comp_obj, CategoryTheory.Functor.map_id,
      MonoidalCategory.tensorHom_comp_tensorHom_assoc,
      Category.comp_id, Category.assoc]
    rw [reassoc_of% hproj]
    simp only [MonoidalCategory.tensorHom_comp_tensorHom_assoc, Category.comp_id]
    rw [Category.assoc, hgamma M]
    rw [reassoc_of% hnat]
    simp only [← Rr.map_comp, Category.assoc]
    congr 2
    rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]
    rw [Category.comp_id, Category.id_comp]
    have hx := congrArg (fun f ↦ (𝟙 M ⊗ₘ theta.hom.app N) ≫ f) hdv
    simp only [Category.assoc,
      MonoidalCategory.tensorHom_comp_tensorHom_assoc, Category.id_comp] at hx
    erw [Category.comp_id] at hx
    exact hx
  have hright :
      ((ai.unit.app (Rr.obj M) ⊗ₘ 𝟙 (Pi.obj N)) ≫
        Functor.LaxMonoidal.μ Pi (Ji.obj (Rr.obj M)) N) ≫
        Pi.map (di ≫ Ji.map (piR M (Pi.obj N)) ≫
          gamma.app (M ⊗ Pr.obj (Pi.obj N)) ≫
          (Jv ⋙ Rp).map (𝟙 M ⊗ₘ theta.hom.app N)) ≫
        beta.app (Jv.obj (M ⊗ Pv.obj (Pp.obj N))) =
      piR M (Pi.obj N) ≫ Rr.map
        ((𝟙 M ⊗ₘ theta.hom.app N) ≫ uv.app (M ⊗ Pv.obj (Pp.obj N))) := by
    have hu := ai.unit.naturality (piR M (Pi.obj N))
    dsimp only [Functor.id_map, Functor.comp_map] at hu
    have hb := beta.naturality (Jv.map (𝟙 M ⊗ₘ theta.hom.app N))
    dsimp only [Functor.comp_map, Functor.comp_obj] at hb
    simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
    rw [reassoc_of% hdi, ← reassoc_of% hu, hb,
      reassoc_of% (hgamma (M ⊗ Pr.obj (Pi.obj N))), ← Rr.map_comp]
    rw [← Rr.map_comp]
    congr 2
    exact (uv.naturality (𝟙 M ⊗ₘ theta.hom.app N)).symm
  simpa only [Functor.map_comp, Category.assoc] using hleft.trans hright.symm

private noncomputable instance (priority := 10) exactPullMonoidal
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedOpenProper.P Λ f).Monoidal :=
  Functor.Monoidal.transport (leftDerivedUpperStarIsoMapDerivedCategory Λ f)

private theorem exactPull_mu
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K L : CondensedOpenProper.D Λ Y) :
    canonicalOpenTensorComparisonInv Λ f K L =
      Functor.LaxMonoidal.μ (CondensedOpenProper.P Λ f) K L := by
  rw [Functor.Monoidal.transport_μ]
  simp only [canonicalOpenTensorComparisonInv, derivedTensor, curriedTensor_map_app,
    curriedTensor_obj_map, MonoidalCategory.tensorHom_def, Category.assoc]
  rfl

private theorem canonicalProjection_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : CondensedOpenProper.D Λ X) (N : CondensedOpenProper.D Λ Y) :
    canonicalModuleObjectProjectionMap Λ f M N =
      ((((upperStarLowerStarAdjunction Λ f).mapDerivedCategoryRightDerivedAdjunction
        ).rightAdjointProjectionMap
          (Functor.OplaxMonoidal.δNatTrans (CondensedOpenProper.P Λ f))).app M).app N := by
  rw [← exactAdjunction_eq]
  have h := projection_transport (derivedUpperStarLowerStarAdjunction Λ f)
    (leftDerivedUpperStarIsoMapDerivedCategory Λ f) M N
  change (((derivedUpperStarLowerStarAdjunction Λ f).rightAdjointProjectionMap
      (Functor.OplaxMonoidal.δNatTrans (upperStar Λ f).leftDerivedFunctor)).app M).app N ≫
      (lowerStar Λ f).rightDerivedFunctor.map
        (M ◁ (leftDerivedUpperStarIsoMapDerivedCategory Λ f).hom.app N) = _
  erw [MonoidalCategory.id_tensorHom M
    ((leftDerivedUpperStarIsoMapDerivedCategory Λ f).hom.app N)] at h
  exact h

private theorem nativePull_delta
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K L : CondensedOpenProper.D Λ Y) :
    Functor.OplaxMonoidal.δ (upperStar Λ f).leftDerivedFunctor K L =
      ((leftDerivedUpperStarTensor Λ f).app K).app L := by
  rfl

private theorem nativePull_eta
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Functor.OplaxMonoidal.η (upperStar Λ f).leftDerivedFunctor =
      (leftDerivedUpperStarUnitIso Λ f).hom := by
  rfl

private theorem nativeSquare_monoidal
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {A B C D : Scheme.{u}} {v : A ⟶ B} {r : A ⟶ C} {p : B ⟶ D} {i : C ⟶ D}
    (sq : CommSq v r p i) : (pullbackSquareComparison Λ sq).hom.IsMonoidal := by
  apply monoidal_of_oplax
  · simpa only [Functor.OplaxMonoidal.comp_η,
    nativePull_eta] using pullbackSquareComparison_unit Λ sq
  · intro K L
    simpa only [Functor.OplaxMonoidal.comp_δ, nativePull_delta, Category.assoc] using
      pullbackSquareComparison_tensor Λ sq K L

private theorem nativeComp_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    leftDerivedUpperStarComp Λ f g =
      leftDerivedUpperStarIsoMapDerivedCategory Λ (f ≫ g) ≪≫
        CondensedOpenProper.pComp Λ f g ≪≫
        (Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ g)
          (upperStar Λ f).leftDerivedFunctor ≪≫
          Functor.isoWhiskerLeft (CondensedOpenProper.P Λ g)
            (leftDerivedUpperStarIsoMapDerivedCategory Λ f)).symm := by
  apply Iso.ext
  ext M
  simp [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, CondensedOpenProper.pComp,
    leftDerivedUpperStarIsoMapDerivedCategory]

private theorem exactEquality_transport
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    Functor.mapDerivedCategoryNatIso (eqToIso (congrArg (upperStar Λ) h)) =
      eqToIso (congrArg (CondensedOpenProper.P Λ) h) := by
  subst h
  apply Iso.ext
  exact Functor.mapDerivedCategoryNatIso_refl

private theorem totalEquality_transport_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm ≪≫
      eqToIso (congrArg (fun a ↦ (upperStar Λ a).leftDerivedFunctor) h) ≪≫
      leftDerivedUpperStarIsoMapDerivedCategory Λ g =
      eqToIso (congrArg (CondensedOpenProper.P Λ) h) := by
  subst h
  simp

private theorem equalityIso_app {C E : Type*} [Category C] [Category E]
    {F G : C ⥤ E} (h : F = G) (N : C) :
    (eqToIso h).hom.app N = eqToHom (Functor.congr_obj h N) := by
  subst h
  rfl

private theorem exactSquare_via_compositors
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {A B C D : Scheme.{u}} {v : A ⟶ B} {r : A ⟶ C} {p : B ⟶ D} {i : C ⟶ D}
    (sq : CommSq v r p i) :
    derivedOpenCoherencePullbackSquare Λ sq =
      (CondensedOpenProper.pComp Λ r i).symm ≪≫
        eqToIso (congrArg (CondensedOpenProper.P Λ) sq.w.symm) ≪≫
        CondensedOpenProper.pComp Λ v p := by
  apply Iso.ext
  simp only [derivedOpenCoherencePullbackSquare, openCoherencePullbackSquare,
    CondensedOpenProper.pComp, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
    exactEquality_transport Λ sq.w.symm, Category.assoc]

private theorem exactSquare_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {A B C D : Scheme.{u}} {v : A ⟶ B} {r : A ⟶ C} {p : B ⟶ D} {i : C ⟶ D}
    (sq : CommSq v r p i) :
    derivedOpenCoherencePullbackSquare Λ sq =
      (Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ i)
        (upperStar Λ r).leftDerivedFunctor ≪≫
        Functor.isoWhiskerLeft (CondensedOpenProper.P Λ i)
          (leftDerivedUpperStarIsoMapDerivedCategory Λ r)).symm ≪≫
      pullbackSquareComparison Λ sq ≪≫
      (Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ p)
        (upperStar Λ v).leftDerivedFunctor ≪≫
        Functor.isoWhiskerLeft (CondensedOpenProper.P Λ p)
          (leftDerivedUpperStarIsoMapDerivedCategory Λ v)) := by
  rw [exactSquare_via_compositors Λ sq]
  conv_rhs =>
    unfold pullbackSquareComparison
    rw [nativeComp_eq Λ r i, nativeComp_eq Λ v p]
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc,
    Iso.symm_self_id_assoc, Iso.symm_self_id, Iso.trans_refl, Iso.refl_trans]
  simpa only [Iso.trans_assoc] using
    congrArg (fun z ↦ (CondensedOpenProper.pComp Λ r i).symm ≪≫ z ≪≫
      CondensedOpenProper.pComp Λ v p) (totalEquality_transport_iso Λ sq.w.symm).symm

private theorem exactSquare_component
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {A B C D : Scheme.{u}} {v : A ⟶ B} {r : A ⟶ C} {p : B ⟶ D} {i : C ⟶ D}
    (sq : CommSq v r p i) (N : CondensedOpenProper.D Λ D) :
    (derivedOpenCoherencePullbackSquare Λ sq).hom.app N =
      canonicalPullbackComparison Λ sq N := by
  rw [exactSquare_via_compositors Λ sq]
  simp only [canonicalPullbackComparison, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, equalityIso_app]

private theorem exactSquare_monoidal
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {A B C D : Scheme.{u}} {v : A ⟶ B} {r : A ⟶ C} {p : B ⟶ D} {i : C ⟶ D}
    (sq : CommSq v r p i) :
    (derivedOpenCoherencePullbackSquare Λ sq).hom.IsMonoidal := by
  have hi := Functor.Monoidal.natTransIsMonoidal_of_transport
    (leftDerivedUpperStarIsoMapDerivedCategory Λ i)
  have hr := Functor.Monoidal.natTransIsMonoidal_of_transport
    (leftDerivedUpperStarIsoMapDerivedCategory Λ r)
  have hp := Functor.Monoidal.natTransIsMonoidal_of_transport
    (leftDerivedUpperStarIsoMapDerivedCategory Λ p)
  have hv := Functor.Monoidal.natTransIsMonoidal_of_transport
    (leftDerivedUpperStarIsoMapDerivedCategory Λ v)
  have ht := nativeSquare_monoidal Λ sq
  rw [exactSquare_eq]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv]
  infer_instance

private theorem restriction_beta_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {A B C D : Scheme.{u}} {v : A ⟶ B} {r : A ⟶ C} {p : B ⟶ D} {i : C ⟶ D}
    [IsOpenImmersion v] [IsOpenImmersion i]
    [QuasiCompact v] [QuasiCompact i] [IsProper p] [IsProper r]
    (sq : CommSq v r p i) (data : CondensedOpenProper.Pasting Λ)
    (K : CondensedOpenProper.D Λ A) :
    IsIso ((derivedDirectImageOpenRestriction Λ sq).app
      ((CondensedOpenProper.J Λ v).obj K)) := by
  try dsimp only [CondensedOpenProper.P, CondensedOpenProper.R,
    moduleObjectDerivedPushforward] at ⊢
  have := data.restriction_isIso sq (Or.inr ⟨inferInstance, inferInstance⟩)
  have h : IsIso ((derivedDirectImageOpenRestriction Λ sq).app
      ((CondensedOpenProper.J Λ v).obj K) ≫
      (CondensedOpenProper.R Λ r).map ((data.units.unitIso v).inv.app K)) := by
    have h0 := (inferInstance : IsIso
      ((CondensedOpenProper.restriction Λ data.units sq).app K))
    dsimp only [CondensedOpenProper.restriction, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Category.id_comp,
      Category.comp_id, Category.assoc] at h0
    dsimp only [CondensedOpenProper.R, moduleObjectDerivedPushforward] at h0 ⊢
    erw [Category.comp_id] at h0
    simpa only [Category.comp_id, Category.id_comp] using h0
  haveI : IsIso ((CondensedOpenProper.R Λ r).map
      ((data.units.unitIso v).inv.app K)) := inferInstance
  exact IsIso.of_isIso_comp_right _
    ((CondensedOpenProper.R Λ r).map ((data.units.unitIso v).inv.app K))

private theorem gamma_normalization
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {A B C D : Scheme.{u}} {v : A ⟶ B} {r : A ⟶ C} {p : B ⟶ D} {i : C ⟶ D}
    [IsOpenImmersion v] [IsOpenImmersion i]
    [QuasiCompact v] [QuasiCompact i] [IsProper p] [IsProper r]
    (sq : CommSq v r p i) (data : CondensedOpenProper.Pasting Λ)
    (M : CondensedOpenProper.D Λ A) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i).unit.app
        ((CondensedOpenProper.R Λ r).obj M) ≫
      (CondensedOpenProper.P Λ i).map ((CondensedOpenProper.gamma Λ data.units sq).app M) ≫
      (derivedDirectImageOpenRestriction Λ sq).app ((CondensedOpenProper.J Λ v).obj M) =
    (CondensedOpenProper.R Λ r).map
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ v).unit.app M) := by
  try dsimp only [CondensedOpenProper.P, CondensedOpenProper.R,
    moduleObjectDerivedPushforward] at ⊢
  letI := data.restriction_isIso sq (Or.inr ⟨inferInstance, inferInstance⟩)
  have ht : (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i).homEquiv _ _
      ((CondensedOpenProper.gamma Λ data.units sq).app M) =
      (CondensedOpenProper.comparisonInverse
        (CondensedOpenProper.restriction Λ data.units sq)).app M := by
    simp only [CondensedOpenProper.gamma, NatTrans.comp_app, Functor.leftUnitor_inv_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
      Functor.rightUnitor_hom_app, Functor.comp_obj, Functor.id_obj,
      Category.id_comp, Category.comp_id]
    exact (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i).homEquiv _ _
      |>.apply_symm_apply _
  have h : (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i).homEquiv _ _
      ((CondensedOpenProper.gamma Λ data.units sq).app M) ≫
      (CondensedOpenProper.restriction Λ data.units sq).app M = 𝟙 _ := by
    rw [ht]
    classical
    simp only [CondensedOpenProper.comparisonInverse, dif_pos (inferInstance : IsIso
      (CondensedOpenProper.restriction Λ data.units sq)), ← NatTrans.comp_app,
      IsIso.inv_hom_id, NatTrans.id_app]
  rw [Adjunction.homEquiv_unit] at h
  have h' := congrArg (fun f ↦ f ≫ (CondensedOpenProper.R Λ r).map
    ((data.units.unitIso v).hom.app M)) h
  simp only [CondensedOpenProper.restriction, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Functor.comp_obj, Functor.id_obj,
    Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app, Category.comp_id,
    Category.id_comp] at h'
  erw [CategoryTheory.Functor.map_id] at h'
  dsimp only [CondensedOpenProper.R, moduleObjectDerivedPushforward] at h'
  erw [Category.comp_id] at h'
  simpa only [Category.comp_id, data.units.normalized] using h'

/-- Condensed proper/open tensor compatibility for ordinary unbounded derived categories.

Fix a prime `ell`, a positive-characteristic field `k` with `char(k) ≠ ell`, an admissible
coefficient ring `Λ`, and a normalized canonical package `data`. Let `A,B,C,D` be separated
finite-type `k`-schemes in a commuting square with proper vertical maps and quasi-compact open
horizontal maps. For maps `delta_v` and `delta_i` satisfying the displayed open-unit
normalization equations, the two canonical composites agree.

Proof (steps 1--7 from the blueprint proof):
1. Set `H = R_r M`, `X = P_i N`, `Y = P_p N`, `K = M ⊗ P_r X`, and `F = J_v M`; use the
   canonical pullback compositor to identify `P_r X` with `P_v Y`.
2. Precompose both arrows with the inverse of the normalized `delta_i`, then use the
   `J_i ⊣ P_i` adjunct bijection, the canonical proper/open mate, and the `P_r ⊣ R_r`
   transpose; every operation is injective on the relevant hom-set.
3. The defining counit-transpose equation for the canonical projection map `pi_p` identifies
   the transpose of the left projection factor with the tensor of the proper counit and the
   identity.
4. The two open-unit normalization equations move the open units through `delta_i` and
   `delta_v`; naturality of the canonical mate moves the remaining comparison through it.
5. The mate normalization and proper counit naturality reduce the left transpose to
   `u_v (epsilon_r ⊗ 1)`.
6. Cancelling `delta_i` on the right and applying the defining transpose equation for `pi_r`
   gives the same `u_v (epsilon_r ⊗ 1)` for the right-hand arrow.
7. The transpose bijections are injective, so the displayed composites are equal; all maps
   are natural in the two unbounded derived inputs and no Tor-amplitude or boundedness
   hypothesis is used.

Source: blueprint proof cited above; finite analogues are Stacks Tags 0F7B, 0B56 and 0GL1.
(blueprint: lem-sf-condensed-proper-open-tensor-mate) -/
theorem condensedProperOpenTensorMate
    (ell : ℕ) [Fact ell.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsAdmissibleCoefficient Λ)
    {A B C D : Scheme.{u}}
    (aA : A ⟶ Spec (.of k)) (aB : B ⟶ Spec (.of k))
    (aC : C ⟶ Spec (.of k)) (aD : D ⟶ Spec (.of k))
    [LocallyOfFiniteType aA] [QuasiCompact aA] [IsSeparated aA]
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB]
    [LocallyOfFiniteType aC] [QuasiCompact aC] [IsSeparated aC]
    [LocallyOfFiniteType aD] [QuasiCompact aD] [IsSeparated aD]
    {v : A ⟶ B} {r : A ⟶ C} {p : B ⟶ D} {i : C ⟶ D}
    [IsOpenImmersion v] [IsOpenImmersion i]
    [QuasiCompact v] [QuasiCompact i] [IsProper p] [IsProper r]
    (_sq : CommSq v r p i)
    (data : CondensedOpenProper.Pasting Λ)
    (delta_v : ∀ (M : CondensedOpenProper.D Λ A) (N : CondensedOpenProper.D Λ D),
      ((derivedTensor Λ B).obj ((CondensedOpenProper.J Λ v).obj M)).obj
        ((CondensedOpenProper.P Λ p).obj N) ⟶
        (CondensedOpenProper.J Λ v).obj (((derivedTensor Λ A).obj M).obj
          ((CondensedOpenProper.P Λ v).obj ((CondensedOpenProper.P Λ p).obj N))))
    (delta_i : ∀ (M : CondensedOpenProper.D Λ A) (N : CondensedOpenProper.D Λ D),
      ((derivedTensor Λ D).obj ((CondensedOpenProper.J Λ i).obj
        ((CondensedOpenProper.R Λ r).obj M))).obj N ⟶
        (CondensedOpenProper.J Λ i).obj (((derivedTensor Λ C).obj
          ((CondensedOpenProper.R Λ r).obj M)).obj
            ((CondensedOpenProper.P Λ i).obj N)))
    (hdelta_v : ∀ (M : CondensedOpenProper.D Λ A) (N : CondensedOpenProper.D Λ D),
      openTensorUnitNormalization Λ v M ((CondensedOpenProper.P Λ p).obj N)
        (delta_v M N))
    (hdelta_i : ∀ (M : CondensedOpenProper.D Λ A) (N : CondensedOpenProper.D Λ D),
      openTensorUnitNormalization Λ i ((CondensedOpenProper.R Λ r).obj M) N
        (delta_i M N))
    (M : CondensedOpenProper.D Λ A) (N : CondensedOpenProper.D Λ D) :
    ((derivedTensor Λ D).map ((CondensedOpenProper.gamma Λ data.units _sq).app M)).app N ≫
        canonicalModuleObjectProjectionMap Λ p ((CondensedOpenProper.J Λ v).obj M) N ≫
        (CondensedOpenProper.R Λ p).map (delta_v M N) =
      delta_i M N ≫
        (CondensedOpenProper.J Λ i).map
          (canonicalModuleObjectProjectionMap Λ r M
            ((CondensedOpenProper.P Λ i).obj N)) ≫
        (CondensedOpenProper.gamma Λ data.units _sq).app
          (((derivedTensor Λ A).obj M).obj
            ((CondensedOpenProper.P Λ r).obj ((CondensedOpenProper.P Λ i).obj N))) ≫
        (CondensedOpenProper.J Λ v ⋙ CondensedOpenProper.R Λ p).map
          (canonicalTensorPullbackComparison Λ _sq M N) := by
  let Pr := CondensedOpenProper.P Λ r
  let Rr := CondensedOpenProper.R Λ r
  let Pp := CondensedOpenProper.P Λ p
  let Rp := CondensedOpenProper.R Λ p
  let Pi := CondensedOpenProper.P Λ i
  let Pv := CondensedOpenProper.P Λ v
  let Ji := CondensedOpenProper.J Λ i
  let Jv := CondensedOpenProper.J Λ v
  let ai := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i
  let av := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ v
  let ar := (upperStarLowerStarAdjunction Λ r).mapDerivedCategoryRightDerivedAdjunction
  let ap := (upperStarLowerStarAdjunction Λ p).mapDerivedCategoryRightDerivedAdjunction
  let theta := derivedOpenCoherencePullbackSquare Λ _sq
  let beta := derivedDirectImageOpenRestriction Λ _sq
  let gamma := CondensedOpenProper.gamma Λ data.units _sq
  let piR := fun K L ↦ ((ar.rightAdjointProjectionMap
    (Functor.OplaxMonoidal.δNatTrans Pr)).app K).app L
  let piP := fun K L ↦ ((ap.rightAdjointProjectionMap
    (Functor.OplaxMonoidal.δNatTrans Pp)).app K).app L
  have htheta : ∀ K L : CondensedOpenProper.D Λ D,
      Pr.map (Functor.OplaxMonoidal.δ Pi K L) ≫
          Functor.OplaxMonoidal.δ Pr (Pi.obj K) (Pi.obj L) ≫
          (theta.hom.app K ⊗ₘ theta.hom.app L) =
        theta.hom.app (K ⊗ L) ≫ Pv.map (Functor.OplaxMonoidal.δ Pp K L) ≫
          Functor.OplaxMonoidal.δ Pv (Pp.obj K) (Pp.obj L) := by
    intro K L
    have := exactSquare_monoidal Λ _sq
    simpa only [Functor.OplaxMonoidal.comp_δ, Category.assoc] using
      oplax_of_monoidal theta.hom K L
  have hnat : (Rr.map (av.unit.app M) ⊗ₘ 𝟙 (Pi.obj N)) ≫
      piR (Pv.obj (Jv.obj M)) (Pi.obj N) =
      piR M (Pi.obj N) ≫ Rr.map (av.unit.app M ⊗ₘ 𝟙 (Pr.obj (Pi.obj N))) := by
    have h := congr_app ((ar.rightAdjointProjectionMap
        (Functor.OplaxMonoidal.δNatTrans Pr)).naturality (av.unit.app M)) (Pi.obj N)
    change Rr.map (av.unit.app M) ▷ Pi.obj N ≫ _ =
      _ ≫ Rr.map (av.unit.app M ▷ Pr.obj (Pi.obj N)) at h
    simpa only [MonoidalCategory.tensorHom_id, piR, Pr, Rr, Pv, Jv, Functor.comp_obj,
      Functor.id_obj] using h
  have hdv := hdelta_v M N
  have hdi := hdelta_i M N
  simp only [openTensorUnitNormalization, exactPull_mu, derivedTensor,
    curriedTensor_map_app, ← MonoidalCategory.tensorHom_id] at hdv hdi
  have hui : IsIso ai.unit := by
    change IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i).unit
    rw [← data.units.normalized]
    infer_instance
  let fi := ai.fullyFaithfulLOfIsIsoUnit
  letI : Ji.Full := fi.full
  letI : Ji.Faithful := fi.faithful
  have hc : IsIso (ai.counit.app (Ji.obj (Rr.obj M) ⊗ N)) :=
    (ai.isIso_counit_app_iff_mem_essImage).2
      (tensorObj_mem_essImage_mapDerivedCategory_openImmersionLowerShriek Λ i
        (Rr.obj M) N)
  have hb := restriction_beta_isIso Λ _sq data (M ⊗ Pv.obj (Pp.obj N))
  have hu : IsIso (ai.unit.app (Rr.obj M)) := by
    rw [← data.units.normalized]
    infer_instance
  have h := normalized_tensor_square Pr Rr Pp Rp Pi Pv Ji Jv ai av.unit theta
    beta gamma piR piP (gamma_normalization Λ _sq data) M N
    (delta_v M N) (delta_i M N) hdv hdi hnat
    (projection_exchange Pr Rr Pp Rp Pi Pv ar ap theta htheta (Jv.obj M) N)
  rw [canonicalProjection_eq, canonicalProjection_eq]
  simpa only [piR, piP, Pr, Rr, Pp, Rp, Pi, Pv, Ji, Jv, ar, ap, theta, gamma,
    derivedTensor, curriedTensor_obj_obj,
    curriedTensor_map_app, canonicalTensorPullbackComparison,
    exactSquare_component, curriedTensor_obj_map, MonoidalCategory.tensorHom_id,
      MonoidalCategory.id_tensorHom] using h

end AlgebraicGeometry.ProEtale.CondensedRing
