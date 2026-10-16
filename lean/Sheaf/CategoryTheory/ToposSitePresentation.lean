/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Continuous
import Sheaf.CategoryTheory.SheafSubcategoryComparison
import Sheaf.CategoryTheory.ToposCompatibleGenerators
import Sheaf.CategoryTheory.SiteOfSheafGenerators
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Whiskering
/-!
# Presenting a geometric adjunction by finite-limit sites

Source: Stacks Project, Sites, Tags 03A1, 03CI, 03A2 and Remark 03CJ
(blueprint: lem-weil-pbc-topos-site-presentation).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

private def nerveHomEquiv
    {C D C' D' : Type u}
    [SmallCategory C] [SmallCategory D] [SmallCategory C'] [SmallCategory D']
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {L : Sheaf K (Type u) ⥤ Sheaf J (Type u)}
    {R : Sheaf J (Type u) ⥤ Sheaf K (Type u)} (adj : L ⊣ R)
    (G : C' ⥤ Sheaf J (Type u)) (E : D' ⥤ Sheaf K (Type u))
    (v : D' ⥤ C') (a : v ⋙ G ≅ E ⋙ L)
    (X : Sheaf J (Type u)) (T : D') :
    (E.obj T ⟶ R.obj X) ≃ (G.obj (v.obj T) ⟶ X) where
  toFun f := a.hom.app T ≫ (adj.homEquiv _ _).symm f
  invFun f := adj.homEquiv _ _ (a.inv.app T ≫ f)
  left_inv f := by simp [← Category.assoc]
  right_inv f := by simp [← Category.assoc]

private noncomputable def nerveAdjunctionIso
    {C D C' D' : Type u}
    [SmallCategory C] [SmallCategory D] [SmallCategory C'] [SmallCategory D']
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {L : Sheaf K (Type u) ⥤ Sheaf J (Type u)}
    {R : Sheaf J (Type u) ⥤ Sheaf K (Type u)} (adj : L ⊣ R)
    (G : C' ⥤ Sheaf J (Type u)) (E : D' ⥤ Sheaf K (Type u))
    (v : D' ⥤ C') (a : v ⋙ G ≅ E ⋙ L) :
    R ⋙ sheafSubcategoryNerve E ≅ sheafSubcategoryNerve G ⋙
      (Functor.whiskeringLeft _ _ (Type u)).obj v.op := by
  refine NatIso.ofComponents (fun X ↦ ?_) ?_
  · refine NatIso.ofComponents (fun T ↦ (nerveHomEquiv adj G E v a X T.unop).toIso) ?_
    intro T U f
    ext g
    change a.hom.app U.unop ≫ (adj.homEquiv _ _).symm (E.map f.unop ≫ g) =
      G.map (v.map f.unop) ≫ (a.hom.app T.unop ≫ (adj.homEquiv _ _).symm g)
    rw [adj.homEquiv_naturality_left_symm]
    simpa only [Functor.comp_map, Category.assoc] using
      congrArg (fun k ↦ k ≫ (adj.homEquiv (E.obj T.unop) X).symm
        (show E.obj T.unop ⟶ R.obj X from g)) (a.hom.naturality f.unop).symm
  · intro X Y f
    ext T g
    change a.hom.app T.unop ≫ (adj.homEquiv _ _).symm (g ≫ R.map f) =
      (a.hom.app T.unop ≫ (adj.homEquiv _ _).symm g) ≫ f
    rw [adj.homEquiv_naturality_right_symm, Category.assoc]

private theorem epi_map_of_adjunction
    {C D C' D' : Type u}
    [SmallCategory C] [SmallCategory D] [SmallCategory C'] [SmallCategory D']
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {L : Sheaf K (Type u) ⥤ Sheaf J (Type u)}
    {R : Sheaf J (Type u) ⥤ Sheaf K (Type u)} (adj : L ⊣ R)
    (G : C' ⥤ Sheaf J (Type u)) (E : D' ⥤ Sheaf K (Type u))
    (v : D' ⥤ C') (a : v ⋙ G ≅ E ⋙ L) (T : D') (S : PreZeroHypercover.{u} T)
    (hS : ⟨T, S⟩ ∈ sheafSubcategoryEpimorphicFamilies.{u, u, 0} E) :
    ⟨v.obj T, S.map v⟩ ∈ sheafSubcategoryEpimorphicFamilies.{u, u, 0} G := by
  intro B x y hxy
  apply (cancel_epi (a.inv.app T)).1
  apply (adj.homEquiv _ _).injective
  apply hS (R.obj B)
  intro i
  rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_left]
  congr 1
  change L.map (E.map (S.f i)) ≫ (a.inv.app T ≫ x) =
    L.map (E.map (S.f i)) ≫ (a.inv.app T ≫ y)
  have hn := a.inv.naturality (S.f i)
  simp only [Functor.comp_map] at hn
  rw [← Category.assoc, ← Category.assoc, hn]
  exact congrArg (fun k ↦ a.inv.app (S.X i) ≫ k) (hxy i)

/-- A left-exact geometric adjunction is presented by a continuous finite-limit site functor.

Source: Stacks Project, Sites, Tags 03A1, 03A2 and 03CI
(blueprint: lem-weil-pbc-topos-site-presentation).

Proof: Apply the compatible finite-limit generators and equip each full subcategory with
the epimorphic precoverage. The comparison equivalences identify their nerves with the
ambient sheaf categories. Joint epimorphy transports across the adjunction, giving
continuity; the natural Hom equivalence gives the direct-image comparison. -/
theorem topos_sitePresentation
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : Precoverage C) (K : Precoverage D)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [K.HasIsos] [K.IsStableUnderComposition] [K.IsStableUnderBaseChange] [K.HasPullbacks]
    (L : Sheaf K.toGrothendieck (Type u) ⥤ Sheaf J.toGrothendieck (Type u))
    (R : Sheaf J.toGrothendieck (Type u) ⥤ Sheaf K.toGrothendieck (Type u))
    (adj : L ⊣ R) [PreservesFiniteLimits L] :
    ∃ (C' D' : Type u) (_ : SmallCategory C') (_ : SmallCategory D')
      (J' : Precoverage C') (K' : Precoverage D')
      (_ : J'.HasIsos) (_ : J'.IsStableUnderComposition)
      (_ : J'.IsStableUnderBaseChange) (_ : J'.HasPullbacks)
      (_ : K'.HasIsos) (_ : K'.IsStableUnderComposition)
      (_ : K'.IsStableUnderBaseChange) (_ : K'.HasPullbacks)
      (_ : HasFiniteLimits C') (_ : HasFiniteLimits D')
      (g : Sheaf J.toGrothendieck (Type u) ≌ Sheaf J'.toGrothendieck (Type u))
      (e : Sheaf K.toGrothendieck (Type u) ≌ Sheaf K'.toGrothendieck (Type u))
      (v : D' ⥤ C') (_ : PreservesFiniteLimits v)
      (_ : v.IsContinuous K'.toGrothendieck J'.toGrothendieck),
      (∀ (T : D') (S : Presieve T), S ∈ K' T → S.map v ∈ J' (v.obj T)) ∧
      Nonempty (R ⋙ e.functor ≅ g.functor ⋙
        v.sheafPushforwardContinuous (Type u) K'.toGrothendieck J'.toGrothendieck) := by
  obtain ⟨C', D', hC', hD', hlimC', hlimD', G, E, v,
      hGfull, hGfaith, hGlim, hEfull, hEfaith, hElim, hvlim, ⟨a⟩, hrepC, hrepD⟩ :=
    topos_compatibleGenerators J.toGrothendieck K.toGrothendieck L
  obtain ⟨J', hJiso, hJcomp, hJbase, hJpb, g, ⟨ng⟩, hJepi⟩ :=
    siteOfSheafGenerators J G hrepC
  obtain ⟨K', hKiso, hKcomp, hKbase, hKpb, e, ⟨ne⟩, hKepi⟩ :=
    siteOfSheafGenerators K E hrepD
  have hcover : ∀ (T : D') (S : Presieve T), S ∈ K' T → S.map v ∈ J' (v.obj T) := by
    intro T S hS
    rw [← S.presieve₀_preZeroHypercover] at hS ⊢
    rw [← PreZeroHypercover.presieve₀_map, hJepi]
    exact epi_map_of_adjunction adj G E v a T S.preZeroHypercover ((hKepi _ _).1 hS)
  have : K'.PullbacksPreservedBy v := inferInstance
  let hv : v.IsContinuous K'.toGrothendieck J'.toGrothendieck :=
    v.isContinuous_toGrothendieck_of_pullbacksPreservedBy K' J' hcover
  let P := (Functor.whiskeringLeft _ _ (Type u)).obj v.op
  let θP : (R ⋙ e.functor) ⋙ sheafToPresheaf K'.toGrothendieck (Type u) ≅
      (g.functor ⋙ v.sheafPushforwardContinuous (Type u)
        K'.toGrothendieck J'.toGrothendieck) ⋙
          sheafToPresheaf K'.toGrothendieck (Type u) :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft R ne ≪≫
      nerveAdjunctionIso adj G E v a ≪≫ Functor.isoWhiskerRight ng.symm P ≪≫
        Functor.associator _ _ _
  exact ⟨C', D', hC', hD', J', K', hJiso, hJcomp, hJbase, hJpb,
    hKiso, hKcomp, hKbase, hKpb, hlimC', hlimD', g, e, v, hvlim, hv,
    hcover, ⟨Functor.fullyFaithfulCancelRight _ θP⟩⟩

end CategoryTheory
