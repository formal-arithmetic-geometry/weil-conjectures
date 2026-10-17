/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyFilteredColimit
public import WeilConjectures.AlgebraicGeometry.Sites.SectionContinuity
public import WeilConjectures.AlgebraicGeometry.Sites.UnitComparison

/-!
# Sections of the colimit of a system of étale sheaves along an inverse limit

Let `D : Iᵒᵖ ⥤ Scheme` be a directed inverse system of quasi-compact quasi-separated schemes with
affine transition maps and limit `X`, and let `(Fᵢ, φ)` be a *system* of abelian étale sheaves:
a sheaf `Fᵢ` on every `Dᵢ` with transition maps `φ : (Dᵢ ⟶ Dⱼ)^* Fᵢ ⟶ Fⱼ` (not necessarily
isomorphisms). Let `L` be the colimit on `X` of the pullbacks of the `Fᵢ`.

Fix a stage `i₀` and a quasi-compact quasi-separated étale `D_{i₀}`-scheme `U`. We show that the
sections of `L` over `U ×_{D_{i₀}} X` are the filtered colimit of the sections of the `Fⱼ` over
the `U ×_{D_{i₀}} Dⱼ` (`AlgebraicGeometry.Etale.SystemData.exists_stageSection_eq`,
`AlgebraicGeometry.Etale.SystemData.exists_transition_eq_zero`). All the sheaves are pushed
forward to the small étale site of `D_{i₀}`, so that the comparison maps are morphisms of sheaves
on a fixed site.

The proof combines the continuity of sections of a single sheaf
(`AlgebraicGeometry.Etale.unitComparison_app_isColimit_of_isLimit`) with the commutation of
sections over quasi-compact quasi-separated objects with filtered colimits
(`AlgebraicGeometry.Scheme.exists_app_eq_of_isColimit_ab`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale


section KeyIdentity

variable {X Dj Di D₀ : Scheme.{u}} (πj : X ⟶ Dj) (Dij : Dj ⟶ Di) (gi : Di ⟶ D₀)
  (πi : X ⟶ Di) (gj : Dj ⟶ D₀) (p : X ⟶ D₀) (h₁ : πi = πj ≫ Dij) (h₂ : gj = Dij ≫ gi)
  (h₃ : p = πi ≫ gi) (h₄ : p = πj ≫ gj)

/-- The comparison of units underlying the sections of a system along an inverse limit: for
`πi = πj ≫ Dij`, `gj = Dij ≫ gi` and `p = πi ≫ gi = πj ≫ gj`, the unit of `πj` on
`Dij^* Fᵢ`, pushed forward to `D₀`, is the pushforward of `unitComparison` followed by the
composition isomorphism `πi^* ≅ πj^* Dij^*`. -/
lemma lowerStarComp_hom_app_unit_eq_unitComparison
    (Fi : Sheaf Di.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (lowerStarComp AddCommGrpCat.{u + 1} Dij gi gj h₂).hom.app
        ((upperStar AddCommGrpCat.{u + 1} Dij).obj Fi) ≫
      (lowerStar AddCommGrpCat.{u + 1} gj).map
        ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} πj).unit.app
          ((upperStar AddCommGrpCat.{u + 1} Dij).obj Fi)) ≫
      (lowerStarComp AddCommGrpCat.{u + 1} πj gj p h₄).hom.app _ =
    (lowerStar AddCommGrpCat.{u + 1} gi).map (unitComparison πj Dij πi h₁ Fi) ≫
      (lowerStarComp AddCommGrpCat.{u + 1} πi gi p h₃).hom.app _ ≫
      (lowerStar AddCommGrpCat.{u + 1} p).map
        ((upperStarComp AddCommGrpCat.{u + 1} πj Dij πi h₁).hom.app Fi) := by
  have hassoc := NatTrans.congr_app (lowerStarComp_assoc' AddCommGrpCat.{u + 1} πj Dij gi πi gj
    p h₁ h₂ h₃) ((upperStar AddCommGrpCat.{u + 1} πj).obj
      ((upperStar AddCommGrpCat.{u + 1} Dij).obj Fi))
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hassoc
  have hnat := (lowerStarComp AddCommGrpCat.{u + 1} πi gi p h₃).hom.naturality
    ((upperStarComp AddCommGrpCat.{u + 1} πj Dij πi h₁).inv.app Fi)
  simp only [Functor.comp_map] at hnat
  rw [unitComparison, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    reassoc_of% hnat, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id]
  rw [Category.comp_id, hassoc]
  have hnat' := (lowerStarComp AddCommGrpCat.{u + 1} Dij gi gj h₂).hom.naturality
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} πj).unit.app
      ((upperStar AddCommGrpCat.{u + 1} Dij).obj Fi))
  simp only [Functor.comp_map] at hnat'
  rw [← reassoc_of% hnat']

end KeyIdentity

/-- A *system* of abelian étale sheaves over a directed inverse system of schemes `D` with a
cone `c`, together with the colimit on `c.pt` of the pullbacks of its members: the data of
`AlgebraicGeometry.Etale.EtaleCohomologyStageContinuity` (without the coherence laws of the
transition maps, which are not needed here). -/
structure SystemData {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) where
  /-- The sheaf at the stage `Dᵢ`. -/
  F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1}
  /-- The transition maps. -/
  φ : ∀ {i j : I} (f : i ⟶ j),
    (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j
  /-- The pullbacks of the `Fᵢ` to the cone point, as a functor. -/
  G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}
  /-- The identification of `G i` with the pullback of `Fᵢ`. -/
  eG : ∀ i : I, G.obj i ≅ (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i)
  hG : ∀ (i j : I) (f : i ⟶ j), G.map f =
    (eG i).hom ≫
      (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
        (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫ (eG j).inv
  /-- The colimit cocone on the cone point. -/
  L : Cocone G
  /-- `L` is a colimit. -/
  hL : IsColimit L

namespace SystemData

variable {I : Type u} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}} {c : Cone D} (S : SystemData D c)

/-- The sheaf `Fⱼ`, pushed forward to the stage `D_{i₀}`. -/
noncomputable abbrev stageSheaf {i₀ j : I} (f : i₀ ⟶ j) :
    Sheaf (D.obj (op i₀)).smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (lowerStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (S.F j)

/-- The comparison `(gᵢ)_* (πᵢ)_* πᵢ^* Fᵢ ⟶ (π_{i₀})_* G i`. -/
noncomputable def limitComparison {i₀ i : I} (f : i₀ ⟶ i) :
    (lowerStar AddCommGrpCat.{u + 1} (D.map f.op)).obj
        ((lowerStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj
          ((upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (S.F i))) ⟶
      (lowerStar AddCommGrpCat.{u + 1} (c.π.app (op i₀))).obj (S.G.obj i) :=
  (lowerStarComp AddCommGrpCat.{u + 1} (c.π.app (op i)) (D.map f.op)
      (c.π.app (op i₀)) (c.w _).symm).hom.app _ ≫
    (lowerStar AddCommGrpCat.{u + 1} (c.π.app (op i₀))).map (S.eG i).inv

instance {i₀ i : I} (f : i₀ ⟶ i) : IsIso (S.limitComparison f) := by
  dsimp only [limitComparison]; infer_instance

/-- The map from the sections of `Fⱼ` over `U ×_{D_{i₀}} Dⱼ` to the sections of `L` over
`U ×_{D_{i₀}} X`, as a morphism of sheaves on `D_{i₀}`. -/
noncomputable def stageMap {i₀ j : I} (f : i₀ ⟶ j) :
    S.stageSheaf f ⟶ (lowerStar AddCommGrpCat.{u + 1} (c.π.app (op i₀))).obj S.L.pt :=
  (lowerStar AddCommGrpCat.{u + 1} (D.map f.op)).map
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (c.π.app (op j))).unit.app (S.F j)) ≫
    S.limitComparison f ≫ (lowerStar AddCommGrpCat.{u + 1} (c.π.app (op i₀))).map (S.L.ι.app j)

/-- The transition `(gᵢ)_* (Dᵢⱼ)_* Dᵢⱼ^* Fᵢ ⟶ (gⱼ)_* Fⱼ` induced by `φ`. -/
noncomputable def pushTransition {i₀ i j : I} (f : i₀ ⟶ i) (g : i ⟶ j) :
    (lowerStar AddCommGrpCat.{u + 1} (D.map f.op)).obj
        ((lowerStar AddCommGrpCat.{u + 1} (D.map g.op)).obj
          ((upperStar AddCommGrpCat.{u + 1} (D.map g.op)).obj (S.F i))) ⟶
      S.stageSheaf (f ≫ g) :=
  (lowerStar AddCommGrpCat.{u + 1} (D.map f.op)).map
      ((lowerStar AddCommGrpCat.{u + 1} (D.map g.op)).map (S.φ g)) ≫
    (lowerStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
      (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (S.F j)

/-- The basic compatibility of `pushTransition` with the comparison maps. -/
lemma pushTransition_unit_limitComparison {i₀ i j : I} (f : i₀ ⟶ i) (g : i ⟶ j) :
    S.pushTransition f g ≫
        (lowerStar AddCommGrpCat.{u + 1} (D.map (f ≫ g).op)).map
          ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (c.π.app (op j))).unit.app
            (S.F j)) ≫ S.limitComparison (f ≫ g) =
      (lowerStar AddCommGrpCat.{u + 1} (D.map f.op)).map
          (unitComparison (c.π.app (op j)) (D.map g.op) (c.π.app (op i))
            (c.w _).symm (S.F i)) ≫
        S.limitComparison f ≫
          (lowerStar AddCommGrpCat.{u + 1} (c.π.app (op i₀))).map (S.G.map g) := by
  have hk := lowerStarComp_hom_app_unit_eq_unitComparison (c.π.app (op j))
    (D.map g.op) (D.map f.op) (c.π.app (op i))
    (D.map (f ≫ g).op) (c.π.app (op i₀)) (c.w _).symm
    (D.map_comp g.op f.op) (c.w _).symm (c.w _).symm (S.F i)
  have h₁ := (lowerStarComp AddCommGrpCat.{u + 1} (D.map g.op)
    (D.map f.op) (D.map (f ≫ g).op)
    (D.map_comp g.op f.op)).hom.naturality (S.φ g)
  have h₂ := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (c.π.app (op j))).unit.naturality
    (S.φ g)
  have h₃ := (lowerStarComp AddCommGrpCat.{u + 1} (c.π.app (op j))
    (D.map (f ≫ g).op) (c.π.app (op i₀)) (c.w _).symm).hom.naturality
    ((upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (S.φ g))
  simp only [Functor.comp_map, Functor.id_map] at h₁ h₂ h₃
  simp only [pushTransition, limitComparison, S.hG, Category.assoc, Functor.map_comp,
    Iso.map_inv_hom_id_assoc]
  rw [← reassoc_of% hk, reassoc_of% h₁, ← Functor.map_comp_assoc, h₂, Functor.map_comp,
    Category.assoc, reassoc_of% h₃]

end SystemData

section SmallIndex

variable {X : Scheme.{u}} {K : Type u} [SmallCategory K] [IsFiltered K]
  {F : K ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {c : Cocone F}

/-- `AlgebraicGeometry.Scheme.exists_app_eq_of_isColimit_ab` for a filtered category in
`Type u`. -/
lemma exists_app_eq_of_isColimit_ab_small (hc : IsColimit c) {W : X.Etale}
    [CompactSpace W.left] [QuasiSeparatedSpace W.left] (s : c.pt.obj.obj (op W)) :
    ∃ (k : K) (t : (F.obj k).obj.obj (op W)), (c.ι.app k).hom.app (op W) t = s := by
  have : IsFiltered (AsSmall.{u + 1} K) := IsFiltered.of_equivalence AsSmall.equiv
  obtain ⟨k, t, ht⟩ := Scheme.exists_app_eq_of_isColimit_ab
    (hc.whiskerEquivalence (AsSmall.equiv.{u, u, u + 1} (C := K)).symm) s
  exact ⟨AsSmall.down.obj k, t, ht⟩

/-- `AlgebraicGeometry.Scheme.exists_map_eq_zero_of_isColimit_ab` for a filtered category in
`Type u`. -/
lemma exists_map_eq_zero_of_isColimit_ab_small (hc : IsColimit c) {W : X.Etale}
    [CompactSpace W.left] {k : K} (t : (F.obj k).obj.obj (op W))
    (h : (c.ι.app k).hom.app (op W) t = 0) :
    ∃ (k' : K) (a : k ⟶ k'), (F.map a).hom.app (op W) t = 0 := by
  have : IsFiltered (AsSmall.{u + 1} K) := IsFiltered.of_equivalence AsSmall.equiv
  obtain ⟨k', a, ha⟩ := Scheme.exists_map_eq_zero_of_isColimit_ab
    (hc.whiskerEquivalence (AsSmall.equiv.{u, u, u + 1} (C := K)).symm)
    (k := AsSmall.up.obj k) t h
  exact ⟨AsSmall.down.obj k', AsSmall.down.map a, ha⟩

end SmallIndex

namespace SystemData

variable {I : Type u} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}} {c : Cone D} (S : SystemData D c)

/-- `pushTransition` followed by the stage map is the unit comparison followed by the leg of the
colimit. -/
lemma pushTransition_stageMap {i₀ i j : I} (f : i₀ ⟶ i) (g : i ⟶ j) :
    S.pushTransition f g ≫ S.stageMap (f ≫ g) =
      (lowerStar AddCommGrpCat.{u + 1} (D.map f.op)).map
          (unitComparison (c.π.app (op j)) (D.map g.op) (c.π.app (op i))
            (c.w _).symm (S.F i)) ≫
        S.limitComparison f ≫
          (lowerStar AddCommGrpCat.{u + 1} (c.π.app (op i₀))).map (S.L.ι.app i) := by
  rw [stageMap, reassoc_of% S.pushTransition_unit_limitComparison f g, ← Functor.map_comp,
    S.L.w]

/-- The transition `(gⱼ)_* Fⱼ ⟶ (gₖ)_* Fₖ` of the stage sheaves along `a : j ⟶ k`. -/
noncomputable def stageTransition {i₀ j k : I} (f : i₀ ⟶ j) (a : j ⟶ k) :
    S.stageSheaf f ⟶ S.stageSheaf (f ≫ a) :=
  (lowerStar AddCommGrpCat.{u + 1} (D.map f.op)).map
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (D.map a.op)).unit.app (S.F j)) ≫
    S.pushTransition f a

lemma stageTransition_unit_limitComparison {i₀ j k : I} (f : i₀ ⟶ j) (a : j ⟶ k) :
    S.stageTransition f a ≫
        (lowerStar AddCommGrpCat.{u + 1} (D.map (f ≫ a).op)).map
          ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (c.π.app (op k))).unit.app
            (S.F k)) ≫ S.limitComparison (f ≫ a) =
      (lowerStar AddCommGrpCat.{u + 1} (D.map f.op)).map
          ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (c.π.app (op j))).unit.app
            (S.F j)) ≫ S.limitComparison f ≫
          (lowerStar AddCommGrpCat.{u + 1} (c.π.app (op i₀))).map (S.G.map a) := by
  rw [stageTransition, Category.assoc, S.pushTransition_unit_limitComparison f a,
    ← Functor.map_comp_assoc, unit_app_comp_unitComparison]

lemma stageTransition_stageMap {i₀ j k : I} (f : i₀ ⟶ j) (a : j ⟶ k) :
    S.stageTransition f a ≫ S.stageMap (f ≫ a) = S.stageMap f := by
  rw [stageMap, reassoc_of% S.stageTransition_unit_limitComparison f a, stageMap,
    ← Functor.map_comp, S.L.w]

end SystemData

section Tail

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
  {D : Iᵒᵖ ⥤ Scheme.{u}} {c : Cone D} (hc : IsLimit c)
  [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
  [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]

include hc in
/-- Continuity of sections of the pullbacks of a sheaf `M` on a stage `Dᵢ`, surjectivity: a
section of `πᵢ^* M` over `W ×_{Dᵢ} X` comes from a section of `(Dᵢ ⟵ Dⱼ)^* M` over
`W ×_{Dᵢ} Dⱼ`. -/
lemma exists_unitComparison_app_eq_of_isLimit (i : I) (M : Sheaf (D.obj (op i)).smallEtaleTopology
      AddCommGrpCat.{u + 1}) (W : (D.obj (op i)).Etale) [CompactSpace W.left]
    [QuasiSeparatedSpace W.left]
    (t : ((lowerStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj
      ((upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj M)).obj.obj (op W)) :
    ∃ (j : I) (g : i ⟶ j) (s : ((lowerStar AddCommGrpCat.{u + 1} (D.map g.op)).obj
        ((upperStar AddCommGrpCat.{u + 1} (D.map g.op)).obj M)).obj.obj (op W)),
      (unitComparison (c.π.app (op j)) (D.map g.op) (c.π.app (op i)) (c.w _).symm M).hom.app
        (op W) s = t := by
  let π' : Over.forget (op i) ⋙ D ⟶ (Functor.const _).obj (D.obj (op i)) :=
    { app m := D.map m.hom
      naturality _ _ f := by simp [← D.map_comp, Over.w f] }
  have hc' := (Functor.Initial.isLimitWhiskerEquiv (Over.forget (op i)) c).symm hc
  have (m : Over (op i)) : CompactSpace ((Over.forget (op i) ⋙ D).obj m) :=
    inferInstanceAs (CompactSpace (D.obj m.left))
  have (m : Over (op i)) : QuasiSeparatedSpace ((Over.forget (op i) ⋙ D).obj m) :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj m.left))
  have {m m' : Over (op i)} (f : m ⟶ m') : IsAffineHom ((Over.forget (op i) ⋙ D).map f) :=
    inferInstanceAs (IsAffineHom (D.map f.left))
  obtain ⟨m, s, hs⟩ := (unitComparison_app_isColimit_of_isLimit (Over.forget (op i) ⋙ D) π'
    (c.whisker (Over.forget (op i))) (c.π.app (op i)) (fun m ↦ by rw [← c.w m.hom]; rfl) hc' M W).1 t
  exact ⟨m.left.unop, m.hom.unop, s, hs⟩

include hc in
/-- Continuity of sections of the pullbacks of a sheaf `M` on a stage `Dᵢ`, injectivity: a
section of `M` over `W` whose pullback to `W ×_{Dᵢ} X` vanishes has vanishing pullback to some
`W ×_{Dᵢ} Dⱼ`. -/
lemma exists_unit_app_eq_zero_of_isLimit (i : I) (M : Sheaf (D.obj (op i)).smallEtaleTopology
      AddCommGrpCat.{u + 1}) (W : (D.obj (op i)).Etale) [CompactSpace W.left]
    [QuasiSeparatedSpace W.left] (x : M.obj.obj (op W))
    (hx : ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (c.π.app (op i))).unit.app
      M).hom.app (op W) x = 0) :
    ∃ (j : I) (g : i ⟶ j), ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
      (D.map g.op)).unit.app M).hom.app (op W) x = 0 := by
  let π' : Over.forget (op i) ⋙ D ⟶ (Functor.const _).obj (D.obj (op i)) :=
    { app m := D.map m.hom
      naturality _ _ f := by simp [← D.map_comp, Over.w f] }
  have hc' := (Functor.Initial.isLimitWhiskerEquiv (Over.forget (op i)) c).symm hc
  have (m : Over (op i)) : CompactSpace ((Over.forget (op i) ⋙ D).obj m) :=
    inferInstanceAs (CompactSpace (D.obj m.left))
  have (m : Over (op i)) : QuasiSeparatedSpace ((Over.forget (op i) ⋙ D).obj m) :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj m.left))
  have {m m' : Over (op i)} (f : m ⟶ m') : IsAffineHom ((Over.forget (op i) ⋙ D).map f) :=
    inferInstanceAs (IsAffineHom (D.map f.left))
  let m₀ : Over (op i) := Over.mk (𝟙 (op i))
  have h₀ := congrArg (fun φ ↦ φ.hom.app (op W) x) (unit_app_comp_unitComparison
    (c.π.app (op i)) (π'.app m₀) (c.π.app (op i)) (by simp [π', m₀]) M)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ConcreteCategory.comp_apply] at h₀
  obtain ⟨m, f, hf⟩ := (unitComparison_app_isColimit_of_isLimit (Over.forget (op i) ⋙ D) π'
    (c.whisker (Over.forget (op i))) (c.π.app (op i)) (fun m ↦ by rw [← c.w m.hom]; rfl) hc' M W).2 m₀
    (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (π'.app m₀)).unit.app M).hom.app
      (op W) x) (h₀.trans hx)
  have h₁ := congrArg (fun φ ↦ φ.hom.app (op W) x) (unit_app_comp_unitComparison
    ((Over.forget (op i) ⋙ D).map f) (π'.app m₀) (π'.app m) (by simp [π', m₀]) M)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ConcreteCategory.comp_apply] at h₁
  exact ⟨m.left.unop, m.hom.unop, h₁.symm.trans hf⟩

end Tail

section Sections

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
  {D : Iᵒᵖ ⥤ Scheme.{u}} {c : Cone D} (hc : IsLimit c)
  [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
  [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]

omit [IsDirected I (· ≤ ·)] [Nonempty I] [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
  [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)] in
/-- The base change of a quasi-compact quasi-separated étale scheme along an affine morphism has
quasi-compact quasi-separated underlying scheme. -/
lemma compactSpace_and_quasiSeparatedSpace_pullback_left {Y Z : Scheme.{u}} (q : Y ⟶ Z)
    [IsAffineHom q] (U : Z.Etale) [CompactSpace U.left] [QuasiSeparatedSpace U.left] :
    CompactSpace ((MorphismProperty.Over.pullback @Etale ⊤ q).obj U).left ∧
      QuasiSeparatedSpace ((MorphismProperty.Over.pullback @Etale ⊤ q).obj U).left := by
  change CompactSpace ↥(pullback U.hom q) ∧ QuasiSeparatedSpace ↥(pullback U.hom q)
  exact ⟨inferInstance, quasiSeparatedSpace_of_quasiSeparated (pullback.fst U.hom q)⟩

namespace SystemData

variable (S : SystemData D c)

include hc in
/-- **Sections of the colimit of a system, surjectivity.** Every section of `L` over
`U ×_{D_{i₀}} X`, for `U` quasi-compact quasi-separated étale over `D_{i₀}`, comes from a section
of some `Fⱼ` over `U ×_{D_{i₀}} Dⱼ`. -/
lemma exists_stageMap_app_eq {i₀ : I} (U : (D.obj (op i₀)).Etale) [CompactSpace U.left]
    [QuasiSeparatedSpace U.left]
    (s : ((lowerStar AddCommGrpCat.{u + 1} (c.π.app (op i₀))).obj S.L.pt).obj.obj (op U)) :
    ∃ (j : I) (f : i₀ ⟶ j) (t : (S.stageSheaf f).obj.obj (op U)),
      (S.stageMap f).hom.app (op U) t = s := by
  have := isAffineHom_π_app D c hc
  obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace_pullback_left (c.π.app (op i₀)) U
  obtain ⟨i, n₀, hn₀⟩ := exists_app_eq_of_isColimit_ab_small S.hL
    (W := (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj U) s
  obtain ⟨k, hk₀, hk⟩ := directed_of (· ≤ ·) i₀ i
  let f₀ : i₀ ⟶ k := homOfLE hk₀
  obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace_pullback_left (D.map f₀.op) U
  -- the section `s` comes from `(g_k)_* (π_k)_* π_k^* F_k`
  let n : ((lowerStar AddCommGrpCat.{u + 1} (D.map f₀.op)).obj
      ((lowerStar AddCommGrpCat.{u + 1} (c.π.app (op k))).obj
        ((upperStar AddCommGrpCat.{u + 1} (c.π.app (op k))).obj (S.F k)))).obj.obj (op U) :=
    (inv (S.limitComparison f₀)).hom.app (op U) ((S.G.map (homOfLE hk)).hom.app _ n₀)
  have hn : (S.limitComparison f₀ ≫ (lowerStar AddCommGrpCat.{u + 1} (c.π.app (op i₀))).map
      (S.L.ι.app k)).hom.app (op U) n = s := by
    rw [← hn₀, ← S.L.w (homOfLE hk)]
    simp only [n, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ConcreteCategory.comp_apply]
    rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom, IsIso.inv_hom_id]
    rfl
  obtain ⟨j, g, m, hm⟩ := exists_unitComparison_app_eq_of_isLimit hc k (S.F k)
    ((MorphismProperty.Over.pullback @Etale ⊤ (D.map f₀.op)).obj U) n
  refine ⟨j, f₀ ≫ g, (S.pushTransition f₀ g).hom.app (op U) m, ?_⟩
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom,
    S.pushTransition_stageMap, ← hn, ← hm]
  rfl

include hc in
/-- **Sections of the colimit of a system, injectivity.** A section `t` of `Fⱼ` over
`U ×_{D_{i₀}} Dⱼ` whose image in the sections of `L` over `U ×_{D_{i₀}} X` vanishes is killed by
a compatible transition to a later stage. -/
lemma exists_stageTransition_app_eq_zero {i₀ j : I} (U : (D.obj (op i₀)).Etale)
    [CompactSpace U.left] [QuasiSeparatedSpace U.left] (f : i₀ ⟶ j)
    (t : (S.stageSheaf f).obj.obj (op U)) (ht : (S.stageMap f).hom.app (op U) t = 0) :
    ∃ (l : I) (f' : i₀ ⟶ l) (ψ : S.stageSheaf f ⟶ S.stageSheaf f'),
      ψ ≫ S.stageMap f' = S.stageMap f ∧ ψ.hom.app (op U) t = 0 := by
  have := isAffineHom_π_app D c hc
  obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace_pullback_left (c.π.app (op i₀)) U
  let n₀ := (((lowerStar AddCommGrpCat.{u + 1} (D.map f.op)).map
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (c.π.app (op j))).unit.app
        (S.F j))) ≫ S.limitComparison f).hom.app (op U) t
  obtain ⟨k, a, ha⟩ := exists_map_eq_zero_of_isColimit_ab_small S.hL
    (W := (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj U) n₀ (by
      rw [← ht, stageMap]; rfl)
  let x := (S.stageTransition f a).hom.app (op U) t
  have hx : ((lowerStar AddCommGrpCat.{u + 1} (D.map (f ≫ a).op)).map
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (c.π.app (op k))).unit.app
        (S.F k))).hom.app (op U) x = 0 := by
    have h := congrArg (fun φ ↦ φ.hom.app (op U) t) (S.stageTransition_unit_limitComparison f a)
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ConcreteCategory.comp_apply] at h
    have h' : ((S.limitComparison (f ≫ a)).hom.app (op U))
        (((lowerStar AddCommGrpCat.{u + 1} (D.map (f ≫ a).op)).map
          ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (c.π.app (op k))).unit.app
            (S.F k))).hom.app (op U) x) = 0 := by
      rw [h]
      exact ha
    have h'' := congrArg ((inv (S.limitComparison (f ≫ a))).hom.app (op U)) h'
    rw [map_zero, ← ConcreteCategory.comp_apply, ← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom,
      IsIso.hom_inv_id] at h''
    exact h''
  obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace_pullback_left (D.map (f ≫ a).op) U
  obtain ⟨l, b, hb⟩ := exists_unit_app_eq_zero_of_isLimit hc k (S.F k)
    ((MorphismProperty.Over.pullback @Etale ⊤ (D.map (f ≫ a).op)).obj U) x hx
  refine ⟨l, (f ≫ a) ≫ b, S.stageTransition f a ≫ S.stageTransition (f ≫ a) b, ?_, ?_⟩
  · rw [Category.assoc, S.stageTransition_stageMap, S.stageTransition_stageMap]
  · change (S.pushTransition (f ≫ a) b).hom.app (op U)
      (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (D.map b.op)).unit.app
        (S.F k)).hom.app _ x) = 0
    rw [hb, map_zero]

end SystemData

end Sections

end AlgebraicGeometry.Etale
