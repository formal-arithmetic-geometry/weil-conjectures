/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q154
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.FineFanBlowup
public import Sheaf.AlgebraicGeometry.LogFanChartBlowup
public import Sheaf.AlgebraicGeometry.AffineFanHomUniversal
import Sheaf.AlgebraicGeometry.FineFanPointLocalization
import Sheaf.AlgebraicGeometry.StrictSharpSpaceSections
import Sheaf.AlgebraicGeometry.AffineOpenGermComparison

/-!
# Local comparison of fan charts under a strict log morphism

Source: ILO, Exposé VIII, proof of Theorem 3.3.15, printed p.109; affine fan
localizations in 3.1.2--3.1.10 (blueprint: lem-trf-strict-fan-chart-local-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- The canonical characteristic-sheaf map of a log morphism, presented by its section
maps and their normalization on every actual log section. The normalization uses all
relative Zariski opens, so it determines the map after quotienting units and sheafifying;
it does not permit an arbitrary morphism of sharp spaces.
Source: ILO VI 1.1--1.2, VIII proof of 3.3.15, p.109
(blueprint: lem-trf-strict-fan-chart-local-comparison). -/
structure EtaleLogHom.SharpSpaceMap {Y X : FineSaturatedLogScheme.{u}}
    (f : EtaleLogHom Y X) where
  sections : X.logStructure.sharpSpace.presheaf ⟶
    (Opens.map f.base.base).op ⋙ Y.logStructure.sharpSpace.presheaf
  onLogSections : ∀ (W : X.scheme.Opens) (V : Y.scheme.Opens)
    (k : V.toScheme ⟶ W.toScheme) (hk : k ≫ W.ι = V.ι ≫ f.base)
    (h : V ≤ f.base ⁻¹ᵁ W)
    (s : X.logStructure.monoidSheaf.obj.obj (op ((logOpenEtale X.scheme).obj W))),
    Y.logStructure.sharpSpace.presheaf.map (homOfLE h).op
        (sections.app (op W) (X.logStructure.sharpSection W s)) =
      Y.logStructure.sharpSection V
        (f.sectionMap ((logOpenEtale X.scheme).obj W)
          ((logOpenEtale Y.scheme).obj V) k hk s)

/-- Bundle the normalized section maps with the given underlying continuous map.
Source: ILO VI 1.1--1.2, VIII proof of 3.3.15, p.109
(blueprint: lem-trf-strict-fan-chart-local-comparison). -/
noncomputable def EtaleLogHom.SharpSpaceMap.map {Y X : FineSaturatedLogScheme.{u}}
    {f : EtaleLogHom Y X} (g : f.SharpSpaceMap) :
    Y.logStructure.sharpSpace ⟶ X.logStructure.sharpSpace :=
  InducedCategory.homMk { base := f.base.base, c := g.sections }

/-- The affine open of generalizations of a fan point, with coordinates its actual stalk.
The germ normalization fixes the coordinate isomorphism, including its section maps.
The fine monoid condition is a conclusion about the given fan stalk, not a hypothesis
on the fan. Source: ILO VIII 3.1.2--3.1.10, especially 3.1.10(ii), pp.98--99
(blueprint: lem-trf-strict-fan-chart-local-comparison). -/
structure FineFan.PointLocalization (F : FineFan.Fan.{u}) (z : F.space)
    extends FineFan.AffineOpen F.space (FineFan.stalk F.space.presheaf z) where
  mem : z ∈ openSet
  generalizations : ∀ t : F.space, t ∈ openSet ↔ t ⤳ z
  fine : FineFan.IsFine (FineFan.stalk F.space.presheaf z)
  normalization : ∀ p : FineFan.stalk F.space.presheaf z,
    FineFan.germ (F.space.restrict openSet.isOpenEmbedding).presheaf ⊤
        ⟨z, mem⟩ (by trivial) (FineFan.affinePullback iso.hom p) =
      FineFan.stalkMap (F.space.ofRestrict openSet.isOpenEmbedding) ⟨z, mem⟩ p

private theorem affine_stalk_sharp (P : Type u) [CommMonoid P]
    (hP : FineFan.IsFine P) :
    ∀ x : FineFan.affine P, FineFan.IsSharp
      (FineFan.stalk (FineFan.affine P).presheaf x) := by
  obtain ⟨_, e, _⟩ := FineFan.affineFan_localization_sections P hP
  intro x a ha
  apply (e x).injective
  rw [map_one]
  exact (Associates.isUnit_iff_eq_one _).mp (ha.map (e x).toMonoidHom)

private theorem stalkMap_germ {T R : SheafedSpace CommMonCat.{u}}
    (f : T ⟶ R) (U : Opens R) (x : T) (hx : f.hom.base x ∈ U) :
    FineFan.germ R.presheaf U (f.hom.base x) hx ≫ FineFan.stalkMap f x =
      f.hom.c.app (op U) ≫
        FineFan.germ T.presheaf ((Opens.map f.hom.base).obj U) x hx := by
  simp only [FineFan.stalkMap, FineFan.germ, FineFan.stalkDiagram,
    colimit.ι_map_assoc, OpenNhds.inclusionMapIso_inv, NatTrans.op_id]
  change f.hom.c.app (op U) ≫ T.presheaf.map (𝟙 _) ≫
    colimit.ι ((OpenNhds.map f.hom.base x ⋙ OpenNhds.inclusion x).op ⋙ T.presheaf)
      (op (⟨U, hx⟩ : OpenNhds (f.hom.base x))) ≫
    colimit.pre (FineFan.stalkDiagram T.presheaf x) (OpenNhds.map f.hom.base x).op = _
  rw [T.presheaf.map_id]
  erw [Category.id_comp]
  exact congrArg (fun k ↦ f.hom.c.app (op U) ≫ k)
    (colimit.ι_pre (FineFan.stalkDiagram T.presheaf x)
      (OpenNhds.map f.hom.base x).op (op (⟨U, hx⟩ : OpenNhds (f.hom.base x))))

private theorem stalkMap_id (T : SheafedSpace CommMonCat.{u}) (x : T) :
    FineFan.stalkMap (𝟙 T) x = 𝟙 _ := by
  apply colimit.hom_ext
  intro U
  induction U with | op U =>
    obtain ⟨U, hx⟩ := U
    change FineFan.germ T.presheaf U ((𝟙 T : T ⟶ T).hom.base x) hx ≫
      FineFan.stalkMap (𝟙 T) x = _
    rw [stalkMap_germ (𝟙 T) U x hx]
    simp [FineFan.germ]
    rfl

private theorem stalkMap_comp {T R S : SheafedSpace CommMonCat.{u}}
    (f : T ⟶ R) (g : R ⟶ S) (x : T) :
    FineFan.stalkMap (f ≫ g) x =
      FineFan.stalkMap g (f.hom.base x) ≫ FineFan.stalkMap f x := by
  apply colimit.hom_ext
  intro U
  induction U with | op U =>
    obtain ⟨U, hx⟩ := U
    let V := (Opens.map g.hom.base).obj U
    let W := (Opens.map f.hom.base).obj V
    calc
      _ = (g.hom.c.app (op U) ≫ f.hom.c.app (op V)) ≫
          FineFan.germ T.presheaf W x hx := stalkMap_germ (f ≫ g) U x hx
      _ = g.hom.c.app (op U) ≫ (f.hom.c.app (op V) ≫
          FineFan.germ T.presheaf W x hx) := Category.assoc _ _ _
      _ = g.hom.c.app (op U) ≫ (FineFan.germ R.presheaf V (f.hom.base x) hx ≫
          FineFan.stalkMap f x) :=
        congrArg (fun m ↦ g.hom.c.app (op U) ≫ m) (stalkMap_germ f V x hx).symm
      _ = (g.hom.c.app (op U) ≫ FineFan.germ R.presheaf V (f.hom.base x) hx) ≫
          FineFan.stalkMap f x := (Category.assoc _ _ _).symm
      _ = (FineFan.germ S.presheaf U (g.hom.base (f.hom.base x)) hx ≫
          FineFan.stalkMap g (f.hom.base x)) ≫ FineFan.stalkMap f x :=
        congrArg (fun m ↦ m ≫ FineFan.stalkMap f x)
          (stalkMap_germ g U (f.hom.base x) hx).symm
      _ = _ := Category.assoc _ _ _

private theorem local_id (T : SheafedSpace CommMonCat.{u}) :
    FineFan.IsLocalMorphism (𝟙 T) := by
  intro x
  rw [stalkMap_id]
  exact ⟨fun _ ha ↦ ha⟩

private theorem local_comp {T R S : SheafedSpace CommMonCat.{u}}
    (f : T ⟶ R) (g : R ⟶ S)
    (hf : FineFan.IsLocalMorphism f) (hg : FineFan.IsLocalMorphism g) :
    FineFan.IsLocalMorphism (f ≫ g) := by
  intro x
  rw [stalkMap_comp]
  have := hf x
  have := hg (f.hom.base x)
  exact MonoidHom.isLocalHom_comp _ _

private theorem affine_iso (P Q : Type u) [CommMonoid P] [CommMonoid Q]
    (hP : FineFan.IsFine P) (sP : FineFan.IsSharp P)
    (hQ : FineFan.IsFine Q) (sQ : FineFan.IsSharp Q) (α : P ≃* Q) :
    ∃ e : FineFan.affine Q ≅ FineFan.affine P,
      FineFan.IsLocalMorphism e.hom ∧
      FineFan.affinePullback e.hom = (FineFan.affineSection Q).comp α.toMonoidHom := by
  have hp := affine_stalk_sharp P hP
  have hq := affine_stalk_sharp Q hQ
  have uP := FineFan.affine_hom_universal P hP sP
  have uQ := FineFan.affine_hom_universal Q hQ sQ
  obtain ⟨g, hg, _⟩ := uP.2.2 Q hQ sQ α.toMonoidHom
  obtain ⟨k, hk, _⟩ := uQ.2.2 P hP sP α.symm.toMonoidHom
  have hgk : g.val ≫ k.val = 𝟙 (FineFan.affine Q) := by
    apply congrArg Subtype.val
      ((uQ.1 (FineFan.affine Q) hq).1 (a₁ :=
        ⟨g.val ≫ k.val, local_comp _ _ g.property k.property⟩)
        (a₂ := ⟨𝟙 _, local_id _⟩) ?_)
    change FineFan.affinePullback (g.val ≫ k.val) = FineFan.affinePullback (𝟙 _)
    rw [hk.2 (FineFan.affine Q) hq g, hg.1]
    ext q
    simp [FineFan.affinePullback]
  have hkg : k.val ≫ g.val = 𝟙 (FineFan.affine P) := by
    apply congrArg Subtype.val
      ((uP.1 (FineFan.affine P) hp).1 (a₁ :=
        ⟨k.val ≫ g.val, local_comp _ _ k.property g.property⟩)
        (a₂ := ⟨𝟙 _, local_id _⟩) ?_)
    change FineFan.affinePullback (k.val ≫ g.val) = FineFan.affinePullback (𝟙 _)
    rw [hg.2 (FineFan.affine P) hp k, hk.1]
    ext p
    simp [FineFan.affinePullback]
  exact ⟨⟨g.val, k.val, hgk, hkg⟩, g.property, hg.1⟩

private theorem affinePullback_comp {P : Type u} [CommMonoid P]
    {T R : SheafedSpace CommMonCat.{u}} (f : T ⟶ R) (g : R ⟶ FineFan.affine P) :
    FineFan.affinePullback (f ≫ g) =
      (SheafedSpace.Γ.map f.op).hom.comp (FineFan.affinePullback g) := by
  simp only [FineFan.affinePullback, op_comp, Functor.map_comp, CommMonCat.hom_comp,
    MonoidHom.comp_assoc]

private theorem local_of_bijective {T R : SheafedSpace CommMonCat.{u}}
    (f : T ⟶ R) (hf : ∀ x, Function.Bijective (FineFan.stalkMap f x)) :
    FineFan.IsLocalMorphism f := by
  intro x
  let e := MulEquiv.ofBijective (FineFan.stalkMap f x).hom (hf x)
  exact isLocalHom_of_leftInverse e.symm.toMonoidHom e.symm_apply_apply

private theorem sharp_of_equiv {P Q : Type u} [CommMonoid P] [CommMonoid Q]
    (e : P ≃* Q) (hP : FineFan.IsSharp P) : FineFan.IsSharp Q := by
  intro q hq
  apply e.symm.injective
  rw [map_one]
  exact hP _ (hq.map e.symm.toMonoidHom)

private theorem pointLocalization_exists (F : FineFan.Fan.{u}) (z : F.space) :
    Nonempty (FineFan.PointLocalization F z) := by
  obtain ⟨hf, _, U, hz, hgen, _, _, ι, hι, _⟩ :=
    FineFan.fineFan_point_localization F z
  refine ⟨{
    openSet := U
    iso := ι
    mem := hz
    generalizations := hgen
    fine := hf
    normalization := ?_ }⟩
  intro p
  have hn := hι.2.2.1 p
  let q := FineFan.affinePullback ι.hom p
  change FineFan.germ (F.space.restrict U.isOpenEmbedding).presheaf ⊤
    ⟨z, hz⟩ (by trivial) q = _
  have he := ConcreteCategory.congr_hom
    (stalkMap_germ (F.space.ofRestrict U.isOpenEmbedding) U ⟨z, hz⟩ hz)
    (FineFan.restrictedGlobalSections F.space U q)
  simp only [CommMonCat.comp_apply] at he
  let V := (Opens.map (F.space.ofRestrict U.isOpenEmbedding).hom.base).obj U
  have i : (⊤ : Opens U) ⟶ V := homOfLE (by intro x _; exact x.property)
  have hw := colimit.w
    (FineFan.stalkDiagram (F.space.restrict U.isOpenEmbedding).presheaf ⟨z, hz⟩)
    (show (op (⟨V, hz⟩ : OpenNhds (⟨z, hz⟩ : U))) ⟶ op ⟨⊤, by trivial⟩ from i.op)
  have heq : (F.space.restrict U.isOpenEmbedding).presheaf.map i.op
      ((F.space.ofRestrict U.isOpenEmbedding).hom.c.app (op U)
        (FineFan.restrictedGlobalSections F.space U q)) = q := by
    change F.space.presheaf.map _ (F.space.presheaf.map _
      (F.space.presheaf.map _ q)) = q
    rw [← ConcreteCategory.comp_apply, ← F.space.presheaf.map_comp]
    rw [← ConcreteCategory.comp_apply, ← F.space.presheaf.map_comp]
    convert ConcreteCategory.congr_hom (F.space.presheaf.map_id _) q using 1
    · congr 2
    · rfl
  calc
    _ = FineFan.germ (F.space.restrict U.isOpenEmbedding).presheaf ⊤ ⟨z, hz⟩
        (by trivial) ((F.space.restrict U.isOpenEmbedding).presheaf.map i.op
          ((F.space.ofRestrict U.isOpenEmbedding).hom.c.app (op U)
            (FineFan.restrictedGlobalSections F.space U q))) := congrArg _ heq.symm
    _ = FineFan.germ (F.space.restrict U.isOpenEmbedding).presheaf V ⟨z, hz⟩ hz
        ((F.space.ofRestrict U.isOpenEmbedding).hom.c.app (op U)
          (FineFan.restrictedGlobalSections F.space U q)) :=
      ConcreteCategory.congr_hom hw _
    _ = FineFan.stalkMap (F.space.ofRestrict U.isOpenEmbedding) ⟨z, hz⟩
        (FineFan.germ F.space.presheaf U z hz
          (FineFan.restrictedGlobalSections F.space U q)) := he.symm
    _ = _ := congrArg (FineFan.stalkMap (F.space.ofRestrict U.isOpenEmbedding) ⟨z, hz⟩) hn

/-- A strict fs Zariski log morphism identifies the affine localizations of any two fan
charts near every point. Equality of the restricted morphisms includes all sheaf maps.
The displayed monoid equivalence is normalized by the chart stalk maps and the canonical
log-morphism map; the final equation fixes the pullback on global monoid sections.

Source: ILO VIII, proof of Theorem 3.3.15, printed p.109, strict specialization;
affine fan interpretation in 3.1.8(ii), 3.1.10(ii)
(blueprint: lem-trf-strict-fan-chart-local-comparison).

Proof:
1. In a finite-generator affine fan chart at a prime, invert the product of generators
outside that prime (the empty product is one). Its basic open is exactly the set of
generalizations and is the smallest neighbourhood. Sections there equal the stalk.
Quotienting units does not change the spectrum, giving the normalized affine model of
the fine sharp stalk. This is the localization construction of def-trf-fine-fan-blowup.
2. The chart maps of lem-trf-log-fan-chart-blowup are stalk isomorphisms. Strictness
identifies the characteristic stalks canonically: the associated-log pushout by units
has the same characteristic, since local ring maps reflect units. Use the characteristic
quotient of def-trf-fs-log-blowup. Compose these isomorphisms to obtain alpha.
3. Apply lem-trf-affine-fan-hom-universal to alpha and its inverse. Naturality and
injectivity give inverse fan morphisms with the prescribed section homomorphism.
4. Intersect the inverse images of the two localized opens. At the chosen point the
two section homomorphisms from the fine source stalk have equal germs. For each of
finitely many generators shrink to a neighbourhood where the sections agree, then
intersect these neighbourhoods. With no generators retain the original intersection.
The homomorphisms agree on every element.
5. Injectivity in lem-trf-affine-fan-hom-universal identifies the two restricted
sharp-space morphisms, including their sheaf maps. All containments hold by the initial
intersection. The construction in steps 2--3 gives the stipulated section formula. -/
theorem strict_fan_chart_local_comparison
    {Y X : FineSaturatedLogScheme.{u}} (f : EtaleLogHom Y X) (hf : f.IsStrict)
    {G F : FineFan.Fan.{u}} (d : LogFanChart Y G) (c : LogFanChart X F)
    (y : Y.scheme) :
    ∃ (g : f.SharpSpaceMap)
      (L : FineFan.PointLocalization F (c.map.hom.base (f.base y)))
      (K : FineFan.PointLocalization G (d.map.hom.base y))
      (U : Y.scheme.Opens),
      y ∈ U ∧
      (∀ t ∈ U, c.map.hom.base (f.base t) ∈ L.openSet) ∧
      (∀ t ∈ U, d.map.hom.base t ∈ K.openSet) ∧
      ∃ (e : G.space.restrict K.openSet.isOpenEmbedding ≅
          F.space.restrict L.openSet.isOpenEmbedding)
        (a : Y.logStructure.sharpSpace.restrict U.isOpenEmbedding ⟶
          F.space.restrict L.openSet.isOpenEmbedding)
        (b : Y.logStructure.sharpSpace.restrict U.isOpenEmbedding ⟶
          G.space.restrict K.openSet.isOpenEmbedding),
        a ≫ F.space.ofRestrict L.openSet.isOpenEmbedding =
          Y.logStructure.sharpSpace.ofRestrict U.isOpenEmbedding ≫ g.map ≫ c.map ∧
        b ≫ G.space.ofRestrict K.openSet.isOpenEmbedding =
          Y.logStructure.sharpSpace.ofRestrict U.isOpenEmbedding ≫ d.map ∧
        a = b ≫ e.hom ∧
        ∃ α : FineFan.stalk F.space.presheaf (c.map.hom.base (f.base y)) ≃*
            FineFan.stalk G.space.presheaf (d.map.hom.base y),
          (FineFan.stalkMap d.map y).hom.comp α.toMonoidHom =
            (FineFan.stalkMap g.map y).hom.comp (FineFan.stalkMap c.map (f.base y)).hom ∧
          (SheafedSpace.Γ.map e.hom.op).hom.comp (FineFan.affinePullback L.iso.hom) =
            (FineFan.affinePullback K.iso.hom).comp α.toMonoidHom := by
  obtain ⟨sections, hn, hg⟩ := strict_sharp_space_sections f hf c.zariski
  let g : f.SharpSpaceMap := ⟨sections, hn⟩
  have hg' : ∀ x, Function.Bijective (FineFan.stalkMap g.map x) := hg
  obtain ⟨L⟩ := pointLocalization_exists F (c.map.hom.base (f.base y))
  obtain ⟨K⟩ := pointLocalization_exists G (d.map.hom.base y)
  let P := FineFan.stalk F.space.presheaf (c.map.hom.base (f.base y))
  let Q := FineFan.stalk G.space.presheaf (d.map.hom.base y)
  let ac := MulEquiv.ofBijective (FineFan.stalkMap c.map (f.base y)).hom
    (c.stalkBijective (f.base y))
  let af := MulEquiv.ofBijective (FineFan.stalkMap g.map y).hom (hg' y)
  let ad := MulEquiv.ofBijective (FineFan.stalkMap d.map y).hom (d.stalkBijective y)
  let α : P ≃* Q := ac.trans (af.trans ad.symm)
  have hα : (FineFan.stalkMap d.map y).hom.comp α.toMonoidHom =
      (FineFan.stalkMap g.map y).hom.comp (FineFan.stalkMap c.map (f.base y)).hom := by
    ext p
    change ad (ad.symm (af (ac p))) = af (ac p)
    exact ad.apply_symm_apply _
  obtain ⟨e₀, _, he₀⟩ := affine_iso P Q L.fine (F.sharp _) K.fine (G.sharp _) α
  let e : G.space.restrict K.openSet.isOpenEmbedding ≅
      F.space.restrict L.openSet.isOpenEmbedding := K.iso ≪≫ e₀ ≪≫ L.iso.symm
  have he : (SheafedSpace.Γ.map e.hom.op).hom.comp (FineFan.affinePullback L.iso.hom) =
      (FineFan.affinePullback K.iso.hom).comp α.toMonoidHom := by
    rw [← affinePullback_comp]
    have hec : e.hom ≫ L.iso.hom = K.iso.hom ≫ e₀.hom := by
      simp [e, Category.assoc]
    rw [hec, affinePullback_comp, he₀]
    rfl
  have hT : ∀ x : Y.logStructure.sharpSpace,
      FineFan.IsSharp (FineFan.stalk Y.logStructure.sharpSpace.presheaf x) := by
    intro x
    exact sharp_of_equiv
      (MulEquiv.ofBijective (FineFan.stalkMap d.map x).hom (d.stalkBijective x))
      (G.sharp _)
  have hα' : (FineFan.stalkMap d.map y).hom.comp α.toMonoidHom =
      (FineFan.stalkMap (g.map ≫ c.map) y).hom := by
    rw [stalkMap_comp, CommMonCat.hom_comp]
    exact hα
  obtain ⟨U, hy, hL, hK, a, b, ha, hb, hab⟩ := FineFan.affine_open_germ_comparison
    Y.logStructure.sharpSpace hT F G (g.map ≫ c.map) d.map
    (local_comp _ _ (local_of_bijective g.map hg')
      (local_of_bijective c.map c.stalkBijective))
    (local_of_bijective d.map d.stalkBijective) y L.toAffineOpen K.toAffineOpen
    L.mem K.mem L.fine L.normalization K.normalization α.toMonoidHom hα' e he
  exact ⟨g, L, K, U, hy, hL, hK, e, a, b, ha, hb, hab, α, hα, he⟩

end AlgebraicGeometry
