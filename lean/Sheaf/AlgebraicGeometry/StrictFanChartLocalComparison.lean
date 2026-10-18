/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q154
-/
import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
import Sheaf.AlgebraicGeometry.FineFanBlowup
import Sheaf.AlgebraicGeometry.LogFanChartBlowup
import Sheaf.AlgebraicGeometry.AffineFanHomUniversal

/-!
# Local comparison of fan charts under a strict log morphism

Source: ILO, Exposé VIII, proof of Theorem 3.3.15, printed p.109; affine fan
localizations in 3.1.2--3.1.10 (blueprint: lem-trf-strict-fan-chart-local-comparison).
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace

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
  sorry

end AlgebraicGeometry
