/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerShriekData
public import WeilConjectures.AlgebraicGeometry.SmoothPurityCoordinateCategories
public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerShriekLevels
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.AlgebraicGeometry.FiniteSupportCoordinates
public import WeilConjectures.AlgebraicGeometry.CompositeProjectionCoefficients
public import WeilConjectures.AlgebraicGeometry.TowerAdjointCompositorRealization
public import WeilConjectures.AlgebraicGeometry.SmoothPurityCoefficientTowers
public import WeilConjectures.AlgebraicGeometry.SmoothPurityNormalizedTowers
public import WeilConjectures.AlgebraicGeometry.ExchangeProjectionSuppliedDomains
public import WeilConjectures.SixFunctors.OpenTensorNormalization
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.SemilinearDerivedSections
import WeilConjectures.AlgebraicGeometry.RouteTensorProjectionFactorwiseNaturality
import WeilConjectures.SecSmoothPurity.TowerProjectionRefinement
import WeilConjectures.SecSmoothPurity.TowerProjectionTriangle

/-! # Composition and projection for the ell-power coefficient tower

Source: Stacks Project, Tags 0F7J (lemma-shriek-composition) and 0B56
(equation-projection-formula-map), with the ell-power tower formulation in the
smooth-purity composition factors proof (blueprint: lem-sp-tower-composition-projection-mate).

The equation is stated in the ordinary derived category of strict varying-coefficient
systems, before any finite-level evaluation. The coefficient system is indexed by powers
of `ell`; it is not replaced by a uniformizer-power system.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.SpTowerCompositionProjectionMate

open CompositeProjectionCoefficients


variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (D : WeilConjectures.FiniteFieldDatum.{u})
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)
  (z : SpTowerCalculus.FiniteCoordinates l E)
  (pres : SpTowerCalculus.Preservation l E D.k b o q)
  (cal : SpTowerCalculus.Calculus l E D.k b o q z pres)
  {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))] [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Z ↘ Spec (.of D.k))] [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
  [QuasiCompact (Z ↘ Spec (.of D.k))]
  (f : X ⟶ Y) (g : Y ⟶ Z)
  [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
  (cf : Compactification f) (cg : Compactification g) (ch : Compactification (f ≫ g))

private theorem tower_compositor_natural
    (M M' : SpTowerShriek.D l E X)
    (hM : towerCtf l E b q X M) (hM' : towerCtf l E b q X M') (a : M ⟶ M') :
    (SpTowerShriek.F l E b o cg).map ((SpTowerShriek.F l E b o cf).map a) ≫
        towerCompositor l E D b o q z pres cal f g cf cg ch M' hM' =
      towerCompositor l E D b o q z pres cal f g cf cg ch M hM ≫
        (SpTowerShriek.F l E b o ch).map a := by
  dsimp only [towerCtf] at hM hM'
  let RX := SpTowerCalculus.realization l E b X (q.abelian X)
  let RZ := SpTowerCalculus.realization l E b Z (q.abelian Z)
  let F := SpTowerShriek.F l E b o cf
  let G := SpTowerShriek.F l E b o cg
  let H := SpTowerShriek.F l E b o ch
  let C := SpTowerCalculus.F l E b o q cf
  let sF := SpCoordinateAdjunction.supportRealization l E b o q cf
  let sG := SpCoordinateAdjunction.supportRealization l E b o q cg
  let sH := SpCoordinateAdjunction.supportRealization l E b o q ch
  let c := cal.composition.composition f g (f ≫ g) rfl cf cg ch
  let a' : (⟨RX.inverse.obj M, hM⟩ : SpTowerCalculus.C l E b q X) ⟶
      ⟨RX.inverse.obj M', hM'⟩ := ObjectProperty.homMk (RX.inverse.map a)
  have h0 := RX.counitIso.inv.naturality a
  have h1 := sF.inv.naturality (RX.inverse.map a)
  have h2 := sG.inv.naturality (C.map (RX.inverse.map a))
  have h3 := congrArg RZ.functor.map (c.hom.naturality a')
  have h4 := sH.hom.naturality (RX.inverse.map a)
  have h5 := RX.counitIso.hom.naturality a
  dsimp only [Functor.comp_map, Functor.id_map] at h0 h1 h2 h4 h5
  change G.map (F.map a) ≫
    (G.map (F.map (RX.counitIso.inv.app M')) ≫
      G.map (sF.inv.app (RX.inverse.obj M')) ≫
      sG.inv.app (C.obj (RX.inverse.obj M')) ≫
      RZ.functor.map (c.hom.app ⟨RX.inverse.obj M', hM'⟩) ≫
      sH.hom.app (RX.inverse.obj M') ≫ H.map (RX.counitIso.hom.app M')) =
    (G.map (F.map (RX.counitIso.inv.app M)) ≫
      G.map (sF.inv.app (RX.inverse.obj M)) ≫
      sG.inv.app (C.obj (RX.inverse.obj M)) ≫
      RZ.functor.map (c.hom.app ⟨RX.inverse.obj M, hM⟩) ≫
      sH.hom.app (RX.inverse.obj M) ≫ H.map (RX.counitIso.hom.app M)) ≫ H.map a
  have h0m := congrArg (fun t ↦ G.map (F.map t)) h0
  simp only [Functor.map_comp] at h0m
  change F.map (RX.functor.map (RX.inverse.map a)) ≫
      sF.inv.app (RX.inverse.obj M') =
    sF.inv.app (RX.inverse.obj M) ≫
      (SpTowerCalculus.realization l E b Y (q.abelian Y)).functor.map
        (C.map (RX.inverse.map a)) at h1
  have h1m := congrArg G.map h1
  simp only [Functor.map_comp] at h1m
  dsimp only [Functor.comp_map, SpTowerCalculus.inclusion, ObjectProperty.ι_map,
    ObjectProperty.homMk_hom, a'] at h3
  rw [Functor.map_comp, Functor.map_comp] at h3
  change G.map ((SpTowerCalculus.realization l E b Y (q.abelian Y)).functor.map
        (C.map (RX.inverse.map a))) ≫ sG.inv.app (C.obj (RX.inverse.obj M')) =
      sG.inv.app (C.obj (RX.inverse.obj M)) ≫
        RZ.functor.map ((SpTowerCalculus.F l E b o q cg).map
          (C.map (RX.inverse.map a))) at h2
  change RZ.functor.map ((SpTowerCalculus.F l E b o q ch).map (RX.inverse.map a)) ≫
        sH.hom.app (RX.inverse.obj M') =
      sH.hom.app (RX.inverse.obj M) ≫ H.map (RX.functor.map (RX.inverse.map a)) at h4
  have h5m := congrArg H.map h5
  simp only [Functor.map_comp] at h5m
  simp only [Category.assoc]
  rw [reassoc_of% h0m, reassoc_of% h1m, reassoc_of% h2,
    reassoc_of% h3, reassoc_of% h4, h5m]


private theorem transport_projection_word
    {B C : Type*} [Category B] [Category C]
    (G : B ⥤ C) (S : B ⥤ B) (T : C ⥤ C)
    {A A' V V' : B} {H H' W W' : C}
    (rM : A ≅ A') (rV : V ≅ V') (sM : H ≅ H') (sV : W ≅ W')
    (aM : G.obj A ⟶ H) (aM' : G.obj A' ⟶ H')
    (aV : G.obj V ⟶ W) (aV' : G.obj V' ⟶ W')
    (p : S.obj A ⟶ V) (p' : S.obj A' ⟶ V')
    (q : T.obj (G.obj A) ⟶ G.obj (S.obj A))
    (q' : T.obj (G.obj A') ⟶ G.obj (S.obj A'))
    (h : T.obj H ⟶ W) (h' : T.obj H' ⟶ W')
    (hq : T.map (G.map rM.hom) ≫ q' = q ≫ G.map (S.map rM.hom))
    (hp : S.map rM.hom ≫ p' = p ≫ rV.hom)
    (hh : T.map sM.hom ≫ h' = h ≫ sV.hom)
    (haM : G.map rM.hom ≫ aM' = aM ≫ sM.hom)
    (haV : G.map rV.hom ≫ aV' = aV ≫ sV.hom)
    (htriangle : q' ≫ G.map p' ≫ aV' = T.map aM' ≫ h') :
    q ≫ G.map p ≫ aV = T.map aM ≫ h := by
  apply (cancel_mono sV.hom).1
  simp only [Category.assoc]
  rw [← haV, ← G.map_comp_assoc, ← hp, G.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% hq, htriangle, ← T.map_comp_assoc, haM, T.map_comp]
  rw [Category.assoc, hh]

private theorem tower_compositor_refinement
    (cf' : Compactification f) (ch' : Compactification (f ≫ g))
    (M : SpTowerShriek.D l E X) (hM : towerCtf l E b q X M) :
    (SpTowerShriek.F l E b o cg).map
        (SpTowerProjectionRefinement.supportComparison l E b o q cf cf'
          (cal.composition.refinement f cf cf') M hM).hom ≫
        towerCompositor l E D b o q z pres cal f g cf' cg ch' M hM =
      towerCompositor l E D b o q z pres cal f g cf cg ch M hM ≫
        (SpTowerProjectionRefinement.supportComparison l E b o q ch ch'
          (cal.composition.refinement (f ≫ g) ch ch') M hM).hom := by
  dsimp only [towerCtf] at hM
  let RX := SpTowerCalculus.realization l E b X (q.abelian X)
  let RY := SpTowerCalculus.realization l E b Y (q.abelian Y)
  let RZ := SpTowerCalculus.realization l E b Z (q.abelian Z)
  let K : SpTowerCalculus.C l E b q X := ⟨RX.inverse.obj M, hM⟩
  let F := SpTowerShriek.F l E b o cf
  let F' := SpTowerShriek.F l E b o cf'
  let G := SpTowerShriek.F l E b o cg
  let H := SpTowerShriek.F l E b o ch
  let H' := SpTowerShriek.F l E b o ch'
  let ε := RX.counitIso.app M
  let sF := (SpCoordinateAdjunction.supportRealization l E b o q cf).app K.obj
  let sF' := (SpCoordinateAdjunction.supportRealization l E b o q cf').app K.obj
  let sG := SpCoordinateAdjunction.supportRealization l E b o q cg
  let sH := (SpCoordinateAdjunction.supportRealization l E b o q ch).app K.obj
  let sH' := (SpCoordinateAdjunction.supportRealization l E b o q ch').app K.obj
  let rf := (cal.composition.refinement f cf cf').app K
  let rh := (cal.composition.refinement (f ≫ g) ch ch').app K
  let α := (cal.composition.composition f g (f ≫ g) rfl cf cg ch).app K
  let α' := (cal.composition.composition f g (f ≫ g) rfl cf' cg ch').app K
  have hc := cal.coherence.refinement_composition f g cf cf' cg cg ch ch' K
  rw [cal.coherence.refinement_identity] at hc
  simp only [Iso.refl_hom, NatTrans.id_app] at hc
  change (SpTowerCalculus.F l E b o q cg).map rf.hom ≫ 𝟙 _ ≫ α'.hom =
    α.hom ≫ rh.hom at hc
  rw [Category.id_comp] at hc
  have hc' := congrArg RZ.functor.map hc
  simp only [Functor.map_comp] at hc'
  have hn := sG.inv.naturality rf.hom
  change G.map (RY.functor.map rf.hom) ≫
      sG.inv.app ((SpTowerCalculus.F l E b o q cf').obj K.obj) =
    sG.inv.app ((SpTowerCalculus.F l E b o q cf).obj K.obj) ≫
      RZ.functor.map ((SpTowerCalculus.F l E b o q cg).map rf.hom) at hn
  simp only [SpTowerProjectionRefinement.supportComparison, towerCompositor,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv,
    Functor.map_comp, Category.assoc]
  change G.map (F.map ε.inv) ≫ G.map sF.inv ≫ G.map (RY.functor.map rf.hom) ≫
      G.map sF'.hom ≫ G.map (F'.map ε.hom) ≫ G.map (F'.map ε.inv) ≫
      G.map sF'.inv ≫ sG.inv.app ((SpTowerCalculus.F l E b o q cf').obj K.obj) ≫
      RZ.functor.map α'.hom ≫ sH'.hom ≫ H'.map ε.hom =
    G.map (F.map ε.inv) ≫ G.map sF.inv ≫
      sG.inv.app ((SpTowerCalculus.F l E b o q cf).obj K.obj) ≫
      RZ.functor.map α.hom ≫ sH.hom ≫ H.map ε.hom ≫ H.map ε.inv ≫
      sH.inv ≫ RZ.functor.map rh.hom ≫ sH'.hom ≫ H'.map ε.hom
  have hεF : G.map (F'.map ε.hom) ≫ G.map (F'.map ε.inv) = 𝟙 _ :=
    (G.mapIso (F'.mapIso ε)).hom_inv_id
  have hsF : G.map sF'.hom ≫ G.map sF'.inv = 𝟙 _ :=
    (G.mapIso sF').hom_inv_id
  have hεH : H.map ε.hom ≫ H.map ε.inv = 𝟙 _ := (H.mapIso ε).hom_inv_id
  rw [reassoc_of% hεF]
  rw [reassoc_of% hsF, reassoc_of% hεH]
  rw [sH.hom_inv_id_assoc, reassoc_of% hn, reassoc_of% hc']


/-- The compactification projection maps compose under the actual proper/open tower
compositor. The domain witness uses successive pullbacks, identified with composite
pullback by `o.comp`; hence it is exactly the condition on `M ⊗ h*L` in the node.
All maps are ordinary derived-system morphisms before finite evaluation.
Source: Stacks Project, Tag 0F7J, lemma-shriek-composition, and Tag 0B56,
equation-projection-formula-map (blueprint: lem-sp-tower-composition-projection-mate).

Proof:
1. Put `ce = ch.ofComp cg`, `cf' = ce.restrict`, `ch' = cg.comp ce`: the compatible
triangle induced by the supplied `cg` and `ch` (def-pur-compatible-compactification-triangle);
`cg` is not changed. Put `V = M ⊗ f^* g^* L`.
2. Let `r_K : F_cf K ≅ F_cf' K` and `s_K : F_ch K ≅ F_ch' K` be the realization-conjugated
refinements `SpTowerProjectionRefinement.supportComparison`. The coherence law
`refinement_composition`, with identity refinement of `cg`, together with cancellation
of the realization counits and support realizations and naturality of the support
realization of `cg`, gives `F_cg(r_K) ≫ α'_K = α_K ≫ s_K` for `K = M, V`.
3. Projection refinement (lem-sp-tower-projection-refinement) for `cf, cf'` at
`(M, g^*L)` with target `V`, and for `ch, ch'` at `(M, L)` with target coordinate the
inverse pullback compositor, together with projection factorwise naturality
(lem-route-tensor-projection-factorwise-naturality) at `r_M`, move all comparisons.
4. The induced-triangle identity (lem-sp-tower-projection-triangle) holds for
`cf', cg, ch'`. The categorical calculation `transport_projection_word`
moves the input comparisons to the front, applies the triangle identity, and cancels
the isomorphism `s_V`. Composing with `F_ch` of the inverse coordinate gives the
displayed equation. Every step is an equality of tower morphisms before evaluation.
-/
theorem tower_composition_projection_mate (_hl : l ≠ D.p) (d e : ℕ)
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (M : SpTowerShriek.D l E X) (L : SpTowerShriek.D l E Z)
    (hM : towerCtf l E b q X M) (_hL : towerCtf l E b q Z L)
    (hML : towerCtf l E b q X ((SpTowerShriek.tensor l E b X).obj
      (M, (SpTowerShriek.pull l E b (o.geometry f)).obj
        ((SpTowerShriek.pull l E b (o.geometry g)).obj L)))) :
    SpTowerShriek.projection l E b o cg ((SpTowerShriek.F l E b o cf).obj M) L ≫
        (SpTowerShriek.F l E b o cg).map
          (SpTowerShriek.projection l E b o cf M
            ((SpTowerShriek.pull l E b (o.geometry g)).obj L)) ≫
        towerCompositor l E D b o q z pres cal f g cf cg ch _ hML ≫
        (SpTowerShriek.F l E b o ch).map
          ((SpTowerShriek.tensor l E b X).map
            (Prod.mkHom (𝟙 M) ((o.comp f g).hom.app L))) =
      (SpTowerShriek.tensor l E b Z).map
          (Prod.mkHom (towerCompositor l E D b o q z pres cal f g cf cg ch M hM) (𝟙 L)) ≫
        SpTowerShriek.projection l E b o ch M L := by
  let ce : Compactification (f ≫ cg.i) := ch.ofComp cg
  let cf' := ce.restrict
  let ch' := cg.comp ce
  let F := SpTowerShriek.F l E b o cf
  let F' := SpTowerShriek.F l E b o cf'
  let G := SpTowerShriek.F l E b o cg
  let H := SpTowerShriek.F l E b o ch
  let H' := SpTowerShriek.F l E b o ch'
  let pg := SpTowerShriek.pull l E b (o.geometry g)
  let Tx := SpTowerShriek.tensor l E b X
  let V := Tx.obj (M, (SpTowerShriek.pull l E b (o.geometry f)).obj (pg.obj L))
  let t := Tx.mapIso ((Iso.refl M).prod ((o.comp f g).app L).symm)
  let S := (Functor.curry.obj (SpTowerShriek.tensor l E b Y)).flip.obj (pg.obj L)
  let T := (Functor.curry.obj (SpTowerShriek.tensor l E b Z)).flip.obj L
  let rM := SpTowerProjectionRefinement.supportComparison l E b o q cf cf'
    (cal.composition.refinement f cf cf') M hM
  let rV := SpTowerProjectionRefinement.supportComparison l E b o q cf cf'
    (cal.composition.refinement f cf cf') V hML
  let sM := SpTowerProjectionRefinement.supportComparison l E b o q ch ch'
    (cal.composition.refinement (f ≫ g) ch ch') M hM
  let sV := SpTowerProjectionRefinement.supportComparison l E b o q ch ch'
    (cal.composition.refinement (f ≫ g) ch ch') V hML
  let aM := towerCompositor l E D b o q z pres cal f g cf cg ch M hM
  let aM' := towerCompositor l E D b o q z pres cal f g cf' cg ch' M hM
  let aV := towerCompositor l E D b o q z pres cal f g cf cg ch V hML
  let aV' := towerCompositor l E D b o q z pres cal f g cf' cg ch' V hML
  let p := SpTowerShriek.projection l E b o cf M (pg.obj L)
  let p' := SpTowerShriek.projection l E b o cf' M (pg.obj L)
  let qM := SpTowerShriek.projection l E b o cg (F.obj M) L
  let qM' := SpTowerShriek.projection l E b o cg (F'.obj M) L
  let h := SpTowerShriek.projection l E b o ch M L ≫ H.map t.hom
  let h' := SpTowerShriek.projection l E b o ch' M L ≫ H'.map t.hom
  have hq : T.map (G.map rM.hom) ≫ qM' = qM ≫ G.map (S.map rM.hom) := by
    have hq0 := SpTowerShriek.projection_factorwise_naturality l E b o cg rM.hom (𝟙 L)
    change T.map (G.map rM.hom) ≫ qM' = qM ≫ G.map
      ((SpTowerShriek.tensor l E b Y).map (Prod.mkHom rM.hom (pg.map (𝟙 L)))) at hq0
    rw [pg.map_id] at hq0
    exact hq0
  have hp : S.map rM.hom ≫ p' = p ≫ rV.hom := by
    have hp0 := SpTowerProjectionRefinement.projection_refinement l E D b o q z pres cal
      f cf cf' _hl M (pg.obj L) hM V hML (Iso.refl V)
    change S.map rM.hom ≫ p' ≫ F'.map (𝟙 V) =
      p ≫ F.map (𝟙 V) ≫ rV.hom at hp0
    rw [F'.map_id, F.map_id, Category.comp_id, Category.id_comp] at hp0
    exact hp0
  have hh : T.map sM.hom ≫ h' = h ≫ sV.hom := by
    have hh0 := SpTowerProjectionRefinement.projection_refinement l E D b o q z pres cal
      (f ≫ g) ch ch' _hl M L hM V hML t
    change T.map sM.hom ≫ SpTowerShriek.projection l E b o ch' M L ≫ H'.map t.hom =
      SpTowerShriek.projection l E b o ch M L ≫ H.map t.hom ≫ sV.hom at hh0
    dsimp only [h, h']
    simpa only [Category.assoc] using hh0
  have haM : G.map rM.hom ≫ aM' = aM ≫ sM.hom :=
    tower_compositor_refinement l E D b o q z pres cal f g cf cg ch cf' ch' M hM
  have haV : G.map rV.hom ≫ aV' = aV ≫ sV.hom :=
    tower_compositor_refinement l E D b o q z pres cal f g cf cg ch cf' ch' V hML
  have htriangle : qM' ≫ G.map p' ≫ aV' = T.map aM' ≫ h' := by
    exact SpTowerProjectionTriangle.projection_triangle l E D b o q z pres cal f g
      _hl cg ce M L hM hML
  have hword := transport_projection_word G S T rM rV sM sV aM aM' aV aV'
    p p' qM qM' h h' hq hp hh haM haV htriangle
  have hfinal := congrArg (fun w ↦ w ≫ H.map t.inv) hword
  simp only [h, Category.assoc, ← H.map_comp, t.hom_inv_id] at hfinal
  rw [H.map_id, Category.comp_id] at hfinal
  exact hfinal

/-- The common composite in the tower composition/projection identity is natural
in both inputs, on exactly the full uniform constructible finite-Tor domain of that
identity. The input arrows are arbitrary ordinary derived-tower morphisms.
Source: Stacks Project, Tags 0F7J and 0B56; naturality clause
(blueprint: lem-sp-tower-composition-projection-mate).

Proof: the compositor `towerCompositor` is natural on the uniform domain, since each
of its six factors is (inverse realization counit, the two inverse support
realizations, the supplied composition transformation, the support realization and the
realization counit). Tensor functoriality combines this with projection factorwise
naturality for `ch` (lem-route-tensor-projection-factorwise-naturality). The main
equation of the preceding theorem is not used.
-/
theorem tower_composition_projection_mate_naturality (_hl : l ≠ D.p) (d e : ℕ)
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (M M' : SpTowerShriek.D l E X) (L L' : SpTowerShriek.D l E Z)
    (hM : towerCtf l E b q X M) (hM' : towerCtf l E b q X M')
    (_hL : towerCtf l E b q Z L) (_hL' : towerCtf l E b q Z L')
    (_hML : towerCtf l E b q X ((SpTowerShriek.tensor l E b X).obj
      (M, (SpTowerShriek.pull l E b (o.geometry f)).obj
        ((SpTowerShriek.pull l E b (o.geometry g)).obj L))))
    (_hML' : towerCtf l E b q X ((SpTowerShriek.tensor l E b X).obj
      (M', (SpTowerShriek.pull l E b (o.geometry f)).obj
        ((SpTowerShriek.pull l E b (o.geometry g)).obj L'))))
    (a : M ⟶ M') (v : L ⟶ L') :
    (SpTowerShriek.tensor l E b Z).map
        (Prod.mkHom ((SpTowerShriek.F l E b o cg).map
          ((SpTowerShriek.F l E b o cf).map a)) v) ≫
      (SpTowerShriek.tensor l E b Z).map
        (Prod.mkHom (towerCompositor l E D b o q z pres cal f g cf cg ch M' hM') (𝟙 L')) ≫
      SpTowerShriek.projection l E b o ch M' L' =
    (SpTowerShriek.tensor l E b Z).map
        (Prod.mkHom (towerCompositor l E D b o q z pres cal f g cf cg ch M hM) (𝟙 L)) ≫
      SpTowerShriek.projection l E b o ch M L ≫
      (SpTowerShriek.F l E b o ch).map
        ((SpTowerShriek.tensor l E b X).map
          (Prod.mkHom a ((SpTowerShriek.pull l E b (o.geometry (f ≫ g))).map v))) := by
  let T := SpTowerShriek.tensor l E b Z
  have ha := tower_compositor_natural l E D b o q z pres cal f g cf cg ch M M' hM hM' a
  have ht :
      T.map (Prod.mkHom ((SpTowerShriek.F l E b o cg).map
          ((SpTowerShriek.F l E b o cf).map a)) v) ≫
        T.map (Prod.mkHom (towerCompositor l E D b o q z pres cal f g cf cg ch M' hM')
          (𝟙 L')) =
      T.map (Prod.mkHom (towerCompositor l E D b o q z pres cal f g cf cg ch M hM)
          (𝟙 L)) ≫
        T.map (Prod.mkHom ((SpTowerShriek.F l E b o ch).map a) v) := by
    rw [← T.map_comp, ← T.map_comp]
    congr 1
    ext
    · exact ha
    · simp
  rw [← Category.assoc, ht, Category.assoc]
  rw [SpTowerShriek.projection_factorwise_naturality l E b o ch a v]


end AlgebraicGeometry.ProEtale.SpTowerCompositionProjectionMate
