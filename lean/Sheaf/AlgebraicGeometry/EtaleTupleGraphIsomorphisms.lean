/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Sheaf.AlgebraicGeometry.EtaleModuleTupleSheaf
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence

/-!
# Graph evaluation for compatible étale module tuples

Source: Stacks Project, Sites, Tag 04TR (lemma-glue-sheaves), omitted local
isomorphisms and overlap diagrams; Properties of Spaces, Tags 03ED and 03G7
(blueprint: lem-trf-space-etale-tuple-graph-isomorphisms).

Local modules live on the localized sites from `AlgebraicSpace.etalePullback`.
The two equalizer arrows are specified by the exact formulas of the tuple-sheaf
node. The conclusion specifies both directions of the local isomorphisms.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Evaluate a transition on a test object with two specified lifts. The identity
arrows in the localized sites implement the canonical projection identifications.
Source: Stacks, Sites, Tag 04TR, evaluation of transition maps
(blueprint: lem-trf-space-etale-tuple-graph-isomorphisms). -/
noncomputable def tupleTransitionValue {S : Scheme.{u}} (F : AlgebraicSpace S)
    {T U : F.EtaleSite}
    (L : ringedSiteModules.{max (u + 1) v} (F.structureSheaf.over T))
    (N : ringedSiteModules.{max (u + 1) v} (F.structureSheaf.over U))
    (a : (F.etalePullbackMap (prod.snd : T ⨯ U ⟶ U)).obj N ⟶
      (F.etalePullbackMap (prod.fst : T ⨯ U ⟶ T)).obj L)
    (t : Over T) (s : t.left ⟶ U)
    (y : N.val.obj (op (Over.mk s))) : L.val.obj (op t) :=
  L.val.map (Over.homMk (𝟙 t.left) (by simp) :
      t ⟶ (Over.map prod.fst).obj (Over.mk (prod.lift t.hom s))).op
    (a.val.app (op (Over.mk (prod.lift t.hom s)))
      (N.val.map (Over.homMk (𝟙 t.left) (by simp) :
        (Over.map prod.snd).obj (Over.mk (prod.lift t.hom s)) ⟶ Over.mk s).op y))

/-- The graph `(t,1)` as an arrow in the localized site of the chart.
The first product coordinate is the chart coordinate, as in `tupleChartSheaf`.
Source: Stacks, Sites, Tag 04TR, omitted local isomorphisms
(blueprint: lem-trf-space-etale-tuple-graph-isomorphisms). -/
noncomputable def tupleGraphArrow {S : Scheme.{u}} (F : AlgebraicSpace S)
    {T W : F.EtaleSite} (t : W ⟶ T) :
    Over.mk t ⟶ (Over.star T).obj W :=
  Over.homMk (prod.lift t (𝟙 W)) (by simp)

/-- The `i`th coordinate of the explicit tuple equalizer, through its canonical inclusion.
Source: Stacks, Sites, Tag 04TR, compatible-tuples formula
(blueprint: lem-trf-space-etale-tuple-graph-isomorphisms). -/
noncomputable def tupleEqualizerCoordinate {S : Scheme.{u}} (F : AlgebraicSpace S)
    {I : Type v} (V : I → F.EtaleSite)
    (L : ∀ i : I, ringedSiteModules.{max (u + 1) v} (F.structureSheaf.over (V i)))
    (f g : tupleProduct F V L ⟶ tupleOverlapProduct F V L)
    (W : F.EtaleSite) (s : (equalizer f g).val.obj (op W)) (i : I) :
    (tupleChartSheaf F (V i) (L i)).val.obj (op W) :=
  tupleProductCoordinates F V L W ((equalizer.ι f g).val.app (op W) s) i

/-- Graph evaluation of the chart coordinate of a compatible tuple.
Source: Stacks, Sites, Tag 04TR, omitted local isomorphisms
(blueprint: lem-trf-space-etale-tuple-graph-isomorphisms). -/
noncomputable def tupleGraphValue {S : Scheme.{u}} (F : AlgebraicSpace S)
    {I : Type v} (V : I → F.EtaleSite)
    (L : ∀ i : I, ringedSiteModules.{max (u + 1) v} (F.structureSheaf.over (V i)))
    (f g : tupleProduct F V L ⟶ tupleOverlapProduct F V L)
    (i : I) {W : F.EtaleSite} (t : W ⟶ V i)
    (s : (equalizer f g).val.obj (op W)) : (L i).val.obj (op (Over.mk t)) :=
  (L i).val.map (tupleGraphArrow F t).op (tupleEqualizerCoordinate F V L f g W s i)

/-- Graph evaluation and the transition formula are mutually inverse natural linear
maps on every localized étale site. The overlap identity includes equal chart indices
with different lifts; normalization is imposed only when the two lifts coincide.
The equalizer arrows `f,g` are exactly those specified by
`exists_etale_module_tuple_sheaf`, so this is the specified tuple module, with its
coordinatewise operations, and does not assume a covering or local freeness.
Source: Stacks, Sites, Tag 04TR (lemma-glue-sheaves), omitted local isomorphisms
and commutative diagrams
(blueprint: lem-trf-space-etale-tuple-graph-isomorphisms).

Proof:
1. Representability and chartwise étale permanence make all products, graphs and
   graph maps into triple products objects and arrows of the small étale site.
   Postcomposition identifies each chart's étale site with its localized site,
   with the same structure rings (regular functions).
2. For a local section y, put z_i = a_ia(y restricted to V_i times W).
   On a double overlap, naturality and the cocycle give a_ij z_j = z_i.
   Thus the literal compatible-tuple formula of
   lem-trf-space-etale-module-tuple-sheaf gives the inverse map.
3. Coordinatewise scalar multiplication and linearity of transitions prove
   linearity. For a map W' to W over the chart, the induced product map commutes
   with its graph; this and transition naturality prove naturality in both directions.
4. Evaluation after this inverse pulls a_aa back along (t,t), the diagonal.
   Diagonal normalization and projection composed with graph equal to identity
   give e j = identity. No identity off the diagonal is used.
5. Pull the (i,a) tuple equation back along (v_i,w) maps to (v_i,t(w),w).
   Its projections are identity and graph composed with the projection to W.
   This gives j e = identity in every coordinate, hence in the equalizer.
6. These natural linear maps and their identities define the stated sheaf isomorphisms.
   Pull the (a,b) tuple equation back along (t_a,t_b,identity) to obtain
   e_a = a_ab e_b on every test object, including a=b with distinct lifts.
   None of the calculations uses joint surjectivity or local freeness. -/
theorem etale_tuple_graph_isomorphisms {S : Scheme.{u}} (F : AlgebraicSpace S)
    {I : Type v} (V : I → F.EtaleSite)
    (L : ∀ i : I, ringedSiteModules.{max (u + 1) v} (F.structureSheaf.over (V i)))
    (a : ∀ i j : I,
      (F.etalePullbackMap (prod.snd : V i ⨯ V j ⟶ V j)).obj (L j) ≅
        (F.etalePullbackMap (prod.fst : V i ⨯ V j ⟶ V i)).obj (L i))
    (hdiag : ∀ (i : I) (W : F.EtaleSite) (t : W ⟶ V i)
      (y : (L i).val.obj (op (Over.mk t))),
      tupleTransitionValue F (L i) (L i) (a i i).hom (Over.mk t) t y = y)
    (hcocycle : ∀ (i j k : I) (W : F.EtaleSite)
      (t : W ⟶ V i) (s : W ⟶ V j) (r : W ⟶ V k)
      (y : (L k).val.obj (op (Over.mk r))),
      tupleTransitionValue F (L i) (L k) (a i k).hom (Over.mk t) r y =
        tupleTransitionValue F (L i) (L j) (a i j).hom (Over.mk t) s
          (tupleTransitionValue F (L j) (L k) (a j k).hom (Over.mk s) r y))
    (f g : tupleProduct F V L ⟶ tupleOverlapProduct F V L)
    (hf : ∀ (W : F.EtaleSite) (s : (tupleProduct F V L).val.obj (op W)) (i j : I),
      tupleOverlapCoordinates F V L W (f.val.app (op W) s) (i, j) =
        tupleLeftSection F V L W (tupleProductCoordinates F V L W s) i j)
    (hg : ∀ (W : F.EtaleSite) (s : (tupleProduct F V L).val.obj (op W)) (i j : I),
      tupleOverlapCoordinates F V L W (g.val.app (op W) s) (i, j) =
        tupleRightSection F V L (fun i j : I ↦ (a i j).hom) W
          (tupleProductCoordinates F V L W s) i j) :
    ∃ e : ∀ i : I, (F.etalePullback (V i)).obj (equalizer f g) ≅ L i,
      (∀ (i : I) (W : F.EtaleSite) (t : W ⟶ V i)
        (s : (equalizer f g).val.obj (op W)),
        (e i).hom.val.app (op (Over.mk t)) s = tupleGraphValue F V L f g i t s) ∧
      (∀ (i k : I) (W : F.EtaleSite) (t : W ⟶ V i)
        (y : (L i).val.obj (op (Over.mk t))),
        tupleEqualizerCoordinate F V L f g W ((e i).inv.val.app (op (Over.mk t)) y) k =
          tupleTransitionValue F (L k) (L i) (a k i).hom
            ((Over.star (V k)).obj W) (prod.snd ≫ t)
            ((L i).val.map (Over.homMk (prod.snd : V k ⨯ W ⟶ W) rfl :
              Over.mk (prod.snd ≫ t) ⟶ Over.mk t).op y)) ∧
      (∀ (i j : I) (W : F.EtaleSite) (t : W ⟶ V i) (s : W ⟶ V j)
        (z : (equalizer f g).val.obj (op W)),
        (e i).hom.val.app (op (Over.mk t)) z =
          tupleTransitionValue F (L i) (L j) (a i j).hom (Over.mk t) s
            ((e j).hom.val.app (op (Over.mk s)) z)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
