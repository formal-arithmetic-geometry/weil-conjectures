/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactCompositionProjection.CompositionProjectionData
import all WeilConjectures.AlgebraicGeometry.AmbientProperOpen.TriangleProjection.TriangleProjectionNormalForm
import all WeilConjectures.AlgebraicGeometry.AmbientProperOpen.RefinementProjection.RefinementProjectionProperComposition
import all WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenProjectionMate
import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemCompositorAssociativity

/-! # Contraction of the triangle projection word

Source: the composition/refinement calculation of the blueprint and Stacks 0F7J
(blueprint: lem-sf-triangle-projection-compositor-contraction).
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOfSpec false
set_option genInjectivity false

universe u g h v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.AmbientProperOpen

namespace AlgebraicGeometry.ProEtale.CompactCompositionProjection

variable {G : Type g} [Category.{h} G] {geo : G ⥤ Scheme.{u}}

attribute [local implicit_reducible] compact ordinary ordinaryTensor

variable (c : Calculus.{u, g, h, v, w} G geo) (t : TensorData c)

private def tr {X : G} (K : c.D X) {M N : c.D X} (a : M ⟶ N) :=
  (t.tensor X).map (Prod.mkHom (𝟙 K) a)

private theorem tr_comp {X : G} (K : c.D X) {M N Q : c.D X}
    (a : M ⟶ N) (b : N ⟶ Q) :
    tr c t K (a ≫ b) = tr c t K a ≫ tr c t K b := by
  exact ((Functor.curryObj (t.tensor X)).obj K).map_comp a b

private def tf {X : G} {M N : c.D X} (a : M ⟶ N) (L : c.D X) :=
  (t.tensor X).map (Prod.mkHom a (𝟙 L))

private theorem tf_comp {X : G} {M N Q : c.D X}
    (a : M ⟶ N) (b : N ⟶ Q) (L : c.D X) :
    tf c t (a ≫ b) L = tf c t a L ≫ tf c t b L := by
  exact congr_app ((Functor.curryObj (t.tensor X)).map_comp a b) L

private theorem tr_id {X : G} (K M : c.D X) : tr c t K (𝟙 M) = 𝟙 _ :=
  ((Functor.curryObj (t.tensor X)).obj K).map_id M

private def rawProjection {X V Y : G} (j : X ⟶ V) (q : V ⟶ Y)
    [IsOpenImmersion (geo.map j)] (K : c.D X) (L : c.D Y) :=
  t.pi q ((c.J j).obj K) L ≫ (c.S q).map (t.delta j K ((c.P q).obj L))

private theorem projection_raw {X V Y : G} (j : X ⟶ V) (q : V ⟶ Y)
    [IsOpenImmersion (geo.map j)] (K : c.D X) (L : c.D Y) :
    projection c t j q K L = rawProjection c t j q K L ≫
      (compact c j q).map (tr c t K ((c.pComp j q).inv.app L)) := by
  simp only [projection, rawProjection, compact, tr, Functor.comp_map,
    Functor.map_comp, Category.assoc]

private theorem alpha_component {X V W Y B Z : G} (j : X ⟶ V) (b : V ⟶ W)
    (q : V ⟶ Y) (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion (geo.map j)] [IsOpenImmersion (geo.map b)]
    [IsOpenImmersion (geo.map i)] [QuasiCompact (geo.map b)]
    [QuasiCompact (geo.map i)] [IsProper (geo.map q)] [IsProper (geo.map p)]
    (h : b ≫ p = q ≫ i) (K : c.D X) :
    (alpha c j b q p i s h).app K =
      (c.S s).map ((c.gamma b q p i h).app ((c.J j).obj K)) ≫
        (c.sComp p s).hom.app ((c.J b).obj ((c.J j).obj K)) ≫
        (c.S (p ≫ s)).map ((c.jComp j b).hom.app K) := by
  simp only [alpha, compact, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_obj, Category.id_comp]

private structure Naturality : Prop where
  pi : ∀ {X Y : G} (f : X ⟶ Y) (M : c.D X) {L L' : c.D Y} (a : L ⟶ L'),
    tr c t ((c.S f).obj M) a ≫ t.pi f M L' =
      t.pi f M L ≫ (c.S f).map (tr c t M ((c.P f).map a))
  pi_first : ∀ {X Y : G} (f : X ⟶ Y) {M M' : c.D X} (a : M ⟶ M') (L : c.D Y),
    (t.tensor Y).map (Prod.mkHom ((c.S f).map a) (𝟙 L)) ≫ t.pi f M' L =
      t.pi f M L ≫ (c.S f).map ((t.tensor X).map
        (Prod.mkHom a (𝟙 ((c.P f).obj L))))
  delta : ∀ {X Y : G} (j : X ⟶ Y) [IsOpenImmersion (geo.map j)]
    (M : c.D X) {L L' : c.D Y} (a : L ⟶ L'),
    tr c t ((c.J j).obj M) a ≫ t.delta j M L' =
      t.delta j M L ≫ (c.J j).map (tr c t M ((c.P j).map a))

private theorem raw_naturality (hn : Naturality c t)
    {X V Y : G} (j : X ⟶ V) (q : V ⟶ Y) [IsOpenImmersion (geo.map j)]
    (K : c.D X) {L L' : c.D Y} (a : L ⟶ L') :
    tr c t ((compact c j q).obj K) a ≫ rawProjection c t j q K L' =
      rawProjection c t j q K L ≫
        (compact c j q).map (tr c t K ((c.P j).map ((c.P q).map a))) := by
  dsimp only [rawProjection, compact, Functor.comp_obj, Functor.comp_map]
  rw [← Category.assoc, hn.pi, Category.assoc, ← Functor.map_comp,
    hn.delta, Functor.map_comp]
  simp only [Category.assoc]

private theorem projection_naturality_right (hn : Naturality c t)
    {X V Y : G} (j : X ⟶ V) (q : V ⟶ Y) [IsOpenImmersion (geo.map j)]
    (K : c.D X) {L L' : c.D Y} (a : L ⟶ L') :
    tr c t ((compact c j q).obj K) a ≫ projection c t j q K L' =
      projection c t j q K L ≫
        (compact c j q).map (tr c t K ((c.P (j ≫ q)).map a)) := by
  rw [projection_raw, projection_raw, ← Category.assoc, raw_naturality c t hn]
  simp only [Category.assoc, ← Functor.map_comp, ← tr_comp]
  congr 2
  exact congrArg (tr c t K) ((c.pComp j q).inv.naturality a)

private def leftTransport {X V W Y B Z : G} (j : X ⟶ V) (b : V ⟶ W)
    (q : V ⟶ Y) (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    (h : b ≫ p = q ≫ i) (L : c.D Z) :=
  (c.pComp j q).inv.app ((c.P i).obj ((c.P s).obj L)) ≫
    (c.P (j ≫ q)).map ((c.pComp i s).inv.app L) ≫
    (trianglePull c j b q p i s h).hom.app L

private def normalLeft {X V W Y B Z : G} (j : X ⟶ V) (b : V ⟶ W)
    (q : V ⟶ Y) (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion (geo.map j)] [IsOpenImmersion (geo.map b)]
    [IsOpenImmersion (geo.map i)] [QuasiCompact (geo.map b)]
    [QuasiCompact (geo.map i)] [IsProper (geo.map q)] [IsProper (geo.map p)]
    (h : b ≫ p = q ≫ i) (K : c.D X) (L : c.D Z) :=
  rawProjection c t i s ((compact c j q).obj K) L ≫
    (compact c i s).map (rawProjection c t j q K ((c.P i).obj ((c.P s).obj L))) ≫
    (alpha c j b q p i s h).app
      ((t.tensor X).obj (K, (c.P j).obj ((c.P q).obj
        ((c.P i).obj ((c.P s).obj L)))))

private def normalInput {X V Y B Z : G} (j : X ⟶ V) (q : V ⟶ Y)
    (i : Y ⟶ B) (s : B ⟶ Z) (K : c.D X) (L : c.D Z) :=
  (t.tensor X).obj (K, (c.P j).obj ((c.P q).obj ((c.P i).obj ((c.P s).obj L))))

private theorem normalLeft_native {X V W Y B Z : G} (j : X ⟶ V) (b : V ⟶ W)
    (q : V ⟶ Y) (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion (geo.map j)] [IsOpenImmersion (geo.map b)]
    [IsOpenImmersion (geo.map i)] [QuasiCompact (geo.map b)]
    [QuasiCompact (geo.map i)] [IsProper (geo.map q)] [IsProper (geo.map p)]
    (h : b ≫ p = q ≫ i) (K : c.D X) (L : c.D Z) :
    normalLeft c t j b q p i s h K L =
      t.pi s ((c.J i).obj ((c.S q).obj ((c.J j).obj K))) L ≫
        (c.S s).map (t.delta i ((c.S q).obj ((c.J j).obj K)) ((c.P s).obj L)) ≫
        (c.S s).map ((c.J i).map
          (rawProjection c t j q K ((c.P i).obj ((c.P s).obj L)))) ≫
        (c.S s).map ((c.gamma b q p i h).app
          ((c.J j).obj (normalInput c t j q i s K L))) ≫
        ((c.sComp p s).hom.app
          ((c.J b).obj ((c.J j).obj (normalInput c t j q i s K L))) ≫
        (c.S (p ≫ s)).map ((c.jComp j b).hom.app (normalInput c t j q i s K L))) := by
  simp only [normalLeft, normalInput, rawProjection, compact, alpha_component,
    Functor.comp_obj, Functor.comp_map, Category.assoc]

private theorem left_expansion (hn : Naturality c t)
    {X V W Y B Z : G} (j : X ⟶ V) (b : V ⟶ W)
    (q : V ⟶ Y) (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion (geo.map j)] [IsOpenImmersion (geo.map b)]
    [IsOpenImmersion (geo.map i)] [QuasiCompact (geo.map b)]
    [QuasiCompact (geo.map i)] [IsProper (geo.map q)] [IsProper (geo.map p)]
    (h : b ≫ p = q ≫ i) (K : c.D X) (L : c.D Z) :
    leftMap c t j b q p i s h K L = normalLeft c t j b q p i s h K L ≫
      (compact c (j ≫ b) (p ≫ s)).map (tr c t K (leftTransport c j b q p i s h L)) := by
  dsimp only [leftMap]
  rw [projection_raw c t i s]
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [← Functor.map_comp,
    projection_naturality_right c t hn j q K ((c.pComp i s).inv.app L),
    Functor.map_comp]
  rw [projection_raw c t j q]
  simp only [Functor.map_comp, Category.assoc]
  slice_lhs 3 4 => rw [← Functor.map_comp, ← Functor.map_comp, ← tr_comp]
  simp only [Category.assoc]
  erw [reassoc_of% (alpha c j b q p i s h).naturality
    (tr c t K ((c.pComp j q).inv.app ((c.P i).obj ((c.P s).obj L)) ≫
      (c.P (j ≫ q)).map ((c.pComp i s).inv.app L)))]
  dsimp only [normalLeft, leftTransport]
  simp only [tr_comp, Functor.map_comp, Category.assoc]
  rfl

private structure Compositions : Prop where
  pi : ∀ {X Y Z : G} (f : X ⟶ Y) (g : Y ⟶ Z) (M : c.D X) (L : c.D Z),
    t.pi g ((c.S f).obj M) L ≫
      (c.S g).map (t.pi f M ((c.P g).obj L) ≫
        (c.S f).map (tr c t M ((c.pComp f g).inv.app L))) ≫
      (c.sComp f g).hom.app ((t.tensor X).obj (M, (c.P (f ≫ g)).obj L)) =
    (t.tensor Z).map (Prod.mkHom ((c.sComp f g).hom.app M) (𝟙 L)) ≫
      t.pi (f ≫ g) M L
  delta : ∀ {X Y Z : G} (j : X ⟶ Y) (b : Y ⟶ Z)
    [IsOpenImmersion (geo.map j)] [IsOpenImmersion (geo.map b)]
    (K : c.D X) (N : c.D Z),
    t.delta b ((c.J j).obj K) N ≫ (c.J b).map (t.delta j K ((c.P b).obj N)) ≫
      (c.jComp j b).hom.app ((t.tensor X).obj (K, (c.P j).obj ((c.P b).obj N))) ≫
      (c.J (j ≫ b)).map (tr c t K ((c.pComp j b).inv.app N)) =
    (t.tensor Z).map (Prod.mkHom ((c.jComp j b).hom.app K) (𝟙 N)) ≫
      t.delta (j ≫ b) K N

private def square {V W Y B : G} (b : V ⟶ W) (q : V ⟶ Y)
    (p : W ⟶ B) (i : Y ⟶ B) (h : b ≫ p = q ≫ i) :
    c.P i ⋙ c.P q ≅ c.P p ⋙ c.P b :=
  (c.pComp q i).symm ≪≫ c.pCongr h.symm ≪≫ c.pComp b p

private def rightTransport {X V W Y B Z : G} (j : X ⟶ V) (b : V ⟶ W)
    (q : V ⟶ Y) (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    (h : b ≫ p = q ≫ i) (L : c.D Z) :=
  (c.P j).map ((square c b q p i h).hom.app ((c.P s).obj L)) ≫
    (c.pComp j b).inv.app ((c.P p).obj ((c.P s).obj L)) ≫
    (c.P (j ≫ b)).map ((c.pComp p s).inv.app L) ≫
    (c.pComp (j ≫ b) (p ≫ s)).inv.app L

private theorem open_contract (hn : Naturality c t) (hc : Compositions c t)
    {X V W : G} (j : X ⟶ V) (b : V ⟶ W)
    [IsOpenImmersion (geo.map j)] [IsOpenImmersion (geo.map b)]
    (K : c.D X) (N : c.D W) {A : c.D V} (a : A ≅ (c.P b).obj N)
    {R : c.D X} (v : (c.P (j ≫ b)).obj N ⟶ R) :
    t.delta b ((c.J j).obj K) N ≫
      (c.J b).map (tr c t ((c.J j).obj K) a.inv) ≫
      (c.J b).map (t.delta j K A) ≫
      (c.jComp j b).hom.app ((t.tensor X).obj (K, (c.P j).obj A)) ≫
      (c.J (j ≫ b)).map (tr c t K
        ((c.P j).map a.hom ≫ (c.pComp j b).inv.app N ≫ v)) =
    (t.tensor W).map (Prod.mkHom ((c.jComp j b).hom.app K) (𝟙 N)) ≫
      t.delta (j ≫ b) K N ≫ (c.J (j ≫ b)).map (tr c t K v) := by
  simp only [tr_comp, Functor.map_comp]
  erw [← reassoc_of% (c.jComp j b).hom.naturality
    (tr c t K ((c.P j).map a.hom))]
  slice_lhs 3 4 => rw [← Functor.map_comp, ← hn.delta]
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [← Functor.map_comp, ← Category.assoc, ← tr_comp,
    a.inv_hom_id, tr_id, Category.id_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hc.delta j b K N]

private def normalRight {X V W Y B Z : G} (j : X ⟶ V) (b : V ⟶ W)
    (q : V ⟶ Y) (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion (geo.map j)] [IsOpenImmersion (geo.map b)]
    [IsOpenImmersion (geo.map i)] [QuasiCompact (geo.map b)]
    [QuasiCompact (geo.map i)] [IsProper (geo.map q)] [IsProper (geo.map p)]
    (h : b ≫ p = q ≫ i) (K : c.D X) (L : c.D Z) :=
  tf c t ((c.S s).map ((c.gamma b q p i h).app ((c.J j).obj K))) L ≫
    t.pi s ((c.S p).obj ((c.J b).obj ((c.J j).obj K))) L ≫
    (c.S s).map (t.pi p ((c.J b).obj ((c.J j).obj K)) ((c.P s).obj L)) ≫
    (c.S s).map ((c.S p).map
      (t.delta b ((c.J j).obj K) ((c.P p).obj ((c.P s).obj L)) ≫
        (c.J b).map (tr c t ((c.J j).obj K)
          ((square c b q p i h).inv.app ((c.P s).obj L))) ≫
        (c.J b).map (t.delta j K ((c.P q).obj ((c.P i).obj ((c.P s).obj L)))))) ≫
    (c.sComp p s).hom.app ((c.J b).obj ((c.J j).obj
      (normalInput c t j q i s K L))) ≫
    (c.S (p ≫ s)).map ((c.jComp j b).hom.app (normalInput c t j q i s K L))

private theorem tensor_cross {X : G} {M M' N N' : c.D X}
    (a : M ⟶ M') (b : N ⟶ N') :
    tf c t a N ≫ tr c t M' b = tr c t M b ≫ tf c t a N' := by
  dsimp only [tf, tr]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext <;> simp

private theorem proper_contract (hc : Compositions c t)
    {X Y Z : G} (p : X ⟶ Y) (s : Y ⟶ Z) (M : c.D X) (L : c.D Z) :
    t.pi s ((c.S p).obj M) L ≫
      (c.S s).map (t.pi p M ((c.P s).obj L)) ≫
      (c.sComp p s).hom.app ((t.tensor X).obj (M, (c.P p).obj ((c.P s).obj L))) ≫
      (c.S (p ≫ s)).map (tr c t M ((c.pComp p s).inv.app L)) =
    tf c t ((c.sComp p s).hom.app M) L ≫ t.pi (p ≫ s) M L := by
  slice_lhs 3 4 => erw [← (c.sComp p s).hom.naturality
    (tr c t M ((c.pComp p s).inv.app L))]
  simpa only [Functor.comp_map, Functor.map_comp, Category.assoc, tf] using hc.pi p s M L

private theorem right_expansion (hn : Naturality c t) (hc : Compositions c t)
    {X V W Y B Z : G} (j : X ⟶ V) (b : V ⟶ W) (q : V ⟶ Y)
    (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion (geo.map j)] [IsOpenImmersion (geo.map b)]
    [IsOpenImmersion (geo.map i)] [QuasiCompact (geo.map b)]
    [QuasiCompact (geo.map i)] [IsProper (geo.map q)] [IsProper (geo.map p)]
    (h : b ≫ p = q ≫ i) (K : c.D X) (L : c.D Z) :
    normalRight c t j b q p i s h K L ≫
      (compact c (j ≫ b) (p ≫ s)).map
        (tr c t K (rightTransport c j b q p i s h L)) =
      rightMap c t j b q p i s h K L := by
  let a := (square c b q p i h).app ((c.P s).obj L)
  let v := (c.P (j ≫ b)).map ((c.pComp p s).inv.app L) ≫
    (c.pComp (j ≫ b) (p ≫ s)).inv.app L
  have ho := open_contract c t hn hc j b K ((c.P p).obj ((c.P s).obj L)) a v
  dsimp only [normalRight, normalInput, compact, Functor.comp_map]
  simp only [Category.assoc]
  slice_lhs 4 5 => erw [(c.sComp p s).hom.naturality]
  simp only [Category.assoc]
  slice_lhs 5 7 => rw [← (c.S (p ≫ s)).map_comp, ← (c.S (p ≫ s)).map_comp]
  dsimp only [a, v, Iso.app_inv, Iso.app_hom, Functor.comp_obj] at ho
  dsimp only [rightTransport]
  simp only [Category.assoc]
  rw [ho]
  simp only [tr_comp, Functor.map_comp]
  slice_lhs 6 7 => rw [← (c.S (p ≫ s)).map_comp, ← hn.delta]
  simp only [Functor.map_comp, Category.assoc]
  slice_lhs 5 6 => rw [← (c.S (p ≫ s)).map_comp, ← tf, tensor_cross, Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% proper_contract c t hc]
  dsimp only [rightMap]
  rw [alpha_component]
  conv_rhs => rw [← tf]
  simp only [tf_comp, projection, Functor.map_comp, Category.assoc]
  dsimp only [tf]
  rw [reassoc_of% hn.pi_first (p ≫ s) ((c.jComp j b).hom.app K) L]
  simp only [tr]

private def MateEquation : Prop :=
  ∀ {V W Y B : G} (b : V ⟶ W) (q : V ⟶ Y) (p : W ⟶ B) (i : Y ⟶ B)
    [IsOpenImmersion (geo.map b)] [IsOpenImmersion (geo.map i)]
    [QuasiCompact (geo.map b)] [QuasiCompact (geo.map i)]
    [IsProper (geo.map q)] [IsProper (geo.map p)]
    (h : b ≫ p = q ≫ i) (M : c.D V) (T : c.D B),
    t.delta i ((c.S q).obj M) T ≫
      (c.J i).map (t.pi q M ((c.P i).obj T)) ≫
      (c.J i).map ((c.S q).map (tr c t M ((square c b q p i h).hom.app T))) ≫
      (c.gamma b q p i h).app
        ((t.tensor V).obj (M, (c.P b).obj ((c.P p).obj T))) =
    tf c t ((c.gamma b q p i h).app M) T ≫
      t.pi p ((c.J b).obj M) T ≫
      (c.S p).map (t.delta b M ((c.P p).obj T))

private theorem normal_from_mate (hn : Naturality c t) (hm : MateEquation c t)
    {X V W Y B Z : G} (j : X ⟶ V) (b : V ⟶ W) (q : V ⟶ Y)
    (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion (geo.map j)] [IsOpenImmersion (geo.map b)]
    [IsOpenImmersion (geo.map i)] [QuasiCompact (geo.map b)]
    [QuasiCompact (geo.map i)] [IsProper (geo.map q)] [IsProper (geo.map p)]
    (h : b ≫ p = q ≫ i) (K : c.D X) (L : c.D Z) :
    normalLeft c t j b q p i s h K L = normalRight c t j b q p i s h K L := by
  let M := (c.J j).obj K
  let T := (c.P s).obj L
  let gamma := c.gamma b q p i h
  let a := ((Functor.curryObj (t.tensor V)).obj M).mapIso
    ((square c b q p i h).app T)
  let v := t.delta j K ((c.P q).obj ((c.P i).obj T))
  have hh := hm b q p i h M T
  have hp := (hn.pi_first s (gamma.app M) L).symm
  have hw := triangle_calculation (c.S q) (c.J i) (c.J b) (c.S p) (c.S s) gamma a v
    (t.delta i ((c.S q).obj M) T) (t.pi q M ((c.P i).obj T))
    (tf c t (gamma.app M) T) (t.pi p ((c.J b).obj M) T)
    (t.delta b M ((c.P p).obj T))
    (t.pi s ((c.J i).obj ((c.S q).obj M)) L)
    (tf c t ((c.S s).map (gamma.app M)) L)
    (t.pi s ((c.S p).obj ((c.J b).obj M)) L)
    ((c.sComp p s).hom.app ((c.J b).obj ((c.J j).obj
        (normalInput c t j q i s K L))) ≫
      (c.S (p ≫ s)).map ((c.jComp j b).hom.app (normalInput c t j q i s K L)))
    (by
      dsimp only [a, gamma, Functor.mapIso_hom, Iso.app_hom, Functor.comp_obj,
        Functor.curryObj, tr]
      exact hh) hp
  rw [normalLeft_native]
  dsimp only [normalRight, rawProjection, a, v, gamma, M, T,
    Functor.mapIso_inv, Iso.app_inv, Functor.comp_obj, Functor.curryObj] at hw ⊢
  exact hw

private def PullAssociative : Prop :=
  ∀ {X Y Z T : G} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (L : c.D T),
    (c.pComp (f ≫ g) h).hom.app L ≫ (c.pComp f g).hom.app ((c.P h).obj L) =
      (c.pCongr (Category.assoc f g h)).hom.app L ≫
        (c.pComp f (g ≫ h)).hom.app L ≫ (c.P f).map ((c.pComp g h).hom.app L)

private theorem collapse_assoc (hp : PullAssociative c)
    {X Y Z T : G} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (L : c.D T) :
    (c.P f).map ((c.pComp g h).inv.app L) ≫ (c.pComp f (g ≫ h)).inv.app L =
      (c.pComp f g).inv.app ((c.P h).obj L) ≫
        (c.pComp (f ≫ g) h).inv.app L ≫
        (c.pCongr (Category.assoc f g h)).hom.app L := by
  apply (cancel_epi ((c.pComp (f ≫ g) h).hom.app L ≫
    (c.pComp f g).hom.app ((c.P h).obj L))).1
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% hp f g h L]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

private theorem collapse_transport {A B Z : G} {f g : A ⟶ B}
    (h : f = g) (s : B ⟶ Z) {r : A ⟶ Z} (e : g ≫ s = r) (L : c.D Z) :
    (c.pCongr h).hom.app ((c.P s).obj L) ≫
      (c.pComp g s).inv.app L ≫ (c.pCongr e).hom.app L =
    (c.pComp f s).inv.app L ≫
      (c.pCongr ((congrArg (fun a ↦ a ≫ s) h).trans e)).hom.app L := by
  cases h
  simp only [Calculus.pCongr, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp]

private theorem collapse_second_transport {X Y Z : G} (f : X ⟶ Y)
    {g h : Y ⟶ Z} (e : g = h) (L : c.D Z) :
    (c.P f).map ((c.pCongr e).hom.app L) ≫ (c.pComp f h).inv.app L =
      (c.pComp f g).inv.app L ≫
        (c.pCongr (congrArg (fun a ↦ f ≫ a) e)).hom.app L := by
  cases e
  simp only [Calculus.pCongr, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

private theorem collapse_four (hp : PullAssociative c)
    {X V Y B Z : G} (j : X ⟶ V) (q : V ⟶ Y) (i : Y ⟶ B) (s : B ⟶ Z)
    {r : X ⟶ Z} (e : (j ≫ q) ≫ (i ≫ s) = r)
    (e' : (j ≫ (q ≫ i)) ≫ s = r) (L : c.D Z) :
    (c.pComp j q).inv.app ((c.P i).obj ((c.P s).obj L)) ≫
      (c.P (j ≫ q)).map ((c.pComp i s).inv.app L) ≫
      (c.pComp (j ≫ q) (i ≫ s)).inv.app L ≫ (c.pCongr e).hom.app L =
    (c.P j).map ((c.pComp q i).inv.app ((c.P s).obj L)) ≫
      (c.pComp j (q ≫ i)).inv.app ((c.P s).obj L) ≫
      (c.pComp (j ≫ (q ≫ i)) s).inv.app L ≫ (c.pCongr e').hom.app L := by
  rw [reassoc_of% collapse_assoc c hp (j ≫ q) i s L]
  have ht : (c.pCongr (Category.assoc (j ≫ q) i s)).hom.app L ≫
      (c.pCongr e).hom.app L =
      (c.pCongr ((Category.assoc (j ≫ q) i s).trans e)).hom.app L := by
    simp only [Calculus.pCongr, eqToIso.hom, eqToHom_app, eqToHom_trans]
  rw [ht]
  have hr := collapse_transport c (Category.assoc j q i) s e' L
  have hl := collapse_assoc c hp j q i ((c.P s).obj L)
  rw [← hr]
  rw [← reassoc_of% hl]

private theorem transport_equation (hp : PullAssociative c)
    {X V W Y B Z : G} (j : X ⟶ V) (b : V ⟶ W) (q : V ⟶ Y)
    (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    (h : b ≫ p = q ≫ i) (L : c.D Z) :
    leftTransport c j b q p i s h L = rightTransport c j b q p i s h L := by
  let e : (j ≫ q) ≫ (i ≫ s) = (j ≫ b) ≫ (p ≫ s) := by
    calc
      (j ≫ q) ≫ (i ≫ s) = j ≫ ((q ≫ i) ≫ s) := by simp only [Category.assoc]
      _ = j ≫ ((b ≫ p) ≫ s) := congrArg (fun a ↦ j ≫ (a ≫ s)) h.symm
      _ = (j ≫ b) ≫ (p ≫ s) := by simp only [Category.assoc]
  let e' : (j ≫ (q ≫ i)) ≫ s = (j ≫ b) ≫ (p ≫ s) := by
    simpa only [Category.assoc] using e
  dsimp only [leftTransport, trianglePull, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [collapse_four c hp j q i s e e' L]
  dsimp only [rightTransport, square, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  have er : (j ≫ (b ≫ p)) ≫ s = (j ≫ b) ≫ (p ≫ s) := by
    simp only [Category.assoc]
  have hr4 := collapse_four c hp j b p s rfl er L
  simp only [Calculus.pCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.comp_id] at hr4
  rw [hr4]
  slice_rhs 3 4 => rw [← Functor.map_comp, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, Category.assoc]
  rw [reassoc_of% collapse_second_transport c j h.symm ((c.P s).obj L)]
  erw [collapse_transport c (congrArg (fun a ↦ j ≫ a) h.symm) s er L]

private theorem contract_normal (hn : Naturality c t) (hc : Compositions c t)
    (hp : PullAssociative c)
    {X V W Y B Z : G} (j : X ⟶ V) (b : V ⟶ W) (q : V ⟶ Y)
    (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion (geo.map j)] [IsOpenImmersion (geo.map b)]
    [IsOpenImmersion (geo.map i)] [QuasiCompact (geo.map b)]
    [QuasiCompact (geo.map i)] [IsProper (geo.map q)] [IsProper (geo.map p)]
    (h : b ≫ p = q ≫ i) (K : c.D X) (L : c.D Z)
    (he : normalLeft c t j b q p i s h K L = normalRight c t j b q p i s h K L) :
    leftMap c t j b q p i s h K L = rightMap c t j b q p i s h K L := by
  rw [left_expansion c t hn, he, transport_equation c hp]
  exact right_expansion c t hn hc j b q p i s h K L

private theorem projection_composition_uncurried
    {B C Y : Type*} [Category B] [Category C] [Category Y]
    {P : Y ⥤ C} {R : C ⥤ Y} {Q : C ⥤ B} {S : B ⥤ C}
    {H : Y ⥤ B} {V : B ⥤ Y}
    (adj : P ⊣ R) (adj' : Q ⊣ S) (adjH : H ⊣ V)
    (TB : B ⥤ B ⥤ B) (TC : C ⥤ C ⥤ C) (TY : Y ⥤ Y ⥤ Y)
    (t : (Functor.postcompose₂.obj P).obj TY ⟶
      (((Functor.whiskeringLeft₂ C).obj P).obj P).obj TC)
    (q : (Functor.postcompose₂.obj Q).obj TC ⟶
      (((Functor.whiskeringLeft₂ B).obj Q).obj Q).obj TB)
    (h : (Functor.postcompose₂.obj H).obj TY ⟶
      (((Functor.whiskeringLeft₂ B).obj H).obj H).obj TB)
    (e : H ≅ P ⋙ Q)
    (he : ∀ M N, e.hom.app ((TY.obj M).obj N) ≫
      Q.map ((t.app M).app N) ≫ (q.app (P.obj M)).app (P.obj N) =
      (h.app M).app N ≫ (TB.map (e.hom.app M)).app (H.obj N) ≫
        (TB.obj (Q.obj (P.obj M))).map (e.hom.app N))
    (M : B) (L : Y) :
    ((adj.rightAdjointProjectionMap t).app (S.obj M)).app L ≫
      R.map (((adj'.rightAdjointProjectionMap q).app M).app (P.obj L) ≫
        S.map ((Functor.uncurry.obj TB).map (Prod.mkHom (𝟙 M) (e.inv.app L)))) ≫
      (conjugateIsoEquiv (adj.comp adj') adjH e).hom.app
        ((Functor.uncurry.obj TB).obj (M, H.obj L)) =
    (Functor.uncurry.obj TY).map
      (Prod.mkHom ((conjugateIsoEquiv (adj.comp adj') adjH e).hom.app M) (𝟙 L)) ≫
      ((adjH.rightAdjointProjectionMap h).app M).app L := by
  simpa only [Functor.uncurry_obj_map, Functor.uncurry_obj_obj,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, Category.comp_id] using
    RefinementProjection.projection_composition_normalized
      adj adj' adjH TB TC TY t q h e he M L

private theorem composition_pi_from_curried
    (T : ∀ X : G, c.D X ⥤ c.D X ⥤ c.D X)
    (q : ∀ {X Y : G} (f : X ⟶ Y),
      (Functor.postcompose₂.obj (c.P f)).obj (T Y) ⟶
        (((Functor.whiskeringLeft₂ (c.D X)).obj (c.P f)).obj (c.P f)).obj (T X))
    (ht : ∀ X, t.tensor X = Functor.uncurry.obj (T X))
    (hpi : ∀ {X Y : G} (f : X ⟶ Y) (M : c.D X) (N : c.D Y),
      HEq (t.pi f M N) ((((c.adj f).rightAdjointProjectionMap (q f)).app M).app N))
    (hq : ∀ {X Y Z : G} (f : X ⟶ Y) (g : Y ⟶ Z) (M N : c.D Z),
      (c.pComp f g).hom.app (((T Z).obj M).obj N) ≫
        (c.P f).map (((q g).app M).app N) ≫
        ((q f).app ((c.P g).obj M)).app ((c.P g).obj N) =
      ((q (f ≫ g)).app M).app N ≫
        ((T X).map ((c.pComp f g).hom.app M)).app ((c.P (f ≫ g)).obj N) ≫
        ((T X).obj ((c.P f).obj ((c.P g).obj M))).map ((c.pComp f g).hom.app N))
    {X Y Z : G} (f : X ⟶ Y) (g : Y ⟶ Z) (M : c.D X) (L : c.D Z) :
    t.pi g ((c.S f).obj M) L ≫
      (c.S g).map (t.pi f M ((c.P g).obj L) ≫
        (c.S f).map (tr c t M ((c.pComp f g).inv.app L))) ≫
      (c.sComp f g).hom.app ((t.tensor X).obj (M, (c.P (f ≫ g)).obj L)) =
    (t.tensor Z).map (Prod.mkHom ((c.sComp f g).hom.app M) (𝟙 L)) ≫
      t.pi (f ≫ g) M L := by
  rcases t with ⟨tensor, pi, delta⟩
  dsimp only at ht hpi ⊢
  have ht' : tensor = fun X ↦ Functor.uncurry.obj (T X) := funext ht
  subst tensor
  have hh : ∀ {X Y : G} (f : X ⟶ Y) (M : c.D X) (N : c.D Y),
      pi f M N = (((c.adj f).rightAdjointProjectionMap (q f)).app M).app N :=
    fun f M N ↦ eq_of_heq (hpi f M N)
  simp only [hh, tr, Calculus.sComp]
  exact projection_composition_uncurried
    (c.adj g) (c.adj f) (c.adj (f ≫ g)) (T X) (T Y) (T Z)
    (q g) (q f) (q (f ≫ g)) (c.pComp f g) (hq f g) M L

section Finite

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions DerivedCategory
  properOpenMate properOpenAlpha properOpenTensorIso properOpenPullSquareIso
  leftDerivedUpperStarComp leftDerivedUpperStarTensorNatIso
  derivedUpperStarLowerStarAdjunction leftDerivedUpperStarTensorComparison derivedTensor
  rightDerivedLowerStarProjectionMap

variable (F : WeilConjectures.FiniteFieldDatum.{u})
  (A : Type (u + 1)) [CommRing A] [Finite A]

omit [Finite A] in
private theorem pull_congr_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    leftDerivedUpperStarCongr (ModuleCat.{u + 1} A) h =
      eqToIso (congrArg (ProperOpenPull A) h) := by
  cases h
  rfl

private theorem finite_naturality : Naturality (ordinary F A) (ordinaryTensor F A) := by
  constructor
  · intro X Y f M L L' a
    simp [ordinaryTensor, ordinary, tr, properOpenProjection,
      derivedTensorRightDerivedLowerStar,
      rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar]
  · intro X Y f M M' a L
    have h := congr_app ((rightDerivedLowerStarProjectionMap
      (ModuleCat.{u + 1} A) f.hom.left).naturality a) L
    simpa [ordinaryTensor, ordinary, properOpenProjection, Functor.uncurry_obj_map,
      derivedTensorRightDerivedLowerStar,
      rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar] using h
  · intro X Y j hj M L L' a
    let : IsOpenImmersion j.hom.left := hj
    have h := (properOpenDelta A j.hom.left).hom.naturality (Prod.mkHom (𝟙 M) a)
    simpa only [ordinaryTensor, ordinary, tr, properOpenDelta_hom,
      Functor.comp_map, Functor.prod_map, Functor.id_map,
      Functor.comp_obj, Functor.prod_obj, Functor.id_obj, Functor.uncurry_obj_map,
      CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
      Category.comp_id] using h

private theorem ordinary_tensor_first (X : Spaces F)
    {M N : ProperOpenDerived A X.obj.left} (a : M ⟶ N)
    (L : ProperOpenDerived A X.obj.left) :
    tf (ordinary F A) (ordinaryTensor F A) a L =
      ((ProperOpenTensor A X.obj.left).map a).app L := by
  change (Functor.uncurry.obj (ProperOpenTensor A X.obj.left)).map
    (Prod.mkHom a (𝟙 L)) = _
  simp only [Functor.uncurry_obj_map]
  erw [((ProperOpenTensor A X.obj.left).obj N).map_id L]
  exact Category.comp_id _

private theorem ordinary_tensor_second (X : Spaces F)
    (K : ProperOpenDerived A X.obj.left) {M N : ProperOpenDerived A X.obj.left}
    (a : M ⟶ N) :
    tr (ordinary F A) (ordinaryTensor F A) K a =
      ((ProperOpenTensor A X.obj.left).obj K).map a := by
  change (Functor.uncurry.obj (ProperOpenTensor A X.obj.left)).map
    (Prod.mkHom (𝟙 K) a) = _
  simp only [Functor.uncurry_obj_map]
  erw [(ProperOpenTensor A X.obj.left).map_id K, NatTrans.id_app]
  exact Category.id_comp _

private theorem finite_projection_eq {X Y : Spaces F} (f : X ⟶ Y)
    (M : ProperOpenDerived A X.obj.left) (N : ProperOpenDerived A Y.obj.left) :
    (ordinaryTensor F A).pi f M N =
      ((((ordinary F A).adj f).rightAdjointProjectionMap
        (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f.hom.left)).app M).app N := by
  unfold ordinaryTensor ordinary properOpenProjection rightDerivedLowerStarProjectionMap
  rfl

private theorem finite_tensor_uncurry :
    ∀ X : Spaces F, (ordinaryTensor F A).tensor X =
      Functor.uncurry.obj (ProperOpenTensor A X.obj.left) := by
  intro X
  rfl

private theorem finite_projection_heq :
    ∀ {X Y : Spaces F} (f : X ⟶ Y) (M : (ordinary F A).D X)
      (N : (ordinary F A).D Y),
    HEq ((ordinaryTensor F A).pi f M N)
      (((((ordinary F A).adj f).rightAdjointProjectionMap
        (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f.hom.left)).app M).app N)
      := by
  intro X Y f M N
  exact heq_of_eq (finite_projection_eq F A f M N)

private theorem finite_tensor_comparison (ht : OrdinaryTensorComposition F A) :
    ∀ {X Y Z : Spaces F} (f : X ⟶ Y) (g : Y ⟶ Z)
      (M N : (ordinary F A).D Z),
    ((ordinary F A).pComp f g).hom.app
        (((ProperOpenTensor A Z.obj.left).obj M).obj N) ≫
      ((ordinary F A).P f).map
        (((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) g.hom.left).app M).app N) ≫
      ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f.hom.left).app
        (((ordinary F A).P g).obj M)).app (((ordinary F A).P g).obj N) =
    ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) (f ≫ g).hom.left).app M).app N ≫
      ((ProperOpenTensor A X.obj.left).map
        (((ordinary F A).pComp f g).hom.app M)).app (((ordinary F A).P (f ≫ g)).obj N) ≫
      ((ProperOpenTensor A X.obj.left).obj
        (((ordinary F A).P f).obj (((ordinary F A).P g).obj M))).map
          (((ordinary F A).pComp f g).hom.app N) := by
  intro X Y Z f g M N
  rw [← RefinementProjection.tensor_component_hom A g.hom.left M N,
    ← RefinementProjection.tensor_component_hom A f.hom.left
      (((ordinary F A).P g).obj M) (((ordinary F A).P g).obj N),
    ← RefinementProjection.tensor_component_hom A (f ≫ g).hom.left M N]
  exact ht f g M N

private theorem finite_compositions (ht : OrdinaryTensorComposition F A) :
    Compositions (ordinary F A) (ordinaryTensor F A) := by
  constructor
  · intro X Y Z f g M L
    exact composition_pi_from_curried (ordinary F A) (ordinaryTensor F A)
      (fun X ↦ ProperOpenTensor A X.obj.left)
      (fun f ↦ leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f.hom.left)
      (finite_tensor_uncurry F A) (finite_projection_heq F A)
      (finite_tensor_comparison F A ht)
      f g M L
  · intro X Y Z j b hj hb K N
    let : IsOpenImmersion j.hom.left := hj
    let : IsOpenImmersion b.hom.left := hb
    have h := properOpenTensor_comp A j.hom.left b.hom.left K N
    simpa only [ordinaryTensor, ordinary, tr, Calculus.jComp, properOpenShriekComp,
      ObjectProperty.FullSubcategory.comp_hom, Over.comp_left, Functor.uncurry_obj_obj,
      NatTrans.id_app, Category.id_comp,
      Functor.uncurry_obj_map, CategoryTheory.Functor.map_id, Category.comp_id] using h

private theorem finite_normal
    {X V W Y B Z : Spaces F} (j : X ⟶ V) (b : V ⟶ W) (q : V ⟶ Y)
    (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion ((geometry F).map j)] [IsOpenImmersion ((geometry F).map b)]
    [IsOpenImmersion ((geometry F).map i)] [QuasiCompact ((geometry F).map b)]
    [QuasiCompact ((geometry F).map i)] [IsProper ((geometry F).map q)]
    [IsProper ((geometry F).map p)] [IsProper ((geometry F).map s)]
    (h : b ≫ p = q ≫ i)
    (K : ProperOpenDerived A X.obj.left) (L : ProperOpenDerived A Z.obj.left) :
    normalLeft (ordinary F A) (ordinaryTensor F A) j b q p i s h K L =
      normalRight (ordinary F A) (ordinaryTensor F A) j b q p i s h K L := by
  change @Eq (@Quiver.Hom (ProperOpenDerived A Z.obj.left) inferInstance _ _) _ _
  let : IsOpenImmersion j.hom.left := inferInstanceAs
    (IsOpenImmersion ((geometry F).map j))
  let : IsOpenImmersion b.hom.left := inferInstanceAs
    (IsOpenImmersion ((geometry F).map b))
  let : IsOpenImmersion i.hom.left := inferInstanceAs
    (IsOpenImmersion ((geometry F).map i))
  let : IsProper q.hom.left := inferInstanceAs (IsProper ((geometry F).map q))
  let : IsProper p.hom.left := inferInstanceAs (IsProper ((geometry F).map p))
  let : IsProper s.hom.left := inferInstanceAs (IsProper ((geometry F).map s))
  have gamma_eq : (ordinary F A).gamma b q p i h =
      properOpenMate A
        b.hom.left q.hom.left p.hom.left i.hom.left
        (congrArg (fun f ↦ f.hom.left) h) := by
    unfold Calculus.gamma ordinary properOpenMate
    rfl
  have jc : (ordinary F A).jComp j b =
      properOpenShriekComp A j.hom.left b.hom.left := by
    unfold Calculus.jComp ordinary properOpenShriekComp
    rfl
  have sq : square (ordinary F A) b q p i h =
      properOpenPullSquareIso A b.hom.left q.hom.left p.hom.left i.hom.left
        (congrArg (fun f ↦ f.hom.left) h) := by
    simp only [square, Calculus.pCongr, ordinary, properOpenPullSquareIso,
      leftDerivedUpperStarSquareIso, pull_congr_eq,
      ObjectProperty.FullSubcategory.comp_hom, Over.comp_left]
  have H := TriangleProjection.finite_normalForm F A j b i q p s h K L
  rw [normalLeft_native]
  unfold normalRight rawProjection
  rw [gamma_eq, jc, sq]
  simp only [ordinary_tensor_first, ordinary_tensor_second]
  exact H

private theorem finite_equations (ht : OrdinaryTensorComposition F A)
    (hp : PullAssociative (ordinary F A)) :
    TriangleEquations (ordinary F A) (ordinaryTensor F A) := by
  intro X V W Y B Z j b q p i s hj hb hi hqb hqi hq hp' hs h K L
  apply contract_normal _ _ (finite_naturality F A) (finite_compositions F A ht) hp
  exact finite_normal F A j b q p i s h K L

end Finite

section Systems

open WeilConjectures.IntegralSystemRealization

attribute [local irreducible] WeilConjectures.pullbackTensorCalculus
  WeilConjectures.pullbackTensorSequenceDerived HasDerivedCategory.standard
  Functor.leftAdjoint Functor.mapDerivedCategory DerivedCategory
  WeilConjectures.CoefficientClosedStructure.tensor properProjection
attribute [local implicit_reducible] WeilConjectures.coefficientSequenceHasDerived
  WeilConjectures.SemilinearSections.moduleAbelian
attribute [local implicit_reducible] realizedSystems realizedTensor openTensorLeft openTensorRight
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived

variable (F : WeilConjectures.FiniteFieldDatum.{u})
  (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (o : Operations l E) (z : Realizations l E F o)

private theorem system_naturality :
    Naturality (realizedSystems F l E o z) (realizedTensor F l E o z) := by
  constructor
  · intro X Y f M L L' a
    have h := ((properProjection l E o f.hom.left).app M).naturality a
    simpa [realizedTensor, realizedSystems, tr, Functor.comp_map, Functor.curryObj]
      using h
  · intro X Y f M M' a L
    have h := congr_app ((properProjection l E o f.hom.left).naturality a) L
    simpa [realizedTensor, realizedSystems, Functor.comp_map, Functor.curryObj]
      using h
  · intro X Y j hj M L L' a
    let : IsOpenImmersion j.hom.left := hj
    have h := (z.openComparisons.projection j.hom.left).hom.naturality (Prod.mkHom (𝟙 M) a)
    simpa only [realizedTensor, realizedSystems, tr, openTensorLeft, openTensorRight,
      Functor.comp_map, Functor.prod_map, Functor.id_map,
      Functor.comp_obj, Functor.prod_obj, Functor.id_obj,
      CategoryTheory.Functor.map_id] using h

private theorem system_open_comp (ht : SystemTensorComposition F l E o z.compositors)
    {X Y Z : Spaces F} (j : X ⟶ Y) (b : Y ⟶ Z)
    [IsOpenImmersion j.hom.left] [IsOpenImmersion b.hom.left]
    (M : System l E X.obj.left) (N : System l E Z.obj.left) :
    (z.openComparisons.projection b.hom.left).hom.app
        ((Operations.shriek l E o j.hom.left).obj M, N) ≫
      (Operations.shriek l E o b.hom.left).map
        ((z.openComparisons.projection j.hom.left).hom.app
          (M, (pull l E b.hom.left).obj N)) ≫
      (z.compositors.openComp l E j.hom.left b.hom.left).hom.app
        ((calculus l E X.obj.left).systemClosed.tensor.obj
          (M, (pull l E j.hom.left).obj ((pull l E b.hom.left).obj N))) ≫
      (Operations.shriek l E o (j.hom.left ≫ b.hom.left)).map
        ((calculus l E X.obj.left).systemClosed.tensor.map
          (Prod.mkHom (𝟙 M) ((z.compositors.pullComp j.hom.left b.hom.left).inv.app N))) =
    (calculus l E Z.obj.left).systemClosed.tensor.map
        (Prod.mkHom ((z.compositors.openComp l E j.hom.left b.hom.left).hom.app M) (𝟙 N)) ≫
      (z.openComparisons.projection (j.hom.left ≫ b.hom.left)).hom.app (M, N) := by
  delta openTensorLeft openTensorRight
  dsimp only [Functor.comp_obj,
    Functor.prod_obj, Functor.id_obj]
  let L := Operations.shriek l E o j.hom.left
  let B := Operations.shriek l E o b.hom.left
  let S := pull l E j.hom.left
  let R := pull l E b.hom.left
  let U' := (calculus l E X.obj.left).systemClosed.tensor
  let T := (calculus l E Y.obj.left).systemClosed.tensor
  let W := (calculus l E Z.obj.left).systemClosed.tensor
  let a := (o.extension j.hom.left).adj
  let ab := (o.extension b.hom.left).adj
  let a' := (o.extension (j.hom.left ≫ b.hom.left)).adj
  let muS := WeilConjectures.pullbackTensorSystemComparison l E j.hom.left
  let muR := WeilConjectures.pullbackTensorSystemComparison l E b.hom.left
  let mu' := WeilConjectures.pullbackTensorSystemComparison l E (j.hom.left ≫ b.hom.left)
  let mu := tensorComparisonComp S R U' T W muS muR
  let delta := openTensorComp L S B R U' T W
    (z.openComparisons.projection j.hom.left) (z.openComparisons.projection b.hom.left)
  let e := z.compositors.openComp l E j.hom.left b.hom.left
  let c := (z.compositors.pullComp j.hom.left b.hom.left).symm
  have he (H : System l E X.obj.left) :
      (a.comp ab).unit.app H ≫ c.hom.app ((L ⋙ B).obj H) =
        a'.unit.app H ≫ (pull l E (j.hom.left ≫ b.hom.left)).map (e.inv.app H) := by
    simpa only [a, ab, a', e, c, Compositors.openComp,
      Adjunction.conjugateEquiv_leftAdjointCompIso_inv] using
      unit_conjugateEquiv (a.comp ab) a' e.inv H
  have hc (H V' : System l E Z.obj.left) :
      mu.inv.app (H, V') ≫ c.hom.app (W.obj (H, V')) =
        U'.map (Prod.mkHom (c.hom.app H) (c.hom.app V')) ≫ mu'.inv.app (H, V') := by
    apply (cancel_epi (mu.hom.app (H, V'))).1
    simp -implicitDefEqProofs only [Iso.hom_inv_id_app_assoc]
    apply (cancel_mono (mu'.hom.app (H, V'))).1
    simp -implicitDefEqProofs only [Category.assoc, Iso.inv_hom_id_app]
    have hh := ht j b H V'
    dsimp only [mu, tensorComparisonComp, NatIso.ofComponents, Iso.trans_hom,
      Functor.mapIso_hom, Iso.app_hom]
    apply (cancel_epi ((z.compositors.pullComp j.hom.left b.hom.left).hom.app
      (W.obj (H, V')))).1
    simp -implicitDefEqProofs only [c, Iso.symm_hom, Iso.hom_inv_id_app_assoc]
    dsimp only [S, R, U', W, muS, muR, mu']
    simp -implicitDefEqProofs only [Category.assoc]
    erw [Category.comp_id]
    rw [reassoc_of% hh]
    rw [← U'.map_comp]
    have hp :
        Prod.mkHom ((z.compositors.pullComp j.hom.left b.hom.left).hom.app H)
          ((z.compositors.pullComp j.hom.left b.hom.left).hom.app V') ≫
        Prod.mkHom ((z.compositors.pullComp j.hom.left b.hom.left).inv.app H)
          ((z.compositors.pullComp j.hom.left b.hom.left).inv.app V') = 𝟙 _ := by
      ext <;> simp
    rw [hp]
    simp [U', ObjectProperty.FullSubcategory.comp_hom, Over.comp_left]
  have hd (H : System l E X.obj.left) (V' : System l E Z.obj.left) :
      (a.comp ab).homEquiv _ _ (delta.inv.app (H, V')) =
        U'.map (Prod.mkHom ((a.comp ab).unit.app H) (𝟙 _)) ≫
          mu.inv.app ((L ⋙ B).obj H, V') := by
    exact open_tensor_composite_transpose L S B R a ab U' T W muS muR
      (z.openComparisons.projection j.hom.left) (z.openComparisons.projection b.hom.left)
      (fun H V' ↦ z.openComparisons.projection_transpose j.hom.left H V')
      (fun H V' ↦ z.openComparisons.projection_transpose b.hom.left H V') H V'
  have hn := open_tensor_transport (L ⋙ B)
    (Operations.shriek l E o (j.hom.left ≫ b.hom.left))
    (R ⋙ S) (pull l E (j.hom.left ≫ b.hom.left)) (a.comp ab) a' W U' mu mu'
    delta (z.openComparisons.projection (j.hom.left ≫ b.hom.left)) e c he hc hd
    (fun H V' ↦ z.openComparisons.projection_transpose (j.hom.left ≫ b.hom.left) H V') M N
  simp only [L, B, S, R, U', T, W, e, c, delta, openTensorComp,
    NatIso.ofComponents, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom,
    Functor.comp_obj, Functor.prod_obj, Functor.id_obj, Category.assoc] at hn ⊢
  convert (closePre := false) (closePost := false) hn using 1

private theorem system_compositions (ht : SystemTensorComposition F l E o z.compositors) :
    Compositions (realizedSystems F l E o z) (realizedTensor F l E o z) := by
  constructor
  · intro X Y Z f g M L
    have h := RefinementProjection.system_comp l E o z.compositors
      f.hom.left g.hom.left (ht f g) (f.hom.left ≫ g.hom.left) rfl M L
    simpa only [realizedTensor, realizedSystems, tr, Calculus.sComp,
      Compositors.pushComp, ObjectProperty.FullSubcategory.comp_hom, Over.comp_left,
      eqToIso_refl, Iso.refl_hom, eqToHom_refl, NatTrans.comp_app, NatTrans.id_app,
      Category.comp_id] using h
  · intro X Y Z j b hj hb M N
    delta realizedSystems realizedTensor openTensorLeft openTensorRight
    dsimp only [tr, Calculus.jComp]
    let : IsOpenImmersion j.hom.left := hj
    let : IsOpenImmersion b.hom.left := hb
    have hh := system_open_comp F l E o z ht j b M N
    simp only [Compositors.openComp, ObjectProperty.FullSubcategory.comp_hom, Over.comp_left,
      openTensorLeft, Functor.comp_obj, Functor.prod_obj, Functor.id_obj] at hh ⊢
    convert (closePre := false) (closePost := false) hh using 1

private theorem system_associative : PullAssociative (realizedSystems F l E o z) := by
  intro X Y Z T f g h M
  have hh := congr_app (congrArg Iso.hom (integralSystemCompositorAssociativity l E
    z.compositors f.hom.left g.hom.left h.hom.left)) M
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hh
  have hc : ((realizedSystems F l E o z).pCongr (Category.assoc f g h)).inv =
      (eqToIso (congrArg (pull l E)
        (Category.assoc f.hom.left g.hom.left h.hom.left).symm)).hom := by
    unfold Calculus.pCongr realizedSystems
    rfl
  apply (cancel_epi
    (((realizedSystems F l E o z).pCongr (Category.assoc f g h)).inv.app M)).1
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  rw [hc, Category.assoc]
  exact hh.symm

private theorem system_gamma {U V W B : Spaces F}
    (b : U ⟶ V) (q : U ⟶ W) (p : V ⟶ B) (i : W ⟶ B)
    [IsOpenImmersion ((geometry F).map b)] [IsOpenImmersion b.hom.left]
    [IsOpenImmersion ((geometry F).map i)] [IsOpenImmersion i.hom.left]
    [QuasiCompact ((geometry F).map b)] [QuasiCompact b.hom.left]
    [QuasiCompact ((geometry F).map i)] [QuasiCompact i.hom.left]
    [IsProper ((geometry F).map q)] [IsProper q.hom.left]
    [IsProper ((geometry F).map p)] [IsProper p.hom.left]
    (h : b ≫ p = q ≫ i) :
    (realizedSystems F l E o z).gamma b q p i h =
      z.properOpen.gamma b.hom.left q.hom.left
        p.hom.left i.hom.left
        (congrArg (fun f ↦ f.hom.left) h) := by
  exact (mateEquiv (o.direct q.hom.left).adj
    (o.direct p.hom.left).adj).apply_symm_apply _

private theorem system_square {U V W B : Spaces F}
    (b : U ⟶ V) (q : U ⟶ W) (p : V ⟶ B) (i : W ⟶ B)
    (h : b ≫ p = q ≫ i) :
    square (realizedSystems F l E o z) b q p i h =
      z.compositors.square l E b.hom.left q.hom.left
        p.hom.left i.hom.left
        (congrArg (fun f ↦ f.hom.left) h) := by
  rfl

attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
  WeilConjectures.SemilinearSections.moduleAbelian in
private theorem system_mate (hl : l ≠ F.p) :
    MateEquation (realizedSystems F l E o z) (realizedTensor F l E o z) := by
  intro V W Y B b q p i hb hi hqb hqi hq hp h M T
  let : IsOpenImmersion b.hom.left := hb
  let : IsOpenImmersion i.hom.left := hi
  let : QuasiCompact b.hom.left := hqb
  let : QuasiCompact i.hom.left := hqi
  let : IsProper q.hom.left := hq
  let : IsProper p.hom.left := hp
  let : V.obj.left.Over (Spec (.of F.k)) := ⟨V.obj.hom⟩
  let : LocallyOfFiniteType (V.obj.left ↘ Spec (.of F.k)) := V.property.1
  let : QuasiCompact (V.obj.left ↘ Spec (.of F.k)) := V.property.2
  let : W.obj.left.Over (Spec (.of F.k)) := ⟨W.obj.hom⟩
  let : LocallyOfFiniteType (W.obj.left ↘ Spec (.of F.k)) := W.property.1
  let : QuasiCompact (W.obj.left ↘ Spec (.of F.k)) := W.property.2
  let : Y.obj.left.Over (Spec (.of F.k)) := ⟨Y.obj.hom⟩
  let : LocallyOfFiniteType (Y.obj.left ↘ Spec (.of F.k)) := Y.property.1
  let : QuasiCompact (Y.obj.left ↘ Spec (.of F.k)) := Y.property.2
  let : B.obj.left.Over (Spec (.of F.k)) := ⟨B.obj.hom⟩
  let : LocallyOfFiniteType (B.obj.left ↘ Spec (.of F.k)) := B.property.1
  let : QuasiCompact (B.obj.left ↘ Spec (.of F.k)) := B.property.2
  let : b.hom.left.IsOver (Spec (.of F.k)) := ⟨b.hom.w⟩
  let : q.hom.left.IsOver (Spec (.of F.k)) := ⟨q.hom.w⟩
  let : p.hom.left.IsOver (Spec (.of F.k)) := ⟨p.hom.w⟩
  let : i.hom.left.IsOver (Spec (.of F.k)) := ⟨i.hom.w⟩
  have hh := properOpenProjectionMateSystems F l hl E o z
    b.hom.left q.hom.left p.hom.left i.hom.left
    (congrArg (fun f ↦ f.hom.left) h) M T
  rw [system_gamma F l E o z, system_square F l E o z]
  simpa only [realizedSystems, realizedTensor, tf, tr, Functor.comp_obj,
    Functor.comp_map] using hh

private theorem system_equations (hl : l ≠ F.p)
    (ht : SystemTensorComposition F l E o z.compositors) :
    TriangleEquations (realizedSystems F l E o z) (realizedTensor F l E o z) := by
  intro X V W Y B Z j b q p i s hj hb hi hqb hqi hq hp hs h K L
  apply contract_normal _ _ (system_naturality F l E o z)
    (system_compositions F l E o z ht) (system_associative F l E o z)
  exact normal_from_mate _ _ (system_naturality F l E o z)
    (system_mate F l E o z hl) j b q p i s h K L

end Systems

/-- Contracting the triangle counit normal form gives the projection equation.
Source: blueprint composition/refinement sentence and Stacks 0F7J
(blueprint: lem-sf-triangle-projection-compositor-contraction).

Proof: expand each compactification projection and each composition comparison.
Naturality moves the inner open tensor map through the proper/open mate. The
triangle normal-form theorem then replaces its left word by its right word,
retaining the successive pullbacks. Combine the two proper projections using
the tensor-composition equation and adjunction conjugation. Combine the two
open tensor maps by transposing under the composite open adjunction: the
recorded open-unit normalization and the tensor-pullback composition equation
make their transposes identical. Naturality of the direct and open compositors
contracts the remaining word to the composite projection after alpha tensor
identity. Pullback associativity identifies the final cast with trianglePull.
The same calculation takes place intrinsically on the simultaneous sequence
site for systems and retains every quotient transition. No projection is inverted.
-/
theorem triangleProjectionCompositorContraction
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ F.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    TriangleEquations
      (ordinary F (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))
      (ordinaryTensor F (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) ∧
    ∀ (o : WeilConjectures.IntegralSystemRealization.Operations l E)
      (z : WeilConjectures.IntegralSystemRealization.Realizations l E F o),
      TriangleEquations (realizedSystems F l E o z) (realizedTensor F l E o z) := by
  obtain ⟨ho, ht, _, hst⟩ := ambientProperOpenPasting F l _hl E n
  constructor
  · exact finite_equations F _ ht (fun f g h L ↦ ho.p_assoc f g h L)
  · intro o z
    exact system_equations F l E o z _hl (hst o z.compositors)

end AlgebraicGeometry.ProEtale.CompactCompositionProjection
