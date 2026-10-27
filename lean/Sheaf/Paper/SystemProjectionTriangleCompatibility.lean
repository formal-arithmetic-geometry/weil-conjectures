/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U6
-/
module

public import Sheaf.Paper.SystemProjectionFormulaMaps
import Sheaf.SixFunctors.TriangleProjectionCompositorContraction

/-! # Projection composition on a compatible triangle

Source: Stacks 0F7B, 0F7J and 0B56; the strict-system projection calculation.
(blueprint: lem-pur-system-projection-triangle-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOfSpec false
set_option genInjectivity false

set_option Elab.async false

universe u g h v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.IntegralSystemRealization
namespace WeilConjectures.SystemProjectionFormula

attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian

attribute [local irreducible] WeilConjectures.pullbackTensorCalculus
  WeilConjectures.pullbackTensorSequenceDerived HasDerivedCategory.standard
  Functor.leftAdjoint Functor.mapDerivedCategory DerivedCategory CoefficientClosedStructure.tensor

attribute [local implicit_reducible] coefficientSequenceHasDerived SemilinearSections.moduleAbelian
  ProEtale.CompactCompositionProjection.realizedSystems
  ProEtale.CompactCompositionProjection.realizedTensor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem adj_right_refl {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    adj.ofNatIsoRight (Iso.refl G) = adj := by
  apply Adjunction.ext
  ext M
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Iso.refl_hom, NatTrans.id_app]
  exact CategoryTheory.Category.comp_id _

private theorem adj_uniq_right_refl {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    (adj.leftAdjointUniq (adj.ofNatIsoRight (Iso.refl G))).hom = 𝟙 F := by
  rw [adj_right_refl]
  exact Adjunction.leftAdjointUniq_refl adj

private theorem openCongr_refl (o : Operations l E) {U V : Scheme.{u}}
    (j : U ⟶ V) [IsOpenImmersion j] :
    (openCongr l E o (rfl : j = j)).hom = 𝟙 _ := by
  exact adj_uniq_right_refl (o.extension j).adj

private theorem tensor_map_comp_right {C : Type*} [Category* C]
    (T : C × C ⥤ C) (M : C) {A B R : C} (f : A ⟶ B) (g : B ⟶ R) :
    T.map (Prod.mkHom (𝟙 M) (f ≫ g)) =
      T.map (Prod.mkHom (𝟙 M) f) ≫ T.map (Prod.mkHom (𝟙 M) g) := by
  exact ((Functor.curryObj T).obj M).map_comp f g

private theorem tensor_map_id_right {C : Type*} [Category* C]
    (T : C × C ⥤ C) (M L : C) : T.map (Prod.mkHom (𝟙 M) (𝟙 L)) = 𝟙 _ := by
  exact ((Functor.curryObj T).obj M).map_id L

private def properComponent (o : Operations l E) {A B : Scheme.{u}} (f : A ⟶ B)
    (K : System l E A) (L : System l E B) :
    (calculus l E B).systemClosed.tensor.obj ((Operations.push l E o f).obj K, L) ⟶
      (Operations.push l E o f).obj
        ((calculus l E A).systemClosed.tensor.obj (K, (pull l E f).obj L)) :=
  ((properProjection l E o f).app K).app L

private def openComponent (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) {A B : Scheme.{u}} (j : A ⟶ B) [IsOpenImmersion j]
    (K : System l E A) (L : System l E B) :
    (calculus l E B).systemClosed.tensor.obj ((Operations.shriek l E o j).obj K, L) ⟶
      (Operations.shriek l E o j).obj
        ((calculus l E A).systemClosed.tensor.obj (K, (pull l E j).obj L)) :=
  (a.projection j).hom.app (K, L)

private theorem projection_component_eq (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) {A B : Scheme.{u}} {f : A ⟶ B}
    (d : Compactification f) (K : System l E A) (L : System l E B) :
    projection l E o c a d K L =
      properComponent l E o d.g ((Operations.shriek l E o d.i).obj K) L ≫
        (Operations.push l E o d.g).map
          (openComponent l E o c a d.i K ((pull l E d.g).obj L) ≫
            (Operations.shriek l E o d.i).map ((calculus l E A).systemClosed.tensor.map
              (Prod.mkHom (𝟙 K) ((c.pullComp d.i d.g).inv.app L ≫
                eqToHom (congrArg (fun h : A ⟶ B ↦ (pull l E h).obj L) d.comm.symm))))) := by
  rfl

private def rawProjection (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) {A V B : Scheme.{u}}
    (j : A ⟶ V) [IsOpenImmersion j] (q : V ⟶ B)
    (K : System l E A) (L : System l E B) :
    (calculus l E B).systemClosed.tensor.obj
        ((Operations.push l E o q).obj ((Operations.shriek l E o j).obj K), L) ⟶
      (Operations.push l E o q).obj ((Operations.shriek l E o j).obj
        ((calculus l E A).systemClosed.tensor.obj (K, (pull l E (j ≫ q)).obj L))) :=
  properComponent l E o q ((Operations.shriek l E o j).obj K) L ≫
    (Operations.push l E o q).map
      (openComponent l E o c a j K ((pull l E q).obj L) ≫
        (Operations.shriek l E o j).map ((calculus l E A).systemClosed.tensor.map
          (Prod.mkHom (𝟙 K) ((c.pullComp j q).inv.app L))))

private theorem projection_transport (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) {A B : Scheme.{u}} {f : A ⟶ B}
    (d : Compactification f) (K : System l E A) (L : System l E B) :
    projection l E o c a d K L = rawProjection l E o c a d.i d.g K L ≫
      (Operations.push l E o d.g).map ((Operations.shriek l E o d.i).map
        ((calculus l E A).systemClosed.tensor.map (Prod.mkHom (𝟙 K)
          (eqToHom (congrArg (fun h : A ⟶ B ↦ (pull l E h).obj L) d.comm.symm))))) := by
  rw [projection_component_eq]
  dsimp only [rawProjection]
  simp -implicitDefEqProofs only [tensor_map_comp_right, Functor.map_comp, Category.assoc]

/-- Pullback composition and equality transport, directly on a system object. -/
private def pullTriangleComponent (o : Operations l E) (c : Compositors l E o)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (e : f ≫ g = h) (N : System l E Z) :
    (pull l E f).obj ((pull l E g).obj N) ⟶ (pull l E h).obj N :=
  (c.pullComp f g).inv.app N ≫
    eqToHom (congrArg (fun h : X ⟶ Z ↦ (pull l E h).obj N) e)

/-- The native composition word, with its compact-support endpoints kept explicit. -/
private def rawAlpha (D : FiniteFieldDatum.{u}) (o : Operations l E)
    (z : Realizations l E D o)
    {X V W Y B Z : Scheme.{u}} (j : X ⟶ V) (b : V ⟶ W) (q : V ⟶ Y)
    (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion b] [IsOpenImmersion i]
    [QuasiCompact b] [QuasiCompact i] [IsProper q] [IsProper p]
    (h : b ≫ p = q ≫ i)
    (K : System l E X) :
    (Operations.push l E o s).obj ((Operations.shriek l E o i).obj
      ((Operations.push l E o q).obj ((Operations.shriek l E o j).obj K))) ⟶
      (Operations.push l E o (p ≫ s)).obj
        ((Operations.shriek l E o (j ≫ b)).obj K) :=
  (Operations.push l E o s).map
    ((z.properOpen.gamma b q p i h).app ((Operations.shriek l E o j).obj K)) ≫
    (Operations.push l E o s).map ((Operations.push l E o p).map
      ((z.compositors.openComp l E j b).hom.app K)) ≫
    (z.compositors.pushComp l E p s).hom.app ((Operations.shriek l E o (j ≫ b)).obj K)

/-- The component formula for alpha, proved before specializing any categories. -/
private theorem alpha_component {G : Type g} [Category.{h} G]
    {geo : G ⥤ Scheme.{u}} (c : ProEtale.AmbientProperOpen.Calculus.{u, g, h, v, w} G geo)
    {X V W Y B Z : G} (j : X ⟶ V) (b : V ⟶ W) (q : V ⟶ Y)
    (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion (geo.map j)] [IsOpenImmersion (geo.map b)]
    [IsOpenImmersion (geo.map i)] [QuasiCompact (geo.map b)]
    [QuasiCompact (geo.map i)] [IsProper (geo.map q)] [IsProper (geo.map p)]
    (square : b ≫ p = q ≫ i) (K : c.D X) :
    (ProEtale.CompactCompositionProjection.alpha c j b q p i s square).app K =
      (c.S s).map ((c.gamma b q p i square).app ((c.J j).obj K)) ≫
        (c.S s).map ((c.S p).map ((c.jComp j b).hom.app K)) ≫
        (c.sComp p s).hom.app ((c.J (j ≫ b)).obj K) := by
  dsimp only [ProEtale.CompactCompositionProjection.alpha,
    ProEtale.CompactCompositionProjection.compact,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_obj, Functor.comp_map]
  simp only [Category.id_comp]
  exact congrArg (fun a ↦ (c.S s).map
    ((c.gamma b q p i square).app ((c.J j).obj K)) ≫ a)
    ((c.sComp p s).hom.naturality ((c.jComp j b).hom.app K)).symm

private theorem realized_sComp (D : FiniteFieldDatum.{u}) (o : Operations l E)
    (z : Realizations l E D o) {A B C : ProEtale.AmbientProperOpen.Spaces D}
    (f : A ⟶ B) (g : B ⟶ C) :
    ProEtale.AmbientProperOpen.Calculus.sComp
        (ProEtale.CompactCompositionProjection.realizedSystems D l E o z) f g =
      z.compositors.pushComp l E
        ((ProEtale.AmbientProperOpen.geometry D).map f)
        ((ProEtale.AmbientProperOpen.geometry D).map g) := by
  rfl

private theorem realized_jComp (D : FiniteFieldDatum.{u}) (o : Operations l E)
    (z : Realizations l E D o) {A B C : ProEtale.AmbientProperOpen.Spaces D}
    (f : A ⟶ B) (g : B ⟶ C)
    [IsOpenImmersion ((ProEtale.AmbientProperOpen.geometry D).map f)]
    [IsOpenImmersion ((ProEtale.AmbientProperOpen.geometry D).map g)] :
    ProEtale.AmbientProperOpen.Calculus.jComp
        (ProEtale.CompactCompositionProjection.realizedSystems D l E o z) f g =
      z.compositors.openComp l E
        ((ProEtale.AmbientProperOpen.geometry D).map f)
        ((ProEtale.AmbientProperOpen.geometry D).map g) := by
  rfl

private theorem realized_gamma (D : FiniteFieldDatum.{u}) (o : Operations l E)
    (z : Realizations l E D o) {U V W B : ProEtale.AmbientProperOpen.Spaces D}
    (b : U ⟶ V) (q : U ⟶ W) (p : V ⟶ B) (i : W ⟶ B)
    [IsOpenImmersion ((ProEtale.AmbientProperOpen.geometry D).map b)]
    [IsOpenImmersion ((ProEtale.AmbientProperOpen.geometry D).map i)]
    [QuasiCompact ((ProEtale.AmbientProperOpen.geometry D).map b)]
    [QuasiCompact ((ProEtale.AmbientProperOpen.geometry D).map i)]
    [IsProper ((ProEtale.AmbientProperOpen.geometry D).map q)]
    [IsProper ((ProEtale.AmbientProperOpen.geometry D).map p)]
    (h : b ≫ p = q ≫ i) :
    ProEtale.AmbientProperOpen.Calculus.gamma
        (ProEtale.CompactCompositionProjection.realizedSystems D l E o z) b q p i h =
      z.properOpen.gamma
        ((ProEtale.AmbientProperOpen.geometry D).map b)
        ((ProEtale.AmbientProperOpen.geometry D).map q)
        ((ProEtale.AmbientProperOpen.geometry D).map p)
        ((ProEtale.AmbientProperOpen.geometry D).map i)
        (congrArg (fun f ↦ (ProEtale.AmbientProperOpen.geometry D).map f) h) := by
  dsimp only [ProEtale.AmbientProperOpen.Calculus.gamma,
    ProEtale.CompactCompositionProjection.realizedSystems]
  exact (mateEquiv (o.direct ((ProEtale.AmbientProperOpen.geometry D).map q)).adj
    (o.direct ((ProEtale.AmbientProperOpen.geometry D).map p)).adj).apply_symm_apply _

/-- The bundled component notation is the native proper/open projection word. -/
private theorem realized_projection (D : FiniteFieldDatum.{u}) (o : Operations l E)
    (z : Realizations l E D o) {A V B : ProEtale.AmbientProperOpen.Spaces D}
    (j : A ⟶ V) (q : V ⟶ B)
    [IsOpenImmersion ((ProEtale.AmbientProperOpen.geometry D).map j)]
      [IsOpenImmersion j.hom.left]
    (K : System l E A.obj.left) (L : System l E B.obj.left) :
    ProEtale.CompactCompositionProjection.projection
        (ProEtale.CompactCompositionProjection.realizedSystems D l E o z)
        (ProEtale.CompactCompositionProjection.realizedTensor D l E o z) j q K L =
      rawProjection l E o z.compositors z.openComparisons
        j.hom.left q.hom.left K L := by
  rfl

private theorem native_comp {D : FiniteFieldDatum.{u}}
    {A B C : ProEtale.AmbientProperOpen.Spaces D} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).hom.left = f.hom.left ≫ g.hom.left := by
  exact (ProEtale.AmbientProperOpen.geometry D).map_comp f g

private theorem realized_trianglePull_iso (D : FiniteFieldDatum.{u}) (o : Operations l E)
    (z : Realizations l E D o) {A V W Y B Z : ProEtale.AmbientProperOpen.Spaces D}
    (j : A ⟶ V) (b : V ⟶ W) (q : V ⟶ Y) (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    (square : b ≫ p = q ≫ i)
    (hfg : (j.hom.left ≫ q.hom.left) ≫ (i.hom.left ≫ s.hom.left) =
      (j.hom.left ≫ b.hom.left) ≫ (p.hom.left ≫ s.hom.left))
    :
    ProEtale.CompactCompositionProjection.trianglePull
        (ProEtale.CompactCompositionProjection.realizedSystems D l E o z)
        j b q p i s square =
      (z.compositors.pullComp (j.hom.left ≫ q.hom.left)
        (i.hom.left ≫ s.hom.left)).symm ≪≫ eqToIso (congrArg (pull l E) hfg) := by
  rfl

attribute [local irreducible] properProjection compactificationProjection projection rawProjection

/-- Translate a bundled system equation into its native, typed component notation. -/
private theorem realized_equation (D : FiniteFieldDatum.{u}) (o : Operations l E)
    (z : Realizations l E D o) {A V W Y B Z : ProEtale.AmbientProperOpen.Spaces D}
    (j : A ⟶ V) (b : V ⟶ W) (q : V ⟶ Y) (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion ((ProEtale.AmbientProperOpen.geometry D).map j)]
    [IsOpenImmersion ((ProEtale.AmbientProperOpen.geometry D).map b)]
    [IsOpenImmersion ((ProEtale.AmbientProperOpen.geometry D).map i)]
    [QuasiCompact ((ProEtale.AmbientProperOpen.geometry D).map b)]
    [QuasiCompact ((ProEtale.AmbientProperOpen.geometry D).map i)]
    [IsProper ((ProEtale.AmbientProperOpen.geometry D).map q)]
    [IsProper ((ProEtale.AmbientProperOpen.geometry D).map p)]
    [IsProper ((ProEtale.AmbientProperOpen.geometry D).map s)]
    [IsOpenImmersion j.hom.left]
    [IsOpenImmersion b.hom.left]
    [IsOpenImmersion i.hom.left]
    [QuasiCompact b.hom.left]
    [QuasiCompact i.hom.left]
    [IsProper q.hom.left]
    [IsProper p.hom.left]
    [IsProper s.hom.left]
    (square : b ≫ p = q ≫ i)
    (squareNative : b.hom.left ≫ p.hom.left = q.hom.left ≫ i.hom.left)
    (hfg : (j.hom.left ≫ q.hom.left) ≫ (i.hom.left ≫ s.hom.left) =
      (j.hom.left ≫ b.hom.left) ≫ (p.hom.left ≫ s.hom.left))
    (H : ProEtale.CompactCompositionProjection.TriangleEquations
      (ProEtale.CompactCompositionProjection.realizedSystems D l E o z)
      (ProEtale.CompactCompositionProjection.realizedTensor D l E o z))
    (M : System l E A.obj.left) (N : System l E Z.obj.left) :
      rawProjection l E o z.compositors z.openComparisons i.hom.left s.hom.left
          ((Operations.push l E o q.hom.left).obj ((Operations.shriek l E o j.hom.left).obj M)) N ≫
        (Operations.push l E o s.hom.left).map ((Operations.shriek l E o i.hom.left).map
          (rawProjection l E o z.compositors z.openComparisons j.hom.left q.hom.left M
            ((pull l E (i.hom.left ≫ s.hom.left)).obj N))) ≫
        rawAlpha l E D o z j.hom.left b.hom.left q.hom.left p.hom.left i.hom.left s.hom.left
          squareNative
          ((calculus l E A.obj.left).systemClosed.tensor.obj
            (M, (pull l E (j.hom.left ≫ q.hom.left)).obj
              ((pull l E (i.hom.left ≫ s.hom.left)).obj N))) ≫
        (Operations.push l E o (p.hom.left ≫ s.hom.left)).map
          ((Operations.shriek l E o (j.hom.left ≫ b.hom.left)).map
          ((calculus l E A.obj.left).systemClosed.tensor.map (Prod.mkHom (𝟙 M)
            (pullTriangleComponent l E o z.compositors
              (j.hom.left ≫ q.hom.left) (i.hom.left ≫ s.hom.left)
              ((j.hom.left ≫ b.hom.left) ≫ (p.hom.left ≫ s.hom.left)) hfg N)))) =
      (calculus l E Z.obj.left).systemClosed.tensor.map
        (Prod.mkHom
          (rawAlpha l E D o z j.hom.left b.hom.left q.hom.left p.hom.left i.hom.left
            s.hom.left squareNative M) (𝟙 N)) ≫
        rawProjection l E o z.compositors z.openComparisons
          (j.hom.left ≫ b.hom.left) (p.hom.left ≫ s.hom.left) M N := by
  have : IsOpenImmersion (j ≫ b).hom.left := by
    rw [native_comp (D := D) j b]
    infer_instance
  have : IsOpenImmersion ((ProEtale.AmbientProperOpen.geometry D).map (j ≫ b)) := by
    change IsOpenImmersion (j ≫ b).hom.left
    infer_instance
  have ha (K : System l E A.obj.left) :
      (ProEtale.CompactCompositionProjection.alpha
        (ProEtale.CompactCompositionProjection.realizedSystems D l E o z)
          j b q p i s square).app K =
      rawAlpha l E D o z j.hom.left b.hom.left q.hom.left p.hom.left i.hom.left s.hom.left
        squareNative K := by
    unfold rawAlpha
    rw [alpha_component
      (ProEtale.CompactCompositionProjection.realizedSystems D l E o z)
      j b q p i s square K]
    rw [realized_gamma l E D o z b q p i square,
      realized_sComp l E D o z p s, realized_jComp l E D o z j b]
    rfl
  have hraw := H j b q p i s square M N
  simp only [ProEtale.CompactCompositionProjection.leftMap,
    ProEtale.CompactCompositionProjection.rightMap,
    Functor.comp_obj,
    realized_projection l E D o z j q, realized_projection l E D o z i s,
    realized_projection l E D o z (j ≫ b) (p ≫ s), ha,
    realized_trianglePull_iso l E D o z j b q p i s square hfg,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app] at hraw
  dsimp only [pullTriangleComponent]
  exact hraw

/-- Normalize the factorization equations before instantiating a property of triangles. -/
private theorem triangle_induction {X Y Z : Scheme.{u}}
    (P : (f : X ⟶ Y) → (g : Y ⟶ Z) → Compactification.Triangle f g → Prop)
    (h : ∀ (V B W : Scheme.{u}) (j : X ⟶ V) (q : V ⟶ Y) (i : Y ⟶ B)
      (s : B ⟶ Z) (b : V ⟶ W) (p : W ⟶ B)
      (hq : IsProper q) (hj : IsOpenImmersion j) (hs : IsProper s)
      (hi : IsOpenImmersion i) (hr : IsProper (p ≫ s))
      (hk : IsOpenImmersion (j ≫ b)) (hb : IsOpenImmersion b)
      (hfg : (j ≫ q) ≫ (i ≫ s) = (j ≫ b) ≫ (p ≫ s))
      (hpb : IsPullback q b i p),
      P (j ≫ q) (i ≫ s)
        { cf := ⟨V, q, j, rfl, hq, hj⟩
          cg := ⟨B, s, i, rfl, hs, hi⟩
          cfg := ⟨W, p ≫ s, j ≫ b, hfg, hr, hk⟩
          q := b
          p := p
          isOpenImmersion_q := hb
          i_q := rfl
          p_g := rfl
          isPullback := hpb })
    {f : X ⟶ Y} {g : Y ⟶ Z} (T : Compactification.Triangle f g) : P f g T := by
  rcases T with @⟨⟨V, q, j, hf, hq, hj⟩, ⟨B, s, i, hg, hs, hi⟩,
    ⟨W, r, k, hfg, hr, hk⟩, b, p, hb, hjb, hps, hpb⟩
  subst f
  subst g
  change V ⟶ W at b
  change W ⟶ B at p
  change j ≫ b = k at hjb
  change p ≫ s = r at hps
  change IsPullback q b i p at hpb
  subst k
  subst r
  exact h V B W j q i s b p hq hj hs hi hr hk hb hfg hpb

section Geometry
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  (o : Operations l E) (z : Realizations l E D o)
  {X Y Z : Scheme.{u}}
  [overX : X.Over (Spec (.of D.k))] [overY : Y.Over (Spec (.of D.k))]
  [overZ : Z.Over (Spec (.of D.k))]
  [sepX : IsSeparated (X ↘ Spec (.of D.k))] [sepY : IsSeparated (Y ↘ Spec (.of D.k))]
  [sepZ : IsSeparated (Z ↘ Spec (.of D.k))]
  [ftX : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [qcX : QuasiCompact (X ↘ Spec (.of D.k))]
  [ftY : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [qcY : QuasiCompact (Y ↘ Spec (.of D.k))]
  [ftZ : LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
  [qcZ : QuasiCompact (Z ↘ Spec (.of D.k))]
  (f : X ⟶ Y) (g : Y ⟶ Z)
  [overF : f.IsOver (Spec (.of D.k))] [overG : g.IsOver (Spec (.of D.k))]
  [sepF : IsSeparated f] [ftF : LocallyOfFiniteType f] [QuasiCompact f]
  [sepG : IsSeparated g] [ftG : LocallyOfFiniteType g] [QuasiCompact g]

-- Keep the original separatedness binders, although the component calculation does not use them.
set_option linter.unusedSectionVars false in
include D hl overX overY overZ sepX sepY sepZ ftX qcX ftY qcY ftZ qcZ
  overF overG sepF sepG ftF ftG in
/-- The projection composition equation for one supplied compatible triangle.
Source: Stacks 0F7J, the proper/open composition word, and 0B56's projection mate.
(blueprint: lem-pur-system-projection-triangle-compatibility).

Proof: bundle the six schemes and maps of the supplied triangle into the
finite-type-over-k calculus. Properness supplies the finiteness of the ambient
structure maps, and the cartesian square supplies quasi-compactness of its open
map. Apply the system component equation of
lem-sf-triangle-projection-compositor-contraction. Adjunction cancellation
identifies its proper/open mate with the specified intrinsic gamma, and
naturality of the proper compositor identifies its alpha with triangleWord.
Postcompose with the inverse equality transport of the composite factorization.
Functoriality of tensor and compact support cancels the two opposite transports
on the left and incorporates the remaining one into the projection on the right.
Everything takes place in the system category, before evaluation. -/
theorem projection_triangle (T : Compactification.Triangle f g)
    (M : System l E X) (N : System l E Z) :
    projection l E o z.compositors z.openComparisons T.cg ((support l E o T.cf).obj M) N ≫
      (support l E o T.cg).map
        (projection l E o z.compositors z.openComparisons T.cf M ((pull l E g).obj N)) ≫
      (triangleWord l E o z.compositors z.openComparisons z.canonicalBridge
        z.properOpen T).app
          ((calculus l E X).systemClosed.tensor.obj
            (M, (pull l E f).obj ((pull l E g).obj N))) ≫
      (support l E o T.cfg).map ((calculus l E X).systemClosed.tensor.map
        (Prod.mkHom (𝟙 M) ((z.compositors.pullComp f g).inv.app N))) =
    (calculus l E Z).systemClosed.tensor.map
      (Prod.mkHom ((triangleWord l E o z.compositors z.openComparisons z.canonicalBridge
        z.properOpen T).app M) (𝟙 N)) ≫
      projection l E o z.compositors z.openComparisons T.cfg M N := by
  rename_i qcf qcg
  revert overF overG sepF sepG ftF ftG qcf qcg
  apply triangle_induction (T := T)
  intro V B W j q i s b p hq hj hs hi hr hk hb hfg hpb
    overF overG sepF sepG ftF ftG qcf qcg
  have := hq
  have := hj
  have := hs
  have := hi
  have := hb
  have := hr
  have : IsProper p := IsProper.of_comp p s
  have qi : QuasiCompact i :=
    QuasiCompact.of_comp i s
  have qb : QuasiCompact b :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb qi
  -- Bundle the given geometry; no compactification is chosen.
  let XX : ProEtale.AmbientProperOpen.Spaces D :=
    ⟨Over.mk (X ↘ Spec (.of D.k)), ftX, qcX⟩
  let YY : ProEtale.AmbientProperOpen.Spaces D :=
    ⟨Over.mk (Y ↘ Spec (.of D.k)), ftY, qcY⟩
  let ZZ : ProEtale.AmbientProperOpen.Spaces D :=
    ⟨Over.mk (Z ↘ Spec (.of D.k)), ftZ, qcZ⟩
  let VV : ProEtale.AmbientProperOpen.Spaces D :=
    ⟨Over.mk (q ≫ (Y ↘ Spec (.of D.k))),
      by change LocallyOfFiniteType (q ≫ (Y ↘ Spec (.of D.k))); infer_instance,
      by change QuasiCompact (q ≫ (Y ↘ Spec (.of D.k))); infer_instance⟩
  let BB : ProEtale.AmbientProperOpen.Spaces D :=
    ⟨Over.mk (s ≫ (Z ↘ Spec (.of D.k))),
      by change LocallyOfFiniteType (s ≫ (Z ↘ Spec (.of D.k))); infer_instance,
      by change QuasiCompact (s ≫ (Z ↘ Spec (.of D.k))); infer_instance⟩
  let WW : ProEtale.AmbientProperOpen.Spaces D :=
    ⟨Over.mk ((p ≫ s) ≫ (Z ↘ Spec (.of D.k))),
      by change LocallyOfFiniteType ((p ≫ s) ≫ (Z ↘ Spec (.of D.k))); infer_instance,
      by change QuasiCompact ((p ≫ s) ≫ (Z ↘ Spec (.of D.k))); infer_instance⟩
  let jj : XX ⟶ VV := ⟨Over.homMk j (by
    change j ≫ (q ≫ (Y ↘ Spec (.of D.k))) = X ↘ Spec (.of D.k)
    simpa only [Category.assoc] using
      (CategoryTheory.comp_over (j ≫ q) (Spec (.of D.k))))⟩
  let qq : VV ⟶ YY := ⟨Over.homMk q rfl⟩
  let ii : YY ⟶ BB := ⟨Over.homMk i (by
    change i ≫ (s ≫ (Z ↘ Spec (.of D.k))) = Y ↘ Spec (.of D.k)
    simpa only [Category.assoc] using
      (CategoryTheory.comp_over (i ≫ s) (Spec (.of D.k))))⟩
  let ss : BB ⟶ ZZ := ⟨Over.homMk s rfl⟩
  let pp : WW ⟶ BB := ⟨Over.homMk p (Category.assoc _ _ _).symm⟩
  let bb : VV ⟶ WW := ⟨Over.homMk b (by
    change b ≫ ((p ≫ s) ≫ (Z ↘ Spec (.of D.k))) = q ≫ (Y ↘ Spec (.of D.k))
    simp only [Category.assoc]
    rw [← Category.assoc b p, ← hpb.w]
    simp only [Category.assoc]
    rw [← Category.assoc i s, CategoryTheory.comp_over (i ≫ s) (Spec (.of D.k))])⟩
  have square : bb ≫ pp = qq ≫ ii := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact hpb.w.symm
  have : IsOpenImmersion ((ProEtale.AmbientProperOpen.geometry D).map jj) := by
    change IsOpenImmersion j
    exact hj
  have : IsOpenImmersion ((ProEtale.AmbientProperOpen.geometry D).map bb) := by
    change IsOpenImmersion b
    exact hb
  have : IsOpenImmersion ((ProEtale.AmbientProperOpen.geometry D).map ii) := by
    change IsOpenImmersion i
    exact hi
  have : QuasiCompact ((ProEtale.AmbientProperOpen.geometry D).map bb) := by
    change QuasiCompact b
    exact qb
  have : QuasiCompact ((ProEtale.AmbientProperOpen.geometry D).map ii) := by
    change QuasiCompact i
    exact qi
  have : IsProper ((ProEtale.AmbientProperOpen.geometry D).map qq) := by
    change IsProper q
    exact hq
  have : IsProper ((ProEtale.AmbientProperOpen.geometry D).map pp) := by
    change IsProper p
    infer_instance
  have : IsProper ((ProEtale.AmbientProperOpen.geometry D).map ss) := by
    change IsProper s
    exact hs
  have : IsOpenImmersion jj.hom.left := by
    change IsOpenImmersion j
    exact hj
  have : IsOpenImmersion bb.hom.left := by
    change IsOpenImmersion b
    exact hb
  have : IsOpenImmersion ii.hom.left := by
    change IsOpenImmersion i
    exact hi
  have : QuasiCompact bb.hom.left := by
    change QuasiCompact b
    exact qb
  have : QuasiCompact ii.hom.left := by
    change QuasiCompact i
    exact qi
  have : IsProper qq.hom.left := by
    change IsProper q
    exact hq
  have : IsProper pp.hom.left := by
    change IsProper p
    infer_instance
  have : IsProper ss.hom.left := by
    change IsProper s
    exact hs
  -- Cancel the inverse mate, then move the open compositor by naturality.
  let a := rawAlpha l E D o z j b q p i s hpb.w.symm
  let TT : Compactification.Triangle (j ≫ q) (i ≫ s) :=
    { cf := ⟨V, q, j, rfl, hq, hj⟩
      cg := ⟨B, s, i, rfl, hs, hi⟩
      cfg := ⟨W, p ≫ s, j ≫ b, hfg, hr, hk⟩
      q := b
      p := p
      isOpenImmersion_q := hb
      i_q := rfl
      p_g := rfl
      isPullback := hpb }
  have ht (K : System l E X) :
      (triangleWord l E o z.compositors z.openComparisons z.canonicalBridge
        z.properOpen TT).app K = a K := by
    dsimp +instances only [triangleWord, TT, support, a, rawAlpha, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Iso.symm_hom, Functor.comp_map, Functor.comp_obj]
    simp -implicitDefEqProofs only [openCongr_refl l E o, eqToHom_refl,
      NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  dsimp only [TT] at ht
  let piF := rawProjection l E o z.compositors z.openComparisons j q
  let piG := rawProjection l E o z.compositors z.openComparisons i s
  let piFG := rawProjection l E o z.compositors z.openComparisons (j ≫ b) (p ≫ s)
  -- Specialize the existing component equation to these concrete functors.
  have hh :
      piG ((Operations.push l E o q).obj ((Operations.shriek l E o j).obj M)) N ≫
        (Operations.push l E o s).map ((Operations.shriek l E o i).map
          (piF M ((pull l E (i ≫ s)).obj N))) ≫
        a ((calculus l E X).systemClosed.tensor.obj
            (M, (pull l E (j ≫ q)).obj ((pull l E (i ≫ s)).obj N))) ≫
        (Operations.push l E o (p ≫ s)).map ((Operations.shriek l E o (j ≫ b)).map
          ((calculus l E X).systemClosed.tensor.map (Prod.mkHom (𝟙 M)
            (pullTriangleComponent l E o z.compositors
              (j ≫ q) (i ≫ s) ((j ≫ b) ≫ (p ≫ s)) hfg N)))) =
      (calculus l E Z).systemClosed.tensor.map
        (Prod.mkHom (a M) (𝟙 N)) ≫ piFG M N := by
    exact realized_equation l E D o z jj bb qq pp ii ss square hpb.w.symm hfg
      ((ProEtale.CompactCompositionProjection.triangleProjectionCompositorContraction
        D l hl E 0).2 o z) M N
  dsimp only [pullTriangleComponent] at hh
  -- Transport back along the composite factorization and cancel its inverse.
  have hh' := congrArg (fun a ↦ a ≫
    (Operations.push l E o (p ≫ s)).map ((Operations.shriek l E o (j ≫ b)).map
      ((calculus l E X).systemClosed.tensor.map (Prod.mkHom (𝟙 M)
        (eqToHom (congrArg (fun h ↦ (pull l E h).obj N) hfg.symm)))))) hh
  dsimp +instances only [piF, piG, piFG] at hh'
  simp only [projection_transport l E o z.compositors z.openComparisons, ht, eqToHom_refl,
    tensor_map_id_right, CategoryTheory.Functor.map_id, Category.comp_id]
  dsimp +instances only [support, Functor.comp]
  simp -implicitDefEqProofs only [Category.assoc, ← Functor.map_comp,
    prod_comp, Prod.mkHom,
    eqToHom_trans, eqToHom_refl, Category.comp_id] at hh'
  dsimp +instances only [System, coefficientSequenceDerived,
    coefficientSequenceHasDerived, SemilinearSections.moduleAbelian] at hh' ⊢
  with_reducible exact hh'

end Geometry
end WeilConjectures.SystemProjectionFormula
