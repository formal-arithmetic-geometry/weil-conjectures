/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.AmbientProperOpenPasting
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.AlgebraicGeometry.CompactCompositionProjection.CompositionProjectionData
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryProperOpenInvertibility
import WeilConjectures.SixFunctors.IntegralSystemRealization.Proper.SystemProperOpenSupport
import WeilConjectures.AlgebraicGeometry.CompactCompositionProjection.TriangleProjectionCompositorContraction
import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemCompositorAssociativity
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting

/-! # Compact-support composition and projection

Source: Stacks Project, Tags 0F7B--0F7D, 0F7J and 0F7K, and the counit calculation
in the blueprint projection-coherence proof (blueprint: lem-sf-composition-projection-mate).
The component formulas retain both successive pullbacks. System operations are the
simultaneous ringed-diagram operations, before evaluation or total limit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOfSpec false
set_option genInjectivity false

universe u g h v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.AmbientProperOpen

namespace AlgebraicGeometry.ProEtale.CompactCompositionProjection

variable {G : Type g} [Category.{h} G] {geo : G ⥤ Scheme.{u}}

variable (c : Calculus.{u, g, h, v, w} G geo) (t : TensorData c)

private theorem alpha_app {X V W Y B Z : G} (j : X ⟶ V) (b : V ⟶ W) (q : V ⟶ Y)
    (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion (geo.map j)] [IsOpenImmersion (geo.map b)]
    [IsOpenImmersion (geo.map i)] [QuasiCompact (geo.map b)]
    [QuasiCompact (geo.map i)] [IsProper (geo.map q)] [IsProper (geo.map p)]
    (hb : b ≫ p = q ≫ i) (K : c.D X) :
    (alpha c j b q p i s hb).app K =
      (c.S s).map ((c.gamma b q p i hb).app ((c.J j).obj K)) ≫
        (c.sComp p s).hom.app ((c.J b).obj ((c.J j).obj K)) ≫
        (c.S (p ≫ s)).map ((c.jComp j b).hom.app K) := by
  simp [alpha, compact]

private structure CompositionLaws (c : Calculus.{u, g, h, v, w} G geo) : Prop where
  s_assoc : ∀ {X Y Z T : G} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (M : c.D X),
    (c.S h).map ((c.sComp f g).hom.app M) ≫ (c.sComp (f ≫ g) h).hom.app M =
      (c.sComp g h).hom.app ((c.S f).obj M) ≫ (c.sComp f (g ≫ h)).hom.app M ≫
        (c.sCongr (Category.assoc f g h)).inv.app M
  j_assoc : ∀ {X Y Z T : G} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    [IsOpenImmersion (geo.map f)] [IsOpenImmersion (geo.map g)]
    [IsOpenImmersion (geo.map h)] (M : c.D X),
    (c.J h).map ((c.jComp f g).hom.app M) ≫ (c.jComp (f ≫ g) h).hom.app M =
      (c.jComp g h).hom.app ((c.J f).obj M) ≫ (c.jComp f (g ≫ h)).hom.app M ≫
        (c.jCongr (Category.assoc f g h)).inv.app M
  gamma_vertical : ∀ {A C₀ E B D F : G}
    (k : A ⟶ B) (i : C₀ ⟶ D) (j : E ⟶ F)
    (r₁ : A ⟶ C₀) (r₂ : C₀ ⟶ E) (p₁ : B ⟶ D) (p₂ : D ⟶ F)
    [IsOpenImmersion (geo.map k)] [IsOpenImmersion (geo.map i)]
    [IsOpenImmersion (geo.map j)]
    [QuasiCompact (geo.map k)] [QuasiCompact (geo.map i)] [QuasiCompact (geo.map j)]
    [IsProper (geo.map r₁)] [IsProper (geo.map r₂)]
    [IsProper (geo.map p₁)] [IsProper (geo.map p₂)]
    (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
    (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) (M : c.D A),
    (c.J j).map ((c.sComp r₁ r₂).hom.app M) ≫
        (c.gamma k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app M ≫
        (c.sComp p₁ p₂).inv.app ((c.J k).obj M) =
      (c.gamma i r₂ p₂ j h₂).app ((c.S r₁).obj M) ≫
        (c.S p₂).map ((c.gamma k r₁ p₁ i h₁).app M)
  gamma_horizontal : ∀ {A B E C₀ D F : G}
    (k : A ⟶ B) (l : B ⟶ E) (i : C₀ ⟶ D) (j : D ⟶ F)
    (r : A ⟶ C₀) (p : B ⟶ D) (q : E ⟶ F)
    [IsOpenImmersion (geo.map k)] [IsOpenImmersion (geo.map l)]
    [IsOpenImmersion (geo.map i)] [IsOpenImmersion (geo.map j)]
    [QuasiCompact (geo.map k)] [QuasiCompact (geo.map l)]
    [QuasiCompact (geo.map i)] [QuasiCompact (geo.map j)]
    [IsProper (geo.map r)] [IsProper (geo.map p)] [IsProper (geo.map q)]
    (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
    (h : (k ≫ l) ≫ q = r ≫ (i ≫ j)) (M : c.D A),
    (c.jComp i j).hom.app ((c.S r).obj M) ≫
        (c.gamma (k ≫ l) r q (i ≫ j) h).app M ≫
        (c.S q).map ((c.jComp k l).inv.app M) =
      (c.J j).map ((c.gamma k r p i h₁).app M) ≫
        (c.gamma l p q j h₂).app ((c.J k).obj M)

private theorem direct_assoc_of_pull_assoc
    (hp : ∀ {X Y Z T : G} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T),
      c.pComp f (g ≫ h) ≪≫ Functor.isoWhiskerRight (c.pComp g h) (c.P f) =
        eqToIso (congrArg c.P (Category.assoc f g h).symm) ≪≫
          c.pComp (f ≫ g) h ≪≫ Functor.isoWhiskerLeft (c.P h) (c.pComp f g))
    {X Y Z T : G} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (M : c.D X) :
    (c.S h).map ((c.sComp f g).hom.app M) ≫ (c.sComp (f ≫ g) h).hom.app M =
      (c.sComp g h).hom.app ((c.S f).obj M) ≫ (c.sComp f (g ≫ h)).hom.app M ≫
        (c.sCongr (Category.assoc f g h)).inv.app M := by
  have hp' := congrArg Iso.hom (hp f g h)
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom] at hp'
  have hh := ProEtale.StrictTower.conjugate_triangle_assoc
    (c.adj h) (c.adj g) (c.adj f) (c.adj (g ≫ h)) (c.adj (f ≫ g))
    (c.adj (f ≫ g ≫ h)) (c.pComp g h) (c.pComp f g)
    (eqToIso (congrArg c.P (Category.assoc f g h).symm) ≪≫ c.pComp (f ≫ g) h)
    (c.pComp f (g ≫ h))
    (by simpa only [Iso.trans_hom, Category.assoc] using hp'.symm)
  have ht := congrArg Iso.hom (SemilinearProperOpen.conjugate_transport c.P c.S
    (fun f ↦ c.adj f) ((c.adj h).comp (c.adj (f ≫ g)))
    (Category.assoc f g h) (c.pComp (f ≫ g) h))
  simp only [Iso.trans_hom, conjugateIsoEquiv_apply_hom] at ht
  simp only [Iso.trans_hom] at hh
  rw [ht] at hh
  have hm := congr_app hh M
  apply (cancel_mono ((c.sCongr (Category.assoc f g h)).hom.app M)).1
  simpa only [Calculus.sComp, Calculus.sCongr, conjugateIsoEquiv_apply_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc, Iso.inv_hom_id_app, Category.comp_id] using hm.symm

private theorem open_comp_transport {X Y Z : G}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z)
    [IsOpenImmersion (geo.map f)] [IsOpenImmersion (geo.map g)]
    [IsOpenImmersion (geo.map k)] (e : f ≫ g = k) :
    Adjunction.leftAdjointCompIso (c.openAdj f) (c.openAdj g) (c.openAdj k)
        ((c.pComp f g).symm ≪≫ eqToIso (congrArg c.P e)) =
      c.jComp f g ≪≫ c.jCongr e := by
  subst k
  simp only [Calculus.jCongr, eqToIso_refl, Iso.trans_refl, Calculus.jComp]

private theorem open_assoc_of_pull_assoc
    (hp : ∀ {X Y Z T : G} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T),
      c.pComp f (g ≫ h) ≪≫ Functor.isoWhiskerRight (c.pComp g h) (c.P f) =
        eqToIso (congrArg c.P (Category.assoc f g h).symm) ≪≫
          c.pComp (f ≫ g) h ≪≫ Functor.isoWhiskerLeft (c.P h) (c.pComp f g))
    {X Y Z T : G} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    [IsOpenImmersion (geo.map f)] [IsOpenImmersion (geo.map g)]
    [IsOpenImmersion (geo.map h)] (M : c.D X) :
    (c.J h).map ((c.jComp f g).hom.app M) ≫ (c.jComp (f ≫ g) h).hom.app M =
      (c.jComp g h).hom.app ((c.J f).obj M) ≫ (c.jComp f (g ≫ h)).hom.app M ≫
        (c.jCongr (Category.assoc f g h)).inv.app M := by
  have hi : Functor.isoWhiskerLeft (c.P h) (c.pComp f g).symm ≪≫
      ((c.pComp (f ≫ g) h).symm ≪≫ eqToIso (congrArg c.P (Category.assoc f g h))) =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (c.pComp g h).symm (c.P f) ≪≫
        (c.pComp f (g ≫ h)).symm := by
    have hp' := congrArg Iso.symm (hp f g h)
    apply Iso.ext
    apply NatTrans.ext
    funext N
    simpa only [Iso.trans_inv, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_inv_app, Category.id_comp, Category.assoc,
      Iso.symm_hom, eqToIso.inv, eqToIso.hom] using
        (congr_app (congrArg Iso.hom hp') N).symm
  have hh := Adjunction.leftAdjointCompIso_assoc
    (c.openAdj f) (c.openAdj g) (c.openAdj h)
    (c.openAdj (f ≫ g)) (c.openAdj (g ≫ h)) (c.openAdj (f ≫ g ≫ h))
    (c.pComp f g).symm (c.pComp g h).symm (c.pComp f (g ≫ h)).symm
    ((c.pComp (f ≫ g) h).symm ≪≫ eqToIso (congrArg c.P (Category.assoc f g h))) hi
  rw [open_comp_transport c (f ≫ g) h (f ≫ g ≫ h) (Category.assoc f g h)] at hh
  have hm := congr_app (congrArg Iso.hom hh) M
  apply (cancel_mono ((c.jCongr (Category.assoc f g h)).hom.app M)).1
  simpa only [Calculus.jComp, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app,
    Category.id_comp, Category.assoc, Iso.inv_hom_id_app, Category.comp_id] using hm.symm

private theorem associativity_of_laws (hc : CompositionLaws c) : Associativity c := by
  intro X U V W Y A B Z C T j b d q r p i e s t₀ k v₀
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA hB hC hAB hBC K
  have hn := (c.gamma d (r ≫ s) (p ≫ t₀) k hBC).naturality
    ((c.jComp j b).hom.app K)
  dsimp only [Functor.comp_map] at hn
  have hv := hc.gamma_vertical d e k r s p t₀ hB hC hBC
    ((c.J b).obj ((c.J j).obj K))
  have hh := hc.gamma_horizontal b d i e q r p hA hB hAB ((c.J j).obj K)
  dsimp only [Functor.comp_obj] at hn hv hh
  have hv' := congrArg (fun a ↦ a ≫
    (c.sComp p t₀).hom.app ((c.J d).obj ((c.J b).obj ((c.J j).obj K)))) hv
  simp only [Category.assoc, Iso.inv_hom_id_app] at hv'
  have hh' := congrArg (fun a ↦ a ≫
    (c.S p).map ((c.jComp b d).hom.app ((c.J j).obj K))) hh
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    ] at hh'
  erw [(c.S p).map_id] at hh'
  simp only [Category.comp_id] at hv' hh'
  have hnv := congrArg (fun a ↦ (c.S v₀).map a) hn
  have hvv := congrArg (fun a ↦ (c.S v₀).map a) hv'
  simp only [Functor.map_comp] at hnv hvv
  simp only [alpha_app, compact, Functor.comp_map, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hnv, reassoc_of% hvv]
  have hcn := (c.gamma e s t₀ k hC).naturality
    ((c.gamma b q r i hA).app ((c.J j).obj K))
  dsimp only [Functor.comp_map] at hcn
  have hcnv := congrArg (fun a ↦ (c.S v₀).map a) hcn
  simp only [Functor.map_comp] at hcnv
  rw [reassoc_of% hcnv]
  congr 1
  have ns₁ := (c.sComp t₀ v₀).hom.naturality
    ((c.jComp i e).hom.app ((c.S q).obj ((c.J j).obj K)))
  have ns₂ := (c.sComp t₀ v₀).hom.naturality
    ((c.gamma (b ≫ d) q p (i ≫ e) hAB).app ((c.J j).obj K))
  dsimp only [Functor.comp_map, Functor.comp_obj] at ns₁ ns₂ ⊢
  rw [← reassoc_of% ns₁, ← reassoc_of% ns₂]
  have hs := congrArg (fun a ↦ a ≫ (c.sCongr (Category.assoc p t₀ v₀)).hom.app
    ((c.J (b ≫ d)).obj ((c.J j).obj K)))
    (hc.s_assoc p t₀ v₀ ((c.J (b ≫ d)).obj ((c.J j).obj K)))
  simp only [Category.assoc, Iso.inv_hom_id_app] at hs
  simp only [Category.comp_id] at hs
  rw [← reassoc_of% hs]
  have hhh := congrArg (fun a ↦ (c.S v₀).map ((c.S t₀).map a)) hh'
  simp only [Functor.map_comp] at hhh
  rw [reassoc_of% hhh]
  congr 1
  congr 1
  have ns₃ := (c.sComp (p ≫ t₀) v₀).hom.naturality
    ((c.J d).map ((c.jComp j b).hom.app K))
  dsimp only [Functor.comp_map] at ns₃
  rw [reassoc_of% ns₃]
  have hj := congrArg (fun a ↦ a ≫
    (c.jCongr (Category.assoc j b d)).hom.app K) (hc.j_assoc j b d K)
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at hj
  have hjm := congrArg (fun a ↦ (c.S ((p ≫ t₀) ≫ v₀)).map a) hj
  simp only [Functor.map_comp] at hjm
  rw [reassoc_of% hjm]
  have ns₄ := (c.sCongr (Category.assoc p t₀ v₀)).hom.naturality
    ((c.jComp j (b ≫ d)).hom.app K)
  rw [ns₄]
  have ns₅ := (c.sComp (p ≫ t₀) v₀).hom.naturality
    ((c.jComp b d).hom.app ((c.J j).obj K))
  dsimp only [Functor.comp_map] at ns₅
  rw [← reassoc_of% ns₅]
  have ns₆ := (c.sComp p t₀).hom.naturality
    ((c.jComp b d).hom.app ((c.J j).obj K))
  have ns₆v := congrArg (fun a ↦ (c.S v₀).map a) ns₆
  dsimp only [Functor.comp_map] at ns₆v
  simp only [Functor.map_comp] at ns₆v
  rw [← reassoc_of% ns₆v]
  rfl

private theorem triangle_naturality_of_projection
    (hp : ∀ {X V Y : G} (j : X ⟶ V) (q : V ⟶ Y)
      [IsOpenImmersion (geo.map j)] {K K' : c.D X} {L L' : c.D Y}
      (a : K ⟶ K') (d : L ⟶ L'),
      (t.tensor Y).map (Prod.mkHom ((compact c j q).map a) d) ≫
          projection c t j q K' L' =
        projection c t j q K L ≫ (compact c j q).map
          ((t.tensor X).map (Prod.mkHom a ((c.P (j ≫ q)).map d))))
    {X V W Y B Z : G} (j : X ⟶ V) (b : V ⟶ W) (q : V ⟶ Y)
    (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion (geo.map j)] [IsOpenImmersion (geo.map b)]
    [IsOpenImmersion (geo.map i)] [QuasiCompact (geo.map b)]
    [QuasiCompact (geo.map i)] [IsProper (geo.map q)] [IsProper (geo.map p)]
    (hb : b ≫ p = q ≫ i) {K K' : c.D X} {L L' : c.D Z}
    (a : K ⟶ K') (d : L ⟶ L') :
    (t.tensor Z).map (Prod.mkHom ((compact c j q ⋙ compact c i s).map a) d) ≫
        rightMap c t j b q p i s hb K' L' =
      rightMap c t j b q p i s hb K L ≫
        (compact c (j ≫ b) (p ≫ s)).map ((t.tensor X).map
          (Prod.mkHom a ((c.P ((j ≫ b) ≫ (p ≫ s))).map d))) := by
  dsimp only [rightMap]
  simp only [← Functor.map_comp_assoc]
  have hn := (alpha c j b q p i s hb).naturality a
  dsimp only [Functor.comp_map] at hn
  rw [show Prod.mkHom ((compact c j q ⋙ compact c i s).map a) d ≫
      Prod.mkHom ((alpha c j b q p i s hb).app K') (𝟙 L') =
      Prod.mkHom ((alpha c j b q p i s hb).app K) (𝟙 L) ≫
        Prod.mkHom ((compact c (j ≫ b) (p ≫ s)).map a) d by
    ext
    · exact hn
    · change d ≫ 𝟙 L' = 𝟙 L ≫ d
      simp]
  simp only [Functor.map_comp, Category.assoc]
  exact congrArg (fun f ↦ (t.tensor Z).map
    (Prod.mkHom ((alpha c j b q p i s hb).app K) (𝟙 L)) ≫ f)
    (hp (j ≫ b) (p ≫ s) a d)

private theorem projection_naturality
    (hpi : ∀ {X Y : G} (f : X ⟶ Y) {M M' : c.D X} {N N' : c.D Y}
      (a : M ⟶ M') (d : N ⟶ N'),
      (t.tensor Y).map (Prod.mkHom ((c.S f).map a) d) ≫ t.pi f M' N' =
        t.pi f M N ≫ (c.S f).map
          ((t.tensor X).map (Prod.mkHom a ((c.P f).map d))))
    (hdelta : ∀ {X Y : G} (j : X ⟶ Y) [IsOpenImmersion (geo.map j)]
      {M M' : c.D X} {N N' : c.D Y} (a : M ⟶ M') (d : N ⟶ N'),
      (t.tensor Y).map (Prod.mkHom ((c.J j).map a) d) ≫ t.delta j M' N' =
        t.delta j M N ≫ (c.J j).map
          ((t.tensor X).map (Prod.mkHom a ((c.P j).map d))))
    {X V Y : G} (j : X ⟶ V) (q : V ⟶ Y) [IsOpenImmersion (geo.map j)]
    {K K' : c.D X} {L L' : c.D Y} (a : K ⟶ K') (d : L ⟶ L') :
    (t.tensor Y).map (Prod.mkHom ((compact c j q).map a) d) ≫
        projection c t j q K' L' =
      projection c t j q K L ≫ (compact c j q).map
        ((t.tensor X).map (Prod.mkHom a ((c.P (j ≫ q)).map d))) := by
  dsimp only [projection, compact, Functor.comp_map]
  rw [reassoc_of% (hpi q ((c.J j).map a) d)]
  simp only [Category.assoc, ← Functor.map_comp]
  congr 1
  apply congrArg (c.S q).map
  rw [reassoc_of% (hdelta j a ((c.P q).map d))]
  simp only [← Functor.map_comp]
  congr 1
  apply congrArg (c.J j).map
  congr 1
  ext
  · simp
  · exact (c.pComp j q).inv.naturality d

private theorem ordinary_projection_naturality
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X V Y : Spaces F} (j : X ⟶ V) (q : V ⟶ Y) [IsOpenImmersion ((geometry F).map j)]
    {K K' : ProperOpenDerived Λ X.obj.left} {L L' : ProperOpenDerived Λ Y.obj.left}
    (a : K ⟶ K') (d : L ⟶ L') :
    ((ordinaryTensor F Λ).tensor Y).map
        (Prod.mkHom ((compact (ordinary F Λ) j q).map a) d) ≫
        projection (ordinary F Λ) (ordinaryTensor F Λ) j q K' L' =
      projection (ordinary F Λ) (ordinaryTensor F Λ) j q K L ≫
        (compact (ordinary F Λ) j q).map (((ordinaryTensor F Λ).tensor X).map
          (Prod.mkHom a (((ordinary F Λ).P (j ≫ q)).map d))) := by
  apply projection_naturality
  · intro X Y f M M' N N' a d
    have h := (Functor.uncurry.map
      (rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f.hom.left)).naturality
        (Prod.mkHom a d)
    simpa [ordinaryTensor, ordinary, properOpenProjection,
      Functor.uncurry_map_app, Functor.uncurry_obj_map,
      derivedTensorRightDerivedLowerStar,
      rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar] using h
  · intro X Y j hj M M' N N' a d
    have : IsOpenImmersion j.hom.left := hj
    have h := (Functor.uncurry.map
      (derivedOpenImmersionLowerShriekProjectionIso
        (ModuleCat.{u + 1} Λ) j.hom.left).inv).naturality (Prod.mkHom a d)
    simpa [ordinaryTensor, ordinary, properOpenTensorIso, Functor.uncurry_map_app,
      Functor.uncurry_obj_map, derivedTensorWhiskeringLeftOpenImmersionLowerShriek,
      derivedTensorWhiskeringRightLeftDerivedUpperStar] using h

open WeilConjectures.IntegralSystemRealization in
private theorem system_projection_naturality (F : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (o : Operations l E) (z : Realizations l E F o)
    {X V Y : Spaces F} (j : X ⟶ V) (q : V ⟶ Y) [IsOpenImmersion ((geometry F).map j)]
    {K K' : System l E X.obj.left} {L L' : System l E Y.obj.left}
    (a : K ⟶ K') (d : L ⟶ L') :
    ((realizedTensor F l E o z).tensor Y).map
        (Prod.mkHom ((compact (realizedSystems F l E o z) j q).map a) d) ≫
        projection (realizedSystems F l E o z) (realizedTensor F l E o z) j q K' L' =
      projection (realizedSystems F l E o z) (realizedTensor F l E o z) j q K L ≫
        (compact (realizedSystems F l E o z) j q).map
          (((realizedTensor F l E o z).tensor X).map
            (Prod.mkHom a (((realizedSystems F l E o z).P (j ≫ q)).map d))) := by
  apply projection_naturality
  · intro X Y f M M' N N' a d
    have h := (Functor.uncurry.map (properProjection l E o f.hom.left)).naturality
      (Prod.mkHom a d)
    simpa [realizedTensor, realizedSystems, Functor.uncurry_obj_map,
      Functor.curryObj, ← Functor.map_comp] using h
  · intro X Y j hj M M' N N' a d
    have : IsOpenImmersion j.hom.left := hj
    exact (z.openComparisons.projection j.hom.left).hom.naturality (Prod.mkHom a d)

private theorem alpha_isIso_of_gamma
    (hgamma : ∀ {V W Y B : G} (b : V ⟶ W) (q : V ⟶ Y)
      (p : W ⟶ B) (i : Y ⟶ B)
      [IsOpenImmersion (geo.map b)] [IsOpenImmersion (geo.map i)]
      [QuasiCompact (geo.map b)] [QuasiCompact (geo.map i)]
      [IsProper (geo.map q)] [IsProper (geo.map p)] (hb : b ≫ p = q ≫ i),
      IsIso (c.gamma b q p i hb))
    {X V W Y B Z : G} (j : X ⟶ V) (b : V ⟶ W) (q : V ⟶ Y)
    (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion (geo.map j)] [IsOpenImmersion (geo.map b)]
    [IsOpenImmersion (geo.map i)] [QuasiCompact (geo.map b)]
    [QuasiCompact (geo.map i)] [IsProper (geo.map q)] [IsProper (geo.map p)]
    (hb : b ≫ p = q ≫ i) : IsIso (alpha c j b q p i s hb) := by
  have := hgamma b q p i hb
  unfold alpha
  infer_instance

private theorem triangleLaws_of_equations
    (he : TriangleEquations c t)
    (hi : ∀ {X V W Y B Z : G} (j : X ⟶ V) (b : V ⟶ W) (q : V ⟶ Y)
      (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
      [IsOpenImmersion (geo.map j)] [IsOpenImmersion (geo.map b)]
      [IsOpenImmersion (geo.map i)] [QuasiCompact (geo.map b)]
      [QuasiCompact (geo.map i)] [IsProper (geo.map q)] [IsProper (geo.map p)]
      (hb : b ≫ p = q ≫ i), IsIso (alpha c j b q p i s hb))
    (hp : ∀ {X V Y : G} (j : X ⟶ V) (q : V ⟶ Y)
      [IsOpenImmersion (geo.map j)] {K K' : c.D X} {L L' : c.D Y}
      (a : K ⟶ K') (d : L ⟶ L'),
      (t.tensor Y).map (Prod.mkHom ((compact c j q).map a) d) ≫
          projection c t j q K' L' =
        projection c t j q K L ≫ (compact c j q).map
          ((t.tensor X).map (Prod.mkHom a ((c.P (j ≫ q)).map d)))) :
    TriangleLaws c t := by
  intro X V W Y B Z j b q p i s _ _ _ _ _ _ _ _ hb
  refine ⟨hi j b q p i s hb, he j b q p i s hb, ?_⟩
  intro K K' L L' a d
  rw [he j b q p i s hb K' L', he j b q p i s hb K L]
  exact triangle_naturality_of_projection c t hp j b q p i s hb a d

attribute [local irreducible] Calculus.sComp Calculus.jComp Calculus.gamma
  Calculus.sCongr Calculus.jCongr Functor.mapDerivedCategory Functor.rightDerivedFunctor

/-- Normalized compact-support composition satisfies the projection identity, naturally
in both arbitrary unbounded inputs, and its compositor is associative for three maps.
Finite coefficients are indexed by n+1, covering exactly all positive levels. The system
clause quantifies over presentations of the specified simultaneous operations, whose
representative normalization is retained by Realizations. There is no Tor, boundedness,
constructibility, Cartesian-square or separated-structure-morphism assumption.
Source: Stacks 0F7B--0F7D, 0F7J--0F7K and blueprint counit calculation
(blueprint: lem-sf-composition-projection-mate).

Proof:
1. The component notation is the unchanged notation of CompositionProjectionData.
   The contraction theorem gives the displayed component equation for every supplied
   triangle, at finite coefficients and for the specified systems.
2. Joint naturality: the proper projections, open tensor maps and pullback compositor are
   natural, so each compactification projection is natural; with naturality of alpha the
   right side, hence by the component equation the left side, is jointly natural.
3. Invertibility: alpha is gamma whiskered by J_j and S_s followed by the proper and open
   compositor isomorphisms. Gamma is invertible: at finite coefficients by the ordinary
   proper/open invertibility theorem, for systems by the supported system counit and the
   recorded open adjunct of gamma.
4. Associativity on the supplied 0F7K grid: expand alpha; vertical pasting expands the
   B+C rectangle and horizontal pasting the A+B rectangle; naturality interchanges the
   disjoint A,C cells; associativity of the proper and open compositors contracts the
   remaining word with its endpoint equality transports. At finite coefficients the four
   inputs are the ambient proper/open pasting laws. For systems, proper and open compositor
   associativity follows from associativity of the section-normalized pullback compositors
   by adjunction conjugation, and the pasting laws are the recorded intrinsic vertical and
   horizontal gamma equations. No evaluation and no choice of refining towers is used.
-/
theorem compositionProjectionMate (F : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ F.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    (TriangleLaws
      (ordinary F (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))
      (ordinaryTensor F (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) ∧
    Associativity
      (ordinary F (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) ∧
    ∀ (o : WeilConjectures.IntegralSystemRealization.Operations l E)
      (z : WeilConjectures.IntegralSystemRealization.Realizations l E F o),
      TriangleLaws (realizedSystems F l E o z) (realizedTensor F l E o z) ∧
        Associativity (realizedSystems F l E o z) := by
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))
  obtain ⟨ho, _ht, _hs, _hst⟩ := ambientProperOpenPasting F l _hl E n
  obtain ⟨he, hes⟩ := triangleProjectionCompositorContraction F l _hl E n
  have hlaws : CompositionLaws (ordinary F A) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro X Y Z T f g h M
      exact ho.s_assoc f g h M
    · intro X Y Z T f g h _ _ _ M
      exact ho.j_assoc f g h M
    · intro A C E₀ B D H k i j r₁ r₂ p₁ p₂ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h M
      exact ho.gamma_vertical k i j r₁ r₂ p₁ p₂ h₁ h₂ h M
    · intro A B E₀ C D H k ll i j r p q _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h M
      exact ho.gamma_horizontal k ll i j r p q h₁ h₂ h M
  refine ⟨?_, associativity_of_laws (ordinary F A) hlaws, ?_⟩
  · apply triangleLaws_of_equations (ordinary F A) (ordinaryTensor F A) he
    · apply alpha_isIso_of_gamma
      intro V W Y B b q p i hb₀ hi₀ hqb hqi hq hp hb
      let : IsOpenImmersion b.hom.left := hb₀
      let : IsOpenImmersion i.hom.left := hi₀
      let : QuasiCompact b.hom.left := hqb
      let : QuasiCompact i.hom.left := hqi
      let : IsProper q.hom.left := hq
      let : IsProper p.hom.left := hp
      simpa only [Calculus.gamma, ordinary, properOpenMate] using
        ordinaryProperOpenMateIsIso A b.hom.left q.hom.left p.hom.left i.hom.left
          (congrArg (fun f ↦ f.hom.left) hb)
    · exact ordinary_projection_naturality F A
  · intro o z
    refine ⟨?_, ?_⟩
    · apply triangleLaws_of_equations (realizedSystems F l E o z)
        (realizedTensor F l E o z) (hes o z)
      · apply alpha_isIso_of_gamma
        intro V W Y B b q p i hb₀ hi₀ hqb hqi hq hp hb
        let : IsOpenImmersion b.hom.left := hb₀
        let : IsOpenImmersion i.hom.left := hi₀
        let : QuasiCompact b.hom.left := hqb
        let : QuasiCompact i.hom.left := hqi
        let : IsProper q.hom.left := hq
        let : IsProper p.hom.left := hp
        simpa only [realizedSystems, Calculus.gamma, Equiv.apply_symm_apply] using
          WeilConjectures.IntegralSystemRealization.systemProperOpenGammaIsIso
            l E o F z b.hom.left q.hom.left p.hom.left i.hom.left
              (congrArg (fun f ↦ f.hom.left) hb)
      · exact system_projection_naturality F l E o z
    · apply associativity_of_laws
      let hp := fun {X Y Z T : Spaces F} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) ↦
        WeilConjectures.IntegralSystemRealization.integralSystemCompositorAssociativity
          l E z.compositors f.hom.left g.hom.left h.hom.left
      refine ⟨direct_assoc_of_pull_assoc _ hp, open_assoc_of_pull_assoc _ hp, ?_, ?_⟩
      · intro A C E₀ B D H k i j r₁ r₂ p₁ p₂ hk hi hj hqk hqi hqj hr₁ hr₂ hp₁ hp₂
          h₁ h₂ h M
        let : IsOpenImmersion k.hom.left := hk
        let : IsOpenImmersion i.hom.left := hi
        let : IsOpenImmersion j.hom.left := hj
        let : QuasiCompact k.hom.left := hqk
        let : QuasiCompact i.hom.left := hqi
        let : QuasiCompact j.hom.left := hqj
        let : IsProper r₁.hom.left := hr₁
        let : IsProper r₂.hom.left := hr₂
        let : IsProper p₁.hom.left := hp₁
        let : IsProper p₂.hom.left := hp₂
        simpa only [realizedSystems, Calculus.gamma, Calculus.sComp,
          WeilConjectures.IntegralSystemRealization.Compositors.pushComp,
          ObjectProperty.FullSubcategory.comp_hom, Over.comp_left, TwoSquare.mk,
          Equiv.apply_symm_apply] using z.properOpen.vertical
            k.hom.left i.hom.left j.hom.left r₁.hom.left r₂.hom.left p₁.hom.left p₂.hom.left
            (congrArg (fun f ↦ f.hom.left) h₁) (congrArg (fun f ↦ f.hom.left) h₂)
            (congrArg (fun f ↦ f.hom.left) h) M
      · intro A B E₀ C D H k ll i j r p q hk hl hi hj hqk hql hqi hqj hr hp hq
          h₁ h₂ h M
        let : IsOpenImmersion k.hom.left := hk
        let : IsOpenImmersion ll.hom.left := hl
        let : IsOpenImmersion i.hom.left := hi
        let : IsOpenImmersion j.hom.left := hj
        let : QuasiCompact k.hom.left := hqk
        let : QuasiCompact ll.hom.left := hql
        let : QuasiCompact i.hom.left := hqi
        let : QuasiCompact j.hom.left := hqj
        let : IsProper r.hom.left := hr
        let : IsProper p.hom.left := hp
        let : IsProper q.hom.left := hq
        simpa only [realizedSystems, Calculus.gamma, Calculus.jComp,
          WeilConjectures.IntegralSystemRealization.Compositors.openComp,
          ObjectProperty.FullSubcategory.comp_hom, Over.comp_left, TwoSquare.mk,
          Equiv.apply_symm_apply] using z.properOpen.horizontal
            k.hom.left ll.hom.left i.hom.left j.hom.left r.hom.left p.hom.left q.hom.left
            (congrArg (fun f ↦ f.hom.left) h₁) (congrArg (fun f ↦ f.hom.left) h₂)
            (congrArg (fun f ↦ f.hom.left) h) M

end AlgebraicGeometry.ProEtale.CompactCompositionProjection
