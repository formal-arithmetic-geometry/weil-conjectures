/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups U1 and E2
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact

/-!
# Linearity of the underived exchange morphism

Source: Stacks Project, Etale Cohomology, Tag 03S6, proof; Modules on Sites,
Tags 03D3, 03D7, 03D8 (blueprint: lem-weil-pbc-underived-exchange-module-linear).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe v u₁ u₂ v₁ v₂

/-- Forgetting a module pushforward map gives the abelian pushforward map. -/
private theorem pushforward_toSheaf_map_for_exchange
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
    [F.IsContinuous J K] {R : Sheaf K RingCat.{v}} {S : Sheaf J RingCat.{v}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R)
    {M N : SheafOfModules.{v} R} (h : M ⟶ N) :
    (SheafOfModules.toSheaf S).map ((SheafOfModules.pushforward φ).map h) =
      (F.sheafPushforwardContinuous AddCommGrpCat.{v} J K).map
        ((SheafOfModules.toSheaf R).map h) := by
  rfl

set_option maxHeartbeats 1000000 in
-- Elaborating the constant-ring pushforward square requires additional heartbeats.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The abelian exchange lifts to a natural transformation of constant-ring module sheaves.
Source: Stacks Project, Tag 03S6, proof, and Tags 03D3, 03D7, 03D8
(blueprint: lem-weil-pbc-underived-exchange-module-linear).

The lambda-bound ring sheaves are the constant sheaves; direct images are the existing
module pushforwards. The universally quantified inverse images,
comparison isomorphisms and compatible adjunctions are precisely the data supplied by
`etaleInverseImageModulesExact`; the conditions on gamma specify the constant-ring map.
They allow any choice of the canonical inverse image rather than fixing a chosen witness.
The comparison formula says that every component of the lifted transformation is the
abelian exchange map, after identifying the underlying abelian inverse images.

Proof:
1. The two composite ring maps agree after the pullback-pasting comparison. By the
   universal property of the constant sheaf, it suffices to check constant sections;
   the four gamma conditions and naturality of the sheafification unit give this.
2. Mathlib's `pushforwardComp` and `pushforwardCongr₂` lift the pushforward square to
   module sheaves. After forgetting it is `Etale.squareLowerStarIso`: both maps are
   restriction along the same pullback-pasting maps.
3. Take its inverse mate under the g' and g module adjunctions. This supplies the
   required natural transformation directly, including naturality.
4. The compatible hom-equivalences identify the module g' unit with the abelian unit.
   Forget the inverse-mate unit formula, use naturality of the pushforward square and
   `Etale.unit_map_baseChangeMap_app`, and apply injectivity of the abelian g adjunction.
   Cancelling the g comparison gives precisely the required component equation. -/
theorem etaleUnderivedExchange_moduleLinear
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (R : CommRingCat.{u + 1}) :
    (fun (RX : Sheaf X.smallEtaleTopology RingCat.{u + 1})
      (RY : Sheaf Y.smallEtaleTopology RingCat.{u + 1})
      (RX' : Sheaf X'.smallEtaleTopology RingCat.{u + 1})
      (RY' : Sheaf Y'.smallEtaleTopology RingCat.{u + 1})
      (etaX : ((Functor.const X.Etaleᵒᵖ).obj
        ((forget₂ CommRingCat RingCat).obj R)) ⟶ RX.obj)
      (etaY : ((Functor.const Y.Etaleᵒᵖ).obj
        ((forget₂ CommRingCat RingCat).obj R)) ⟶ RY.obj)
      (etaX' : ((Functor.const X'.Etaleᵒᵖ).obj
        ((forget₂ CommRingCat RingCat).obj R)) ⟶ RX'.obj)
      (etaY' : ((Functor.const Y'.Etaleᵒᵖ).obj
        ((forget₂ CommRingCat RingCat).obj R)) ⟶ RY'.obj) =>
    ∀ (gamma_f : RY ⟶
      ((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
        RingCat.{u + 1} (Y.smallGrothendieckTopology @Etale)
          (X.smallGrothendieckTopology @Etale)).obj RX),
    (∀ (W : Y.Etaleᵒᵖ) (r : R),
      gamma_f.hom.app W
        (etaY.app W r) =
      etaX.app
          ((MorphismProperty.Over.pullback @Etale ⊤ f).op.obj W) r) →
    ∀ (gamma_fp : RY' ⟶
      ((MorphismProperty.Over.pullback @Etale ⊤ f').sheafPushforwardContinuous
        RingCat.{u + 1} (Y'.smallGrothendieckTopology @Etale)
          (X'.smallGrothendieckTopology @Etale)).obj RX'),
    (∀ (W : Y'.Etaleᵒᵖ) (r : R),
      gamma_fp.hom.app W
        (etaY'.app W r) =
      etaX'.app
          ((MorphismProperty.Over.pullback @Etale ⊤ f').op.obj W) r) →
    ∀ (gamma_g : RY ⟶
      ((MorphismProperty.Over.pullback @Etale ⊤ g).sheafPushforwardContinuous
        RingCat.{u + 1} (Y.smallGrothendieckTopology @Etale)
          (Y'.smallGrothendieckTopology @Etale)).obj RY'),
    (∀ (W : Y.Etaleᵒᵖ) (r : R),
      gamma_g.hom.app W
        (etaY.app W r) =
      etaY'.app
          ((MorphismProperty.Over.pullback @Etale ⊤ g).op.obj W) r) →
    ∀ (gamma_gp : RX ⟶
      ((MorphismProperty.Over.pullback @Etale ⊤ g').sheafPushforwardContinuous
        RingCat.{u + 1} (X.smallGrothendieckTopology @Etale)
          (X'.smallGrothendieckTopology @Etale)).obj RX'),
    (∀ (W : X.Etaleᵒᵖ) (r : R),
      gamma_gp.hom.app W
        (etaX.app W r) =
      etaX'.app
          ((MorphismProperty.Over.pullback @Etale ⊤ g').op.obj W) r) →
    ∀ (L_f : SheafOfModules.{u + 1} RY ⥤ SheafOfModules.{u + 1} RX)
      (e_f : L_f ⋙ SheafOfModules.toSheaf RX ≅
        SheafOfModules.toSheaf RY ⋙ Etale.upperStar AddCommGrpCat.{u + 1} f)
      (a_f : L_f ⊣ (SheafOfModules.pushforward
        (J := Y.smallGrothendieckTopology @Etale)
        (K := X.smallGrothendieckTopology @Etale)
        (F := MorphismProperty.Over.pullback @Etale ⊤ f) gamma_f)),
    (∀ (M : SheafOfModules.{u + 1} RY) (N : SheafOfModules.{u + 1} RX)
      (h : L_f.obj M ⟶ N),
      (SheafOfModules.toSheaf RY).map (a_f.homEquiv M N h) =
        (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv
          ((SheafOfModules.toSheaf RY).obj M) ((SheafOfModules.toSheaf RX).obj N)
          (e_f.inv.app M ≫ (SheafOfModules.toSheaf RX).map h)) →
    ∀ (L_fp : SheafOfModules.{u + 1} RY' ⥤ SheafOfModules.{u + 1} RX')
      (e_fp : L_fp ⋙ SheafOfModules.toSheaf RX' ≅
        SheafOfModules.toSheaf RY' ⋙ Etale.upperStar AddCommGrpCat.{u + 1} f')
      (a_fp : L_fp ⊣ (SheafOfModules.pushforward
        (J := Y'.smallGrothendieckTopology @Etale)
        (K := X'.smallGrothendieckTopology @Etale)
        (F := MorphismProperty.Over.pullback @Etale ⊤ f') gamma_fp)),
    (∀ (M : SheafOfModules.{u + 1} RY') (N : SheafOfModules.{u + 1} RX')
      (h : L_fp.obj M ⟶ N),
      (SheafOfModules.toSheaf RY').map (a_fp.homEquiv M N h) =
        (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f').homEquiv
          ((SheafOfModules.toSheaf RY').obj M) ((SheafOfModules.toSheaf RX').obj N)
          (e_fp.inv.app M ≫ (SheafOfModules.toSheaf RX').map h)) →
    ∀ (L_g : SheafOfModules.{u + 1} RY ⥤ SheafOfModules.{u + 1} RY')
      (e_g : L_g ⋙ SheafOfModules.toSheaf RY' ≅
        SheafOfModules.toSheaf RY ⋙ Etale.upperStar AddCommGrpCat.{u + 1} g)
      (a_g : L_g ⊣ (SheafOfModules.pushforward
        (J := Y.smallGrothendieckTopology @Etale)
        (K := Y'.smallGrothendieckTopology @Etale)
        (F := MorphismProperty.Over.pullback @Etale ⊤ g) gamma_g)),
    (∀ (M : SheafOfModules.{u + 1} RY) (N : SheafOfModules.{u + 1} RY')
      (h : L_g.obj M ⟶ N),
      (SheafOfModules.toSheaf RY).map (a_g.homEquiv M N h) =
        (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv
          ((SheafOfModules.toSheaf RY).obj M) ((SheafOfModules.toSheaf RY').obj N)
          (e_g.inv.app M ≫ (SheafOfModules.toSheaf RY').map h)) →
    ∀ (L_gp : SheafOfModules.{u + 1} RX ⥤ SheafOfModules.{u + 1} RX')
      (e_gp : L_gp ⋙ SheafOfModules.toSheaf RX' ≅
        SheafOfModules.toSheaf RX ⋙ Etale.upperStar AddCommGrpCat.{u + 1} g')
      (a_gp : L_gp ⊣ (SheafOfModules.pushforward
        (J := X.smallGrothendieckTopology @Etale)
        (K := X'.smallGrothendieckTopology @Etale)
        (F := MorphismProperty.Over.pullback @Etale ⊤ g') gamma_gp)),
    (∀ (M : SheafOfModules.{u + 1} RX) (N : SheafOfModules.{u + 1} RX')
      (h : L_gp.obj M ⟶ N),
      (SheafOfModules.toSheaf RX).map (a_gp.homEquiv M N h) =
        (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g').homEquiv
          ((SheafOfModules.toSheaf RX).obj M) ((SheafOfModules.toSheaf RX').obj N)
          (e_gp.inv.app M ≫ (SheafOfModules.toSheaf RX').map h)) →
    ∃ t :
      SheafOfModules.pushforward
        (J := Y.smallGrothendieckTopology @Etale)
        (K := X.smallGrothendieckTopology @Etale)
        (F := MorphismProperty.Over.pullback @Etale ⊤ f) gamma_f ⋙ L_g ⟶
      L_gp ⋙ SheafOfModules.pushforward
        (J := Y'.smallGrothendieckTopology @Etale)
        (K := X'.smallGrothendieckTopology @Etale)
        (F := MorphismProperty.Over.pullback @Etale ⊤ f') gamma_fp,
      ∀ G : SheafOfModules.{u + 1} RX,
        (SheafOfModules.toSheaf RY').map (t.app G) =
          e_g.hom.app ((SheafOfModules.pushforward
            (J := Y.smallGrothendieckTopology @Etale)
            (K := X.smallGrothendieckTopology @Etale)
            (F := MorphismProperty.Over.pullback @Etale ⊤ f) gamma_f).obj G) ≫
          (Etale.baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app
            ((SheafOfModules.toSheaf RX).obj G) ≫
          (Etale.lowerStar AddCommGrpCat.{u + 1} f').map (e_gp.inv.app G))
      ((constantSheaf X.smallEtaleTopology RingCat.{u + 1}).obj
        ((forget₂ CommRingCat RingCat).obj R))
      ((constantSheaf Y.smallEtaleTopology RingCat.{u + 1}).obj
        ((forget₂ CommRingCat RingCat).obj R))
      ((constantSheaf X'.smallEtaleTopology RingCat.{u + 1}).obj
        ((forget₂ CommRingCat RingCat).obj R))
      ((constantSheaf Y'.smallEtaleTopology RingCat.{u + 1}).obj
        ((forget₂ CommRingCat RingCat).obj R))
      (toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj ((forget₂ CommRingCat RingCat).obj R)))
      (toSheafify Y.smallEtaleTopology
        ((Functor.const Y.Etaleᵒᵖ).obj ((forget₂ CommRingCat RingCat).obj R)))
      (toSheafify X'.smallEtaleTopology
        ((Functor.const X'.Etaleᵒᵖ).obj ((forget₂ CommRingCat RingCat).obj R)))
      (toSheafify Y'.smallEtaleTopology
        ((Functor.const Y'.Etaleᵒᵖ).obj ((forget₂ CommRingCat RingCat).obj R))) := by
  classical
  intro gamma_f hf gamma_fp hfp gamma_g hg gamma_gp hgp
    L_f e_f a_f ha_f L_fp e_fp a_fp ha_fp L_g e_g a_g ha_g L_gp e_gp a_gp ha_gp
  let RX := (constantSheaf X.smallEtaleTopology RingCat.{u + 1}).obj
    ((forget₂ CommRingCat RingCat).obj R)
  let RY := (constantSheaf Y.smallEtaleTopology RingCat.{u + 1}).obj
    ((forget₂ CommRingCat RingCat).obj R)
  let RX' := (constantSheaf X'.smallEtaleTopology RingCat.{u + 1}).obj
    ((forget₂ CommRingCat RingCat).obj R)
  let RY' := (constantSheaf Y'.smallEtaleTopology RingCat.{u + 1}).obj
    ((forget₂ CommRingCat RingCat).obj R)
  let Ff := MorphismProperty.Over.pullback @Etale ⊤ f
  let Ffp := MorphismProperty.Over.pullback @Etale ⊤ f'
  let Fg := MorphismProperty.Over.pullback @Etale ⊤ g
  let Fgp := MorphismProperty.Over.pullback @Etale ⊤ g'
  let Pf := SheafOfModules.pushforward.{u + 1}
    (J := Y.smallGrothendieckTopology (Q := @Etale) @Etale)
    (K := X.smallGrothendieckTopology (Q := @Etale) @Etale) gamma_f
  let Pfp := SheafOfModules.pushforward.{u + 1}
    (J := Y'.smallGrothendieckTopology (Q := @Etale) @Etale)
    (K := X'.smallGrothendieckTopology (Q := @Etale) @Etale) gamma_fp
  let Pg := SheafOfModules.pushforward.{u + 1}
    (J := Y.smallGrothendieckTopology (Q := @Etale) @Etale)
    (K := Y'.smallGrothendieckTopology (Q := @Etale) @Etale) gamma_g
  let Pgp := SheafOfModules.pushforward.{u + 1}
    (J := X.smallGrothendieckTopology (Q := @Etale) @Etale)
    (K := X'.smallGrothendieckTopology (Q := @Etale) @Etale) gamma_gp
  let α : Fg ⋙ Ffp ≅ Ff ⋙ Fgp :=
    (MorphismProperty.Over.pullbackComp f' g (g' ≫ f) sq.w).symm ≪≫
      MorphismProperty.Over.pullbackComp g' f
  let : (Ff ⋙ Fgp).IsContinuous
      (Y.smallGrothendieckTopology (Q := @Etale) @Etale)
      (X'.smallGrothendieckTopology (Q := @Etale) @Etale) :=
    Functor.isContinuous_comp Ff Fgp _ (X.smallGrothendieckTopology @Etale) _
  let : (Fg ⋙ Ffp).IsContinuous
      (Y.smallGrothendieckTopology (Q := @Etale) @Etale)
      (X'.smallGrothendieckTopology (Q := @Etale) @Etale) :=
    Functor.isContinuous_comp Fg Ffp _ (Y'.smallGrothendieckTopology @Etale) _
  let φ : RY ⟶ ((Ff ⋙ Fgp).sheafPushforwardContinuous RingCat.{u + 1}
      (Y.smallGrothendieckTopology (Q := @Etale) @Etale)
      (X'.smallGrothendieckTopology (Q := @Etale) @Etale)).obj RX' :=
    gamma_f ≫ (Ff.sheafPushforwardContinuous RingCat.{u + 1}
      (Y.smallGrothendieckTopology (Q := @Etale) @Etale)
      (X.smallGrothendieckTopology (Q := @Etale) @Etale)).map gamma_gp
  let ψ : RY ⟶ ((Fg ⋙ Ffp).sheafPushforwardContinuous RingCat.{u + 1}
      (Y.smallGrothendieckTopology (Q := @Etale) @Etale)
      (X'.smallGrothendieckTopology (Q := @Etale) @Etale)).obj RX' :=
    gamma_g ≫ (Fg.sheafPushforwardContinuous RingCat.{u + 1}
      (Y.smallGrothendieckTopology (Q := @Etale) @Etale)
      (Y'.smallGrothendieckTopology (Q := @Etale) @Etale)).map gamma_fp
  have hφψ : φ ≫ (Functor.sheafPushforwardContinuousNatTrans α.hom
      RingCat.{u + 1} (Y.smallGrothendieckTopology (Q := @Etale) @Etale)
      (X'.smallGrothendieckTopology (Q := @Etale) @Etale)).app RX' = ψ := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext Y.smallEtaleTopology _ _
      (((Fg ⋙ Ffp).sheafPushforwardContinuous RingCat.{u + 1}
        (Y.smallGrothendieckTopology (Q := @Etale) @Etale)
        (X'.smallGrothendieckTopology (Q := @Etale) @Etale)).obj RX').property
    ext W r
    dsimp [φ, ψ]
    erw [hf, hgp, hg, hfp]
    simpa [RX', constantSheaf, Ff, Fg, Ffp, Fgp] using (CategoryTheory.congr_fun
      ((toSheafify X'.smallEtaleTopology
        ((Functor.const X'.Etaleᵒᵖ).obj ((forget₂ CommRingCat RingCat).obj R))).naturality
          (α.hom.app W.unop).op) r).symm
  let d : Pgp ⋙ Pf ≅ Pfp ⋙ Pg :=
    SheafOfModules.pushforwardComp.{u + 1}
      (J := Y.smallGrothendieckTopology (Q := @Etale) @Etale)
      (K := X.smallGrothendieckTopology (Q := @Etale) @Etale)
      (K' := X'.smallGrothendieckTopology (Q := @Etale) @Etale) gamma_f gamma_gp ≪≫
      SheafOfModules.pushforwardCongr₂.{u + 1}
        (J := Y.smallGrothendieckTopology (Q := @Etale) @Etale)
        (K := X'.smallGrothendieckTopology (Q := @Etale) @Etale) φ α hφψ ≪≫
      (SheafOfModules.pushforwardComp.{u + 1}
      (J := Y.smallGrothendieckTopology (Q := @Etale) @Etale)
      (K := Y'.smallGrothendieckTopology (Q := @Etale) @Etale)
      (K' := X'.smallGrothendieckTopology (Q := @Etale) @Etale) gamma_g gamma_fp).symm
  let UX := SheafOfModules.toSheaf RX
  let UY := SheafOfModules.toSheaf RY
  let UX' := SheafOfModules.toSheaf RX'
  let UY' := SheafOfModules.toSheaf RY'
  have hd (G : SheafOfModules.{u + 1} RX') :
      UY.map (d.hom.app G) =
        (Etale.squareLowerStarIso AddCommGrpCat.{u + 1} sq.toCommSq).hom.app (UX'.obj G) := by
    ext W x
    change G.val.map (α.hom.app W.unop).op x =
      G.val.map
        ((MorphismProperty.Over.pullbackComp f' g (g' ≫ f) sq.w).inv.app W.unop).op
        (G.val.map
          ((MorphismProperty.Over.pullbackComp g' f).hom.app W.unop).op x)
    exact G.val.map_comp_apply
      ((MorphismProperty.Over.pullbackComp g' f).hom.app W.unop).op
      ((MorphismProperty.Over.pullbackComp f' g (g' ≫ f) sq.w).inv.app W.unop).op x
  clear_value d
  let t : Pf ⋙ L_g ⟶ L_gp ⋙ Pfp :=
    ((mateEquiv a_gp a_g).symm (TwoSquare.mk _ _ _ _ d.hom)).natTrans
  refine ⟨t, ?_⟩
  intro G
  have hunit (M : SheafOfModules.{u + 1} RX) :
      UX.map (a_gp.unit.app M) =
        (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g').unit.app (UX.obj M) ≫
          (Etale.lowerStar AddCommGrpCat.{u + 1} g').map (e_gp.inv.app M) := by
    simpa [Adjunction.homEquiv_apply] using ha_gp M (L_gp.obj M) (𝟙 _)
  have ht : a_g.homEquiv (Pf.obj G) (Pfp.obj (L_gp.obj G)) (t.app G) =
      Pf.map (a_gp.unit.app G) ≫ d.hom.app (L_gp.obj G) := by
    exact (unit_mateEquiv_symm a_gp a_g (TwoSquare.mk _ _ _ _ d.hom) G).symm
  clear_value t
  have h := ha_g (Pf.obj G) (Pfp.obj (L_gp.obj G)) (t.app G)
  change UY.map (a_g.homEquiv (Pf.obj G) (Pfp.obj (L_gp.obj G)) (t.app G)) = _ at h
  rw [ht, Functor.map_comp, hd] at h
  clear ha_f a_f e_f L_f ha_fp a_fp e_fp L_fp hf hgp hg hfp hφψ φ ψ α ht hd d
  have hp := pushforward_toSheaf_map_for_exchange (F := Ff)
    (J := Y.smallGrothendieckTopology (Q := @Etale) @Etale)
    (K := X.smallGrothendieckTopology (Q := @Etale) @Etale)
    (R := RX) (S := RY) gamma_f (a_gp.unit.app G)
  have hq := congrArg (fun z => z ≫
      (Etale.squareLowerStarIso AddCommGrpCat.{u + 1} sq.toCommSq).hom.app
        (UX'.obj (L_gp.obj G))) hp
  have h := hq.symm.trans h
  have hu := congrArg (fun z => (Etale.lowerStar AddCommGrpCat.{u + 1} f).map z ≫
      (Etale.squareLowerStarIso AddCommGrpCat.{u + 1} sq.toCommSq).hom.app
        (UX'.obj (L_gp.obj G))) (hunit G)
  have h := hu.symm.trans h
  have hm := (Etale.lowerStar AddCommGrpCat.{u + 1} f).map_comp
    ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g').unit.app (UX.obj G))
    ((Etale.lowerStar AddCommGrpCat.{u + 1} g').map (e_gp.inv.app G))
  have hv := congrArg (fun z => z ≫
      (Etale.squareLowerStarIso AddCommGrpCat.{u + 1} sq.toCommSq).hom.app
        (UX'.obj (L_gp.obj G))) hm
  have h := hv.symm.trans h
  have hn := (Etale.squareLowerStarIso AddCommGrpCat.{u + 1} sq.toCommSq).hom.naturality
    (e_gp.inv.app G)
  change (Etale.lowerStar AddCommGrpCat.{u + 1} f).map
      ((Etale.lowerStar AddCommGrpCat.{u + 1} g').map (e_gp.inv.app G)) ≫ _ = _ at hn
  erw [Category.assoc, hn] at h
  erw [← Category.assoc,
    ← Etale.unit_map_baseChangeMap_app AddCommGrpCat.{u + 1} sq.toCommSq (UX.obj G)] at h
  have hh :
      (Etale.baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app (UX.obj G) ≫
          (Etale.lowerStar AddCommGrpCat.{u + 1} f').map (e_gp.inv.app G) =
        e_g.inv.app (Pf.obj G) ≫ UY'.map (t.app G) := by
    apply ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv
      ((Etale.lowerStar AddCommGrpCat.{u + 1} f).obj (UX.obj G))
      ((Etale.lowerStar AddCommGrpCat.{u + 1} f').obj (UX'.obj (L_gp.obj G)))).injective
    simp only [Adjunction.homEquiv_apply, Functor.map_comp]
    simp only [Functor.comp_map, Category.assoc] at h
    ext W x
    exact congrArg (fun k => k.hom.app W x) h
  calc
    UY'.map (t.app G) =
        e_g.hom.app (Pf.obj G) ≫ (e_g.inv.app (Pf.obj G) ≫ UY'.map (t.app G)) := by
      simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    _ = _ := by rw [← hh]

end AlgebraicGeometry
