/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.AlgebraicGeometry.EtaleModuleSetPullbackComparison
public import WeilConjectures.AlgebraicGeometry.EtaleSetSectionsFlatConnectedFibres
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-!
# Sections of inverse images along flat morphisms with geometrically connected fibres

Let `p : X ⟶ S` be a morphism of schemes, `V` an étale `S`-scheme, `W` an étale `X`-scheme and
`φ : W ⟶ V ×_S X` a morphism of étale `X`-schemes such that the induced morphism `q : W ⟶ V` is
flat, quasi-compact with geometrically connected fibres. For every étale sheaf `G` of modules
on `S`, the map `G(V) ⟶ (p^* G)(V ×_S X) ⟶ (p^* G)(W)` is bijective [Stacks 0A3H].

The case of global sections (`V = S`, `W = X`, `p = q`) for sheaves of sets is
`AlgebraicGeometry.etaleSet_sections_bijective_of_flat_qc_connected_geometricFibres`; it is
transferred to sheaves of modules by `AlgebraicGeometry.Etale.isIso_upperStar_forget_comparison`.
The general case reduces to it: for an étale `j : W ⟶ X` the sections of a sheaf over `W` are the
global sections of its pullback along `j`
(`AlgebraicGeometry.Etale.isIso_unit_app_comp_map_of_etale`), and the units of the adjunctions
`g^* ⊣ g_*` are compatible with the composition isomorphisms
(`AlgebraicGeometry.Etale.unit_app_map_unit_app_map_upperStarComp_inv`).

## Main statements

- `AlgebraicGeometry.Etale.isIso_unit_app_mkId_of_geometricallyConnected`: the case of global
  sections.
- `AlgebraicGeometry.Etale.isIso_unit_app_comp_map_of_geometricallyConnected`: the general case.

## References

- Stacks Project, Lemma 59.39.3, <https://stacks.math.columbia.edu/tag/0A3H>
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

open Scheme

/-- A morphism of étale `X`-schemes whose underlying morphism of schemes is an isomorphism is an
isomorphism. -/
lemma isIso_of_isIso_left' {X : Scheme.{u}} {V W : X.Etale} (f : V ⟶ W) (hf : IsIso f.left) :
    IsIso f := by
  have : IsIso ((Over.forget X).map ((Scheme.Etale.forget X).map f)) := hf
  have : IsIso ((Scheme.Etale.forget X).map f) :=
    isIso_of_reflects_iso _ (Over.forget X)
  exact isIso_of_reflects_iso f (Scheme.Etale.forget X)

section Coefficients

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

/-- The components of an isomorphism of sheaves are isomorphisms. -/
instance isIso_hom_app_of_isIso {X : Scheme.{u}} {F F' : Sheaf X.smallEtaleTopology A}
    (e : F ⟶ F') [IsIso e] (U : X.Etaleᵒᵖ) : IsIso (e.hom.app U) := by
  have : IsIso e.hom := inferInstanceAs (IsIso ((sheafToPresheaf _ _).map e))
  infer_instance

omit [HasSmallSiteSheafify A] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- For an étale `f : T ⟶ Y`, the unit of `f^* ⊣ f_*` followed by the restriction along
`ψ : c ⟶ b ×_Y T` is, under the identification of `f^*` with the restriction along the
localization functor, the restriction along the adjoint morphism `c ⟶ b` of étale
`Y`-schemes. -/
lemma unit_app_comp_map_comp_upperStarIsoLocalizationRestriction {T Y : Scheme.{u}}
    (f : T ⟶ Y) [Etale f] (F : Sheaf Y.smallEtaleTopology A) (b : Y.Etale) (c : T.Etale)
    (ψ : c ⟶ (MorphismProperty.Over.pullback @Etale ⊤ f).obj b) :
    ((upperStarLowerStarAdjunction A f).unit.app F).hom.app (op b) ≫
        ((f)^*[A].obj F).obj.map ψ.op ≫
        ((upperStarIsoLocalizationRestriction A f inferInstance).hom.app F).hom.app (op c) =
      F.obj.map (((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ f inferInstance
        _root_.trivial).homEquiv c b).symm ψ).op := by
  let ρ := (upperStarIsoLocalizationRestriction A f inferInstance).hom.app F
  have hu := congrArg (fun α ↦ α.hom.app (op b))
    (Adjunction.unit_leftAdjointUniq_hom_app (upperStarLowerStarAdjunction A f)
      (localizationRestrictionLowerStarAdjunction A f inferInstance) F)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at hu
  rw [ρ.hom.naturality, ← Category.assoc]
  erw [show ((upperStarLowerStarAdjunction A f).unit.app F).hom.app (op b) ≫
    ρ.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj b)) =
    ((localizationRestrictionLowerStarAdjunction A f inferInstance).unit.app F).hom.app
      (op b) from hu]
  change (𝟙 _ ≫ F.obj.map _ ≫ 𝟙 _) ≫ F.obj.map _ = _
  simp only [Category.id_comp, Category.comp_id, ← Functor.map_comp]
  rfl

omit [HasSmallSiteSheafify A] in
/-- For an étale `f : T ⟶ Y` and a morphism `ψ : c ⟶ b ×_Y T` of étale `T`-schemes whose
composite with the projection to `b` is an isomorphism, the unit of `f^* ⊣ f_*` at `b`
followed by the restriction along `ψ` is an isomorphism `F(b) ≅ (f^* F)(c)`. -/
lemma isIso_unit_app_comp_map_of_etale {T Y : Scheme.{u}} (f : T ⟶ Y) [Etale f]
    (F : Sheaf Y.smallEtaleTopology A) (b : Y.Etale) (c : T.Etale)
    (ψ : c ⟶ (MorphismProperty.Over.pullback @Etale ⊤ f).obj b)
    (hψ : IsIso (ψ.left ≫ pullback.fst b.hom f)) :
    IsIso (((upperStarLowerStarAdjunction A f).unit.app F).hom.app (op b) ≫
        ((f)^*[A].obj F).obj.map ψ.op) := by
  have h := unit_app_comp_map_comp_upperStarIsoLocalizationRestriction A f F b c ψ
  have : IsIso (((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ f inferInstance
      _root_.trivial).homEquiv c b).symm ψ) := by
    apply isIso_of_isIso_left'
    rw [Adjunction.homEquiv_counit]
    simpa [MorphismProperty.Over.mapPullbackAdj] using hψ
  rw [← Category.assoc] at h
  have : IsIso ((((upperStarLowerStarAdjunction A f).unit.app F).hom.app (op b) ≫
      ((f)^*[A].obj F).obj.map ψ.op) ≫
        ((upperStarIsoLocalizationRestriction A f inferInstance).hom.app F).hom.app (op c)) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (((upperStarIsoLocalizationRestriction A f inferInstance).hom.app F).hom.app (op c))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The unit of `(f ≫ g)^* ⊣ (f ≫ g)_*`, followed by a restriction and the composition
isomorphism, is the composite of the units of `g^* ⊣ g_*` and `f^* ⊣ f_*`. -/
lemma unit_app_map_comp_upperStarComp_hom {T Y R : Scheme.{u}}
    (f : T ⟶ Y) (g : Y ⟶ R) (t : T ⟶ R) (ht : t = f ≫ g)
    (F : Sheaf R.smallEtaleTopology A) (b : R.Etale) (c : T.Etale)
    (ψ : c ⟶ (MorphismProperty.Over.pullback @Etale ⊤ t).obj b) :
    ((upperStarLowerStarAdjunction A t).unit.app F).hom.app (op b) ≫
        ((t)^*[A].obj F).obj.map ψ.op ≫
        ((upperStarComp A f g t ht).hom.app F).hom.app (op c) =
      ((upperStarLowerStarAdjunction A g).unit.app F).hom.app (op b) ≫
        ((upperStarLowerStarAdjunction A f).unit.app ((g)^*[A].obj F)).hom.app
            (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj b)) ≫
        ((f)^*[A].obj ((g)^*[A].obj F)).obj.map
          (ψ ≫ (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f g t ht).hom.app
            b).op := by
  have h := congrArg (fun α ↦ α.hom.app (op b))
    (upperStarComp_hom_app_unit_app A f g F t ht)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Adjunction.comp_unit_app, lowerStarComp,
    Functor.sheafPushforwardContinuousComp'_hom_app_hom_app] at h
  rw [((upperStarComp A f g t ht).hom.app F).hom.naturality, ← Category.assoc]
  erw [h]
  simp only [Functor.comp_obj, Iso.symm_inv, lowerStar_map_hom_app, Category.assoc,
    ← Functor.map_comp, ← op_comp]

/-- Two morphisms of étale `T'`-schemes into an iterated base change `(b ×_R T) ×_T T'` agree
as soon as their projections to `b` agree. -/
lemma hom_ext_pullback_pullback {R T T' : Scheme.{u}} (t : T ⟶ R) (f : T' ⟶ T) {b : R.Etale}
    {c' : T'.Etale}
    {x y : c' ⟶ (MorphismProperty.Over.pullback @Etale ⊤ f).obj
      ((MorphismProperty.Over.pullback @Etale ⊤ t).obj b)}
    (h : x.left ≫ pullback.fst _ f ≫ pullback.fst b.hom t =
      y.left ≫ pullback.fst _ f ≫ pullback.fst b.hom t) : x = y := by
  have hx := MorphismProperty.Over.w x
  have hy := MorphismProperty.Over.w y
  simp only [MorphismProperty.Over.pullback_obj_hom] at hx hy
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext _ (hx.trans hy.symm)
  apply pullback.hom_ext h
  have e : pullback.fst ((MorphismProperty.Over.pullback @Etale ⊤ t).obj b).hom f ≫
      pullback.snd b.hom t =
      pullback.snd ((MorphismProperty.Over.pullback @Etale ⊤ t).obj b).hom f ≫ f :=
    pullback.condition
  have key (z : c' ⟶ (MorphismProperty.Over.pullback @Etale ⊤ f).obj
      ((MorphismProperty.Over.pullback @Etale ⊤ t).obj b))
      (hz : z.left ≫ pullback.snd ((MorphismProperty.Over.pullback @Etale ⊤ t).obj b).hom f =
        c'.hom) :
      (z.left ≫ pullback.fst ((MorphismProperty.Over.pullback @Etale ⊤ t).obj b).hom f) ≫
        pullback.snd b.hom t = c'.hom ≫ f :=
    (Category.assoc _ _ _).trans ((congrArg (z.left ≫ ·) e).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ f) hz)))
  exact (key x hx).trans (key y hy).symm

/-- Compatibility of the units of the adjunctions `g^* ⊣ g_*` with the composition
isomorphisms: for `t' = f ≫ t`, the unit of `t^* ⊣ t_*` at `b`, restricted along
`ψ : c ⟶ b ×_R T`, followed by the unit of `f^* ⊣ f_*` at `c`, restricted along
`ψ' : c' ⟶ c ×_T T'`, is the unit of `t'^* ⊣ t'_*` at `b` restricted along any morphism
`χ : c' ⟶ b ×_R T'` with the same projection to `b`. -/
lemma unit_app_map_unit_app_map_upperStarComp_inv {R T T' : Scheme.{u}} (t : T ⟶ R)
    (f : T' ⟶ T) (t' : T' ⟶ R) (ht : t' = f ≫ t) (G : Sheaf R.smallEtaleTopology A)
    {b : R.Etale} {c : T.Etale} {c' : T'.Etale}
    (ψ : c ⟶ (MorphismProperty.Over.pullback @Etale ⊤ t).obj b)
    (ψ' : c' ⟶ (MorphismProperty.Over.pullback @Etale ⊤ f).obj c)
    (χ : c' ⟶ (MorphismProperty.Over.pullback @Etale ⊤ t').obj b)
    (hχ : χ.left ≫ pullback.fst b.hom t' =
      ψ'.left ≫ pullback.fst c.hom f ≫ ψ.left ≫ pullback.fst b.hom t) :
    ((upperStarLowerStarAdjunction A t).unit.app G).hom.app (op b) ≫
        ((t)^*[A].obj G).obj.map ψ.op ≫
        ((upperStarLowerStarAdjunction A f).unit.app ((t)^*[A].obj G)).hom.app (op c) ≫
        ((f)^*[A].obj ((t)^*[A].obj G)).obj.map ψ'.op ≫
        ((upperStarComp A f t t' ht).inv.app G).hom.app (op c') =
      ((upperStarLowerStarAdjunction A t').unit.app G).hom.app (op b) ≫
        ((t')^*[A].obj G).obj.map χ.op := by
  have hcomp := unit_app_map_comp_upperStarComp_hom A f t t' ht G b c' χ
  have hnat := ((upperStarLowerStarAdjunction A f).unit.app ((t)^*[A].obj G)).hom.naturality
    ψ.op
  have hinv : ((upperStarComp A f t t' ht).hom.app G).hom.app (op c') ≫
      ((upperStarComp A f t t' ht).inv.app G).hom.app (op c') = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom, Iso.hom_inv_id_app]
    rfl
  have hχ' : χ ≫ (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f t t' ht).hom.app
      b = ψ' ≫ (MorphismProperty.Over.pullback @Etale ⊤ f).map ψ := by
    apply hom_ext_pullback_pullback
    subst ht
    simp only [Functor.id_obj, Functor.comp_obj, Etale.comp_left_eq,
      MorphismProperty.Over.pullbackComp_hom_app_left, pullback.map_id, Category.id_comp,
      Functor.const_obj_obj, Category.assoc, MorphismProperty.Over.pullback_map_left,
      limit.lift_π_assoc, cospan_left, PullbackCone.mk_π_app]
    erw [pullbackLeftPullbackSndIso_inv_fst]
    exact hχ
  calc _ = ((upperStarLowerStarAdjunction A t).unit.app G).hom.app (op b) ≫
        ((upperStarLowerStarAdjunction A f).unit.app ((t)^*[A].obj G)).hom.app
            (op ((MorphismProperty.Over.pullback @Etale ⊤ t).obj b)) ≫
        ((f)^*[A].obj ((t)^*[A].obj G)).obj.map
          (χ ≫ (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f t t' ht).hom.app
            b).op ≫
        ((upperStarComp A f t t' ht).inv.app G).hom.app (op c') := by
        rw [hχ', op_comp, Functor.map_comp]
        erw [reassoc_of% hnat]
        simp only [Category.assoc]
        rfl
    _ = _ := by
        rw [← reassoc_of% hcomp]
        simp only [hinv, Category.comp_id]

end Coefficients

section GeometricallyConnected

set_option backward.isDefEq.respectTransparency false in
/-- Global sections case of [Stacks 0A3H] for sheaves of modules: for a flat, quasi-compact
morphism `f : T ⟶ S` with geometrically connected fibres, the unit of `f^* ⊣ f_*` induces a
bijection `G(S) ⟶ (f^* G)(S ×_S T)`. -/
theorem isIso_unit_app_mkId_of_geometricallyConnected (R : Type (u + 1)) [Ring R]
    {S T : Scheme.{u}} (f : T ⟶ S) [Flat f] [QuasiCompact f] [GeometricallyConnected f]
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    IsIso (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f).unit.app G).hom.app
      (op (Scheme.Etale.mk (𝟙 S)))) := by
  let U := forget (ModuleCat.{u + 1} R)
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
    (S.smallGrothendieckTopology (Q := @Etale) @Etale)
    (T.smallGrothendieckTopology (Q := @Etale) @Etale)
  let F := (sheafCompose S.smallEtaleTopology U).obj G
  let H := (sheafCompose T.smallEtaleTopology U).obj ((f)^*[ModuleCat.{u + 1} R].obj G)
  let η := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f).unit.app G
  let c := (adj.homEquiv F H).symm ((sheafCompose S.smallEtaleTopology U).map η)
  have hiso : IsIso c := isIso_upperStar_forget_comparison R f G
  have hη : adj.homEquiv F H c = (sheafCompose S.smallEtaleTopology U).map η :=
    (adj.homEquiv F H).apply_symm_apply _
  rw [Adjunction.homEquiv_unit] at hη
  have h1 := congrArg (fun φ ↦ φ.hom.app (op (Scheme.Etale.mk (𝟙 S)))) hη
  have hconn : ∀ s : S, ConnectedSpace
      (pullback f
        (Spec.map (CommRingCat.ofHom
          (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
            S.fromSpecResidueField s) : Scheme.{u}) := fun s ↦
    GeometricallyConnected.geometrically_connectedSpace (f := f) _ _ _
      (IsPullback.of_hasPullback _ _)
  have hb := etaleSet_sections_bijective_of_flat_qc_connected_geometricFibres f hconn F
  have : IsIso c.hom := inferInstanceAs (IsIso ((sheafToPresheaf _ _).map c))
  have hc : Function.Bijective (c.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj
      (Scheme.Etale.mk (𝟙 S))))) := by
    rw [← isIso_iff_bijective]
    infer_instance
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective (U.map (η.hom.app (op (Scheme.Etale.mk (𝟙 S)))))
  have h2 : U.map (η.hom.app (op (Scheme.Etale.mk (𝟙 S)))) =
      (adj.unit.app F).hom.app (op (Scheme.Etale.mk (𝟙 S))) ≫
        c.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj
          (Scheme.Etale.mk (𝟙 S)))) :=
    h1.symm
  rw [h2]
  exact hc.comp hb

/-- **Sections of an inverse image along a flat morphism with geometrically connected fibres**
[Stacks 0A3H]. Let `φ : W ⟶ V ×_S X` be a morphism of étale `X`-schemes, `V` an étale
`S`-scheme, such that the induced morphism `q : W ⟶ V` is flat, quasi-compact and has
geometrically connected fibres. Then for every étale sheaf `G` of modules on `S`, the unit of
`p^* ⊣ p_*` at `V` followed by the restriction along `φ` is a bijection
`G(V) ≅ (p^* G)(W)`.

Writing `j : W ⟶ X` and `r : V ⟶ S` for the structure morphisms, `j ≫ p = q ≫ r`, the map
is identified, through the bijections `(p^* G)(W) ≅ (j^* p^* G)(W) ≅ ((j ≫ p)^* G)(W)` and
`G(V) ≅ (r^* G)(V)` for the étale morphisms `j` and `r`, with the map on global sections
`(r^* G)(V) ⟶ (q^* r^* G)(W) ≅ ((q ≫ r)^* G)(W)`, which is bijective by
`AlgebraicGeometry.Etale.isIso_unit_app_mkId_of_geometricallyConnected`. -/
@[stacks 0A3H]
theorem isIso_unit_app_comp_map_of_geometricallyConnected (R : Type (u + 1)) [Ring R]
    {X S : Scheme.{u}} (p : X ⟶ S) (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} R))
    {V : S.Etale} {W : X.Etale} (φ : W ⟶ (MorphismProperty.Over.pullback @Etale ⊤ p).obj V)
    [Flat (φ.left ≫ pullback.fst V.hom p)] [QuasiCompact (φ.left ≫ pullback.fst V.hom p)]
    [GeometricallyConnected (φ.left ≫ pullback.fst V.hom p)] :
    IsIso (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) p).unit.app G).hom.app (op V) ≫
      ((p)^*[ModuleCat.{u + 1} R].obj G).obj.map φ.op) := by
  let A := ModuleCat.{u + 1} R
  let q := φ.left ≫ pullback.fst V.hom p
  have hq : q ≫ V.hom = W.hom ≫ p := by
    have hw : φ.left ≫ pullback.snd V.hom p = W.hom := MorphismProperty.Over.w φ
    simp only [q, Category.assoc, pullback.condition, reassoc_of% hw]
  have : Etale W.hom := W.prop
  have : Etale V.hom := V.prop
  let IW : W.left.Etale := Scheme.Etale.mk (𝟙 W.left)
  let IV : V.left.Etale := Scheme.Etale.mk (𝟙 V.left)
  let δW : IW ⟶ (MorphismProperty.Over.pullback @Etale ⊤ W.hom).obj W :=
    MorphismProperty.Over.homMk (pullback.lift (𝟙 W.left) (𝟙 W.left) rfl)
      (pullback.lift_snd _ _ _)
  let δV : IV ⟶ (MorphismProperty.Over.pullback @Etale ⊤ V.hom).obj V :=
    MorphismProperty.Over.homMk (pullback.lift (𝟙 V.left) (𝟙 V.left) rfl)
      (pullback.lift_snd _ _ _)
  let γ : IW ⟶ (MorphismProperty.Over.pullback @Etale ⊤ q).obj IV :=
    MorphismProperty.Over.homMk (pullback.lift (f := 𝟙 V.left) q (𝟙 W.left)
      ((Category.comp_id q).trans (Category.id_comp q).symm)) (pullback.lift_snd _ _ _)
  let χ : IW ⟶ (MorphismProperty.Over.pullback @Etale ⊤ (W.hom ≫ p)).obj V :=
    MorphismProperty.Over.homMk (pullback.lift q (𝟙 W.left) (hq.trans (Category.id_comp _).symm))
      (pullback.lift_snd _ _ _)
  have e₁ := unit_app_map_unit_app_map_upperStarComp_inv A p W.hom (W.hom ≫ p) rfl G φ δW χ
    (by
      change pullback.lift q (𝟙 W.left) _ ≫ pullback.fst V.hom (W.hom ≫ p) =
        pullback.lift (𝟙 W.left) (𝟙 W.left) rfl ≫ pullback.fst W.hom W.hom ≫ q
      rw [pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp])
  have e₂ := unit_app_map_unit_app_map_upperStarComp_inv A V.hom q (W.hom ≫ p) hq.symm G δV γ χ
    (by
      change pullback.lift q (𝟙 W.left) _ ≫ pullback.fst V.hom (W.hom ≫ p) =
        pullback.lift (f := 𝟙 V.left) q (𝟙 W.left) _ ≫ pullback.fst (𝟙 V.left) q ≫
          pullback.lift (𝟙 V.left) (𝟙 V.left) rfl ≫ pullback.fst V.hom V.hom
      rw [pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst, Category.comp_id])
  have i₁ := isIso_unit_app_comp_map_of_etale A W.hom ((p)^*[A].obj G) W IW δW
    (by
      change IsIso (pullback.lift (𝟙 W.left) (𝟙 W.left) rfl ≫ pullback.fst W.hom W.hom)
      rw [pullback.lift_fst]
      infer_instance)
  have i₂ := isIso_unit_app_comp_map_of_etale A V.hom G V IV δV
    (by
      change IsIso (pullback.lift (𝟙 V.left) (𝟙 V.left) rfl ≫ pullback.fst V.hom V.hom)
      rw [pullback.lift_fst]
      infer_instance)
  have i₃ : IsIso (((upperStarLowerStarAdjunction A q).unit.app ((V.hom)^*[A].obj G)).hom.app
      (op IV) ≫ ((q)^*[A].obj ((V.hom)^*[A].obj G)).obj.map γ.op) := by
    have h₁ : IsIso (((upperStarLowerStarAdjunction A q).unit.app
        ((V.hom)^*[A].obj G)).hom.app (op IV)) :=
      isIso_unit_app_mkId_of_geometricallyConnected R q ((V.hom)^*[A].obj G)
    have : IsIso γ := isIso_of_isIso_left' γ
      ⟨pullback.snd (𝟙 V.left) q, pullback.lift_snd _ _ _, by
        change pullback.snd (𝟙 V.left) q ≫ pullback.lift (f := 𝟙 V.left) q (𝟙 W.left) _ = 𝟙 _
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, ← pullback.condition, Category.comp_id,
            Category.id_comp]
        · rw [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]⟩
    infer_instance
  have key : (((upperStarLowerStarAdjunction A p).unit.app G).hom.app (op V) ≫
      ((p)^*[A].obj G).obj.map φ.op) ≫
      ((((upperStarLowerStarAdjunction A W.hom).unit.app ((p)^*[A].obj G)).hom.app (op W) ≫
        ((W.hom)^*[A].obj ((p)^*[A].obj G)).obj.map δW.op) ≫
        ((upperStarComp A W.hom p (W.hom ≫ p) rfl).inv.app G).hom.app (op IW)) =
      (((upperStarLowerStarAdjunction A V.hom).unit.app G).hom.app (op V) ≫
        ((V.hom)^*[A].obj G).obj.map δV.op) ≫
      ((((upperStarLowerStarAdjunction A q).unit.app ((V.hom)^*[A].obj G)).hom.app
        (op IV) ≫ ((q)^*[A].obj ((V.hom)^*[A].obj G)).obj.map γ.op) ≫
        ((upperStarComp A q V.hom (W.hom ≫ p) hq.symm).inv.app G).hom.app (op IW)) := by
    simp only [Category.assoc]
    rw [e₁, e₂]
  have : IsIso ((((upperStarLowerStarAdjunction A p).unit.app G).hom.app (op V) ≫
      ((p)^*[A].obj G).obj.map φ.op) ≫
      ((((upperStarLowerStarAdjunction A W.hom).unit.app ((p)^*[A].obj G)).hom.app (op W) ≫
        ((W.hom)^*[A].obj ((p)^*[A].obj G)).obj.map δW.op) ≫
        ((upperStarComp A W.hom p (W.hom ≫ p) rfl).inv.app G).hom.app (op IW))) := by
    rw [key]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((((upperStarLowerStarAdjunction A W.hom).unit.app
    ((p)^*[A].obj G)).hom.app (op W) ≫ ((W.hom)^*[A].obj ((p)^*[A].obj G)).obj.map δW.op) ≫
      ((upperStarComp A W.hom p (W.hom ≫ p) rfl).inv.app G).hom.app (op IW))

end GeometricallyConnected

end AlgebraicGeometry.Etale
