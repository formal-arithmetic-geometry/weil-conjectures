/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Forget
import WeilConjectures.AlgebraicGeometry.Sites.UpperStarSections
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageRestriction
import WeilConjectures.AlgebraicGeometry.EtaleSetSectionsFlatConnectedFibres

/-!
# Sections of an inverse image along a flat morphism with connected fibres

Let `p : X ⟶ S` be a morphism of schemes, `V` an étale `S`-scheme, `W` an étale `X`-scheme and
`φ : W ⟶ V ×_S X` a morphism of étale `X`-schemes such that the induced morphism `q : W ⟶ V`
is flat, quasi-compact and has geometrically connected fibres. Then for every étale sheaf `G`
on `S` the map `G(V) ⟶ (p^* G)(W)`, the unit of `p^* ⊣ p_*` at `V` followed by the restriction
along `φ`, is bijective.

For sheaves of sets this is reduced to the case `V = S`, `W = X` of
`AlgebraicGeometry.etaleSet_sections_bijective_of_flat_qc_connected_geometricFibres`
[Stacks 0A3H], applied to `q` and the restriction of `G` to `V`: inverse images along étale
morphisms are restrictions, and inverse images are compatible with composition. The cases of
abelian sheaves and of sheaves of modules follow, since inverse images commute with the
forgetful functors.

## Main statements

- `AlgebraicGeometry.Etale.bijective_etaleSet_unit_map_of_flat`: sheaves of sets.
- `AlgebraicGeometry.Etale.bijective_addCommGrp_unit_map_of_flat`: abelian sheaves.
- `AlgebraicGeometry.Etale.bijective_moduleCat_unit_map_of_flat`: sheaves of modules.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace Etale

local notation "L" => Scheme.etaleSetPullback
local notation "b" => MorphismProperty.Over.pullback @Etale ⊤
local notation "η[" S ", " T "] " e =>
  Adjunction.unit
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (b e) _
      (Scheme.smallGrothendieckTopology @Etale S)
      (Scheme.smallGrothendieckTopology @Etale T))

/-- The components of an isomorphism of sheaves with values in a concrete category are
bijective. -/
lemma bijective_hom_app_of_isIso {C : Type*} [Category C] {J : GrothendieckTopology C}
    {A : Type*} [Category A] {FA : A → A → Type*} {CA : A → Type*}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
    {F G : Sheaf J A} (f : F ⟶ G) [IsIso f] (T : Cᵒᵖ) :
    Function.Bijective (f.hom.app T) := by
  have : IsIso f.hom := inferInstanceAs (IsIso ((sheafToPresheaf J _).map f))
  exact ConcreteCategory.bijective_of_isIso (f.hom.app T)

/-- For an étale `R`-scheme `U` and a sheaf of sets `H` on `R`, the sections of `H` over `U`
are the global sections of the inverse image of `H` along the structure morphism `j` of `U`:
the unit at `U` followed by the restriction along a section `U ⟶ U ×_R U` of the first
projection is bijective. -/
lemma bijective_map_unit_app_of_etale {R : Scheme.{u}}
    (H : Sheaf R.smallEtaleTopology (Type (u + 1))) (U : R.Etale) (j : U.left ⟶ R)
    (hj : U.hom = j) [Etale j]
    (m : Scheme.Etale.mk (𝟙 U.left) ⟶ (b j).obj U)
    (hm : m.left ≫ pullback.fst U.hom j = 𝟙 U.left) :
    Function.Bijective fun s : H.obj.obj (op U) ↦
      ((L j).obj H).obj.map m.op (((η[R, U.left] j).app H).hom.app (op U) s) := by
  obtain ⟨ρ, hρ⟩ := etaleSetInverseImageRestriction j
  let M := MorphismProperty.Over.map ⊤ (inferInstance : Etale j)
  let ε := (MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j inferInstance trivial).counit.app U
  let e : M.obj (Scheme.Etale.mk (𝟙 U.left)) ≅ U :=
    MorphismProperty.Over.isoMk (Iso.refl U.left) (by simp [M, hj])
  have he : M.map m ≫ ε = e.hom := by
    apply MorphismProperty.Over.Hom.ext
    simp only [Functor.id_obj, MorphismProperty.Comma.comp_hom, Comma.comp_left]
    exact hm
  have key (s : H.obj.obj (op U)) :
      (ρ.hom.app H).hom.app (op (Scheme.Etale.mk (𝟙 U.left)))
        (((L j).obj H).obj.map m.op (((η[R, U.left] j).app H).hom.app (op U) s)) =
      H.obj.map e.hom.op s := by
    rw [NatTrans.naturality_apply, hρ, ← he, op_comp, Functor.map_comp,
      ConcreteCategory.comp_apply]
    rfl
  refine (Function.Bijective.of_comp_iff'
    (bijective_hom_app_of_isIso (ρ.hom.app H) (op (Scheme.Etale.mk (𝟙 U.left)))) _).1 ?_
  have hk : ((ρ.hom.app H).hom.app (op (Scheme.Etale.mk (𝟙 U.left))) ∘ fun s ↦
      ((L j).obj H).obj.map m.op (((η[R, U.left] j).app H).hom.app (op U) s)) =
      H.obj.map e.hom.op := funext key
  exact (congrArg Function.Bijective hk).mpr (ConcreteCategory.bijective_of_isIso _)

/-- A section `x = m₁^* η(s)` is sent by the transport `e` along an equality `k₁ = k₂` of
structure morphisms to `m₂^* η(s)`, as soon as the first projections of the morphisms
`m₁, m₂ : Y ⟶ V ×_S Y` agree. -/
lemma hom_app_eq_map_unit_app {S Y : Scheme.{u}} (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
    (V : S.Etale) {k₁ k₂ : Y ⟶ S} (h : k₁ = k₂) (e : (L k₁).obj F ⟶ (L k₂).obj F)
    (he : e = eqToHom (congrArg (fun k ↦ (L k).obj F) h))
    (m₁ : Scheme.Etale.mk (𝟙 Y) ⟶ (b k₁).obj V) (m₂ : Scheme.Etale.mk (𝟙 Y) ⟶ (b k₂).obj V)
    (hm : m₁.left ≫ pullback.fst V.hom k₁ = m₂.left ≫ pullback.fst V.hom k₂)
    (s : F.obj.obj (op V)) (x : ((L k₁).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 Y))))
    (hx : x = ((L k₁).obj F).obj.map m₁.op (((η[S, Y] k₁).app F).hom.app (op V) s)) :
    e.hom.app (op (Scheme.Etale.mk (𝟙 Y))) x =
      ((L k₂).obj F).obj.map m₂.op (((η[S, Y] k₂).app F).hom.app (op V) s) := by
  subst h he hx
  obtain rfl : m₁ = m₂ := by
    apply MorphismProperty.Over.Hom.ext
    refine pullback.hom_ext hm ?_
    exact (MorphismProperty.Over.w m₁).trans (MorphismProperty.Over.w m₂).symm
  simp

/-- The first projection of the pasting isomorphism `(U ×_Z Y) ×_Y X ≅ U ×_Z X` of iterated
base change. -/
lemma pullbackComp_inv_app_left_fst {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (A : Z.Etale) :
    ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f g).inv.app A).left ≫
        pullback.fst A.hom (f ≫ g) =
      pullback.fst ((b g).obj A).hom f ≫ pullback.fst A.hom g := by
  simp [MorphismProperty.Over.pullbackComp_inv_app_left]

/-- The first projection of the base change of a morphism of étale schemes. -/
@[reassoc]
lemma overPullback_map_left_fst {X Y : Scheme.{u}} (g : Y ⟶ X) {U U' : X.Etale} (a : U' ⟶ U) :
    ((b g).map a).left ≫ pullback.fst U.hom g = pullback.fst U'.hom g ≫ a.left := by
  simp

/-- The components of an isomorphism of sheaves of sets are bijective. -/
lemma bijective_hom_hom_app_of_iso {C : Type*} [Category C] {J : GrothendieckTopology C}
    {F G : Sheaf J (Type (u + 1))} (e : F ≅ G) (T : Cᵒᵖ) :
    Function.Bijective (e.hom.hom.app T) :=
  bijective_hom_app_of_isIso e.hom T

/-- Pulling back a section twice, along `f` and then along `g`, and restricting along the way,
is pulling it back once along `g ≫ f`, under a composition map `γ` compatible with the units. -/
lemma hom_app_map_unit_app_map_unit_app {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (γ : (L g).obj ((L f).obj F) ⟶ (L (g ≫ f)).obj F)
    (hγ : ∀ (U : X.Etale) (s : F.obj.obj (op U)),
      γ.hom.app (op ((b g).obj ((b f).obj U)))
          (((η[Y, Z] g).app ((L f).obj F)).hom.app (op ((b f).obj U))
            (((η[X, Y] f).app F).hom.app (op U) s)) =
        ((L (g ≫ f)).obj F).obj.map
          ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g f).inv.app U).op
          (((η[X, Z] (g ≫ f)).app F).hom.app (op U) s))
    {U : X.Etale} {U' : Y.Etale} {T' : Z.Etale} (a : U' ⟶ (b f).obj U)
    (m : T' ⟶ (b g).obj U') (s : F.obj.obj (op U)) :
    γ.hom.app (op T')
        (((L g).obj ((L f).obj F)).obj.map m.op
          (((η[Y, Z] g).app ((L f).obj F)).hom.app (op U')
            (((L f).obj F).obj.map a.op (((η[X, Y] f).app F).hom.app (op U) s)))) =
      ((L (g ≫ f)).obj F).obj.map
        (m ≫ (b g).map a ≫
          (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g f).inv.app U).op
        (((η[X, Z] (g ≫ f)).app F).hom.app (op U) s) := by
  obtain ⟨hη, -⟩ := etaleSetInverseImageCompositionUnits.{u}
  rw [hη Y Z g ((L f).obj F) _ _ a, ← Functor.map_comp_apply, ← op_comp, NatTrans.naturality_apply,
    hγ]
  erw [← Functor.map_comp_apply]
  rw [← op_comp, Category.assoc]

/-- The unit compatibility of a composition isomorphism `c`, phrased for `(c.app F).hom`. -/
lemma app_hom_hom_app_unit_app_unit_app {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (c : L f ⋙ L g ≅ L (g ≫ f))
    (hc : ∀ (U : X.Etale) (s : F.obj.obj (op U)),
      (c.hom.app F).hom.app (op ((b g).obj ((b f).obj U)))
          (((η[Y, Z] g).app ((L f).obj F)).hom.app (op ((b f).obj U))
            (((η[X, Y] f).app F).hom.app (op U) s)) =
        ((L (g ≫ f)).obj F).obj.map
          ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g f).inv.app U).op
          (((η[X, Z] (g ≫ f)).app F).hom.app (op U) s))
    (U : X.Etale) (s : F.obj.obj (op U)) :
    ((c.app F).hom : (L g).obj ((L f).obj F) ⟶ (L (g ≫ f)).obj F).hom.app
        (op ((b g).obj ((b f).obj U)))
          (((η[Y, Z] g).app ((L f).obj F)).hom.app (op ((b f).obj U))
            (((η[X, Y] f).app F).hom.app (op U) s)) =
        ((L (g ≫ f)).obj F).obj.map
          ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g f).inv.app U).op
          (((η[X, Z] (g ≫ f)).app F).hom.app (op U) s) :=
  hc U s

/-- **Sections of an inverse image along a flat morphism with connected fibres**, for sheaves
of sets [Stacks 0A3H]. Let `φ : W ⟶ V ×_S X` be a morphism of étale `X`-schemes such that the
induced morphism `q : W ⟶ V` is flat, quasi-compact and has geometrically connected fibres.
Then the unit of `p^* ⊣ p_*` at `V` followed by the restriction along `φ` is a bijection
`F(V) ≃ (p^* F)(W)`.

Writing `r : V ⟶ S` and `j : W ⟶ X` for the structure morphisms, `(p^* F)(W)` is the set of
global sections of `j^* p^* F = (j ≫ p)^* F = (q ≫ r)^* F = q^* r^* F`, and `F(V)` is the set
of global sections of `r^* F`, by `bijective_map_unit_app_of_etale`. Under these
identifications the map becomes the pullback of global sections along `q`, which is bijective
by `AlgebraicGeometry.etaleSet_sections_bijective_of_flat_qc_connected_geometricFibres`. -/
theorem bijective_etaleSet_unit_map_of_flat {S X : Scheme.{u}} (p : X ⟶ S)
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) {V : S.Etale} {W : X.Etale}
    (φ : W ⟶ (b p).obj V) [Flat (φ.left ≫ pullback.fst V.hom p)]
    [QuasiCompact (φ.left ≫ pullback.fst V.hom p)]
    [GeometricallyConnected (φ.left ≫ pullback.fst V.hom p)] :
    Function.Bijective fun s : F.obj.obj (op V) ↦
      ((L p).obj F).obj.map φ.op (((η[S, X] p).app F).hom.app (op V) s) := by
  obtain ⟨-, -, c, hc, -, -⟩ := etaleSetInverseImageCompositionUnits.{u}
  obtain ⟨q, hq⟩ : ∃ q : W.left ⟶ V.left, φ.left ≫ pullback.fst V.hom p = q := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : V.left ⟶ S, V.hom = r := ⟨_, rfl⟩
  obtain ⟨j, hj⟩ : ∃ j : W.left ⟶ X, W.hom = j := ⟨_, rfl⟩
  have : Flat q := hq ▸ inferInstance
  have : QuasiCompact q := hq ▸ inferInstance
  have : GeometricallyConnected q := hq ▸ inferInstance
  have : Etale r := hr ▸ V.prop
  have : Etale j := hj ▸ W.prop
  have hφ : φ.left ≫ pullback.snd V.hom p = j := hj ▸ MorphismProperty.Over.w φ
  have hqr : j ≫ p = q ≫ r := by
    rw [← hq, ← hφ, ← hr, Category.assoc, Category.assoc, pullback.condition]
  -- the diagonals of `V` and `W`
  let δV : Scheme.Etale.mk (𝟙 V.left) ⟶ (b r).obj V :=
    MorphismProperty.Over.homMk (pullback.lift (𝟙 V.left) (𝟙 V.left) (by rw [hr])) (by simp)
  let δW : Scheme.Etale.mk (𝟙 W.left) ⟶ (b j).obj W :=
    MorphismProperty.Over.homMk (pullback.lift (𝟙 W.left) (𝟙 W.left) (by rw [hj])) (by simp)
  -- the identification of `W` with `V ×_V W`
  let κ : Scheme.Etale.mk (𝟙 W.left) ⟶ (b q).obj (Scheme.Etale.mk (𝟙 V.left)) :=
    MorphismProperty.Over.homMk
      (pullback.lift q (𝟙 W.left) ((Category.comp_id _).trans (Category.id_comp _).symm))
      (by simp)
  let κ' : (b q).obj (Scheme.Etale.mk (𝟙 V.left)) ⟶ Scheme.Etale.mk (𝟙 W.left) :=
    MorphismProperty.Over.homMk (pullback.snd (𝟙 V.left) q) (by exact Category.comp_id _)
  have : IsIso κ := ⟨κ', by
    apply MorphismProperty.Over.Hom.ext
    exact pullback.lift_snd _ _ _, by
    apply MorphismProperty.Over.Hom.ext
    change pullback.snd (𝟙 V.left) q ≫ pullback.lift q (𝟙 W.left) _ = 𝟙 _
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, Category.id_comp]
      simpa only [Category.comp_id] using (pullback.condition (f := 𝟙 V.left) (g := q)).symm
    · simp⟩
  -- the bijections
  have h₁ := bijective_map_unit_app_of_etale F V r hr δV (by simp [δV])
  have h₂ := etaleSet_sections_bijective_of_flat_qc_connected_geometricFibres q
    (fun _ ↦ GeometricallyConnected.geometrically_connectedSpace (f := q) _ _ _
      (IsPullback.of_hasPullback _ _)) ((L r).obj F)
  have h₃ : Function.Bijective (((L q).obj ((L r).obj F)).obj.map κ.op) :=
    ConcreteCategory.bijective_of_isIso _
  obtain ⟨γ₂, hγ₂⟩ : ∃ γ₂ : (L q).obj ((L r).obj F) ⟶ (L (q ≫ r)).obj F,
      γ₂ = ((c S V.left W.left r q).app F).hom := ⟨_, rfl⟩
  have h₄ : Function.Bijective (γ₂.hom.app (op (Scheme.Etale.mk (𝟙 W.left)))) := by
    subst hγ₂; exact bijective_hom_hom_app_of_iso ((c S V.left W.left r q).app F) _
  have h₅ := bijective_map_unit_app_of_etale ((L p).obj F) W j hj δW (by simp [δW])
  obtain ⟨γ₁, hγ₁⟩ : ∃ γ₁ : (L j).obj ((L p).obj F) ⟶ (L (j ≫ p)).obj F,
      γ₁ = ((c S X W.left p j).app F).hom := ⟨_, rfl⟩
  have h₆ : Function.Bijective (γ₁.hom.app (op (Scheme.Etale.mk (𝟙 W.left)))) := by
    subst hγ₁; exact bijective_hom_hom_app_of_iso ((c S X W.left p j).app F) _
  obtain ⟨e, he⟩ : ∃ e : (L (j ≫ p)).obj F ⟶ (L (q ≫ r)).obj F,
      e = eqToHom (congrArg (fun k ↦ (L k).obj F) hqr) := ⟨_, rfl⟩
  have h₇ : Function.Bijective (e.hom.app (op (Scheme.Etale.mk (𝟙 W.left)))) := by
    subst he; exact bijective_hom_app_of_isIso _ _
  rw [← Function.comp_def] at h₁ h₅ ⊢
  refine (Function.Bijective.of_comp_iff' (h₇.comp (h₆.comp h₅)) _).1 ?_
  refine (congrArg Function.Bijective (funext fun s ↦ ?_)).mpr (h₄.comp (h₃.comp (h₂.comp h₁)))
  repeat rw [Function.comp_apply]
  have hh₁ := hom_app_map_unit_app_map_unit_app p j F γ₁
    (hγ₁ ▸ app_hom_hom_app_unit_app_unit_app p j F _ (hc S X W.left p j F)) φ δW s
  have hh₂ := hom_app_map_unit_app_map_unit_app r q F γ₂
    (hγ₂ ▸ app_hom_hom_app_unit_app_unit_app r q F _ (hc S V.left W.left r q F)) δV κ s
  have hm : (δW ≫ (b j).map φ ≫
      (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) j p).inv.app V).left ≫
        pullback.fst V.hom (j ≫ p) =
      (κ ≫ (b q).map δV ≫
        (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) q r).inv.app V).left ≫
        pullback.fst V.hom (q ≫ r) := by
    have e₁ : δW.left ≫ pullback.fst W.hom j = 𝟙 W.left := by simp [δW]
    have e₂ : δV.left ≫ pullback.fst V.hom r = 𝟙 V.left := by simp [δV]
    have e₃ : κ.left ≫ pullback.fst (Scheme.Etale.mk (𝟙 V.left)).hom q = q := by simp [κ]
    simp only [etale_comp_left, Category.assoc, pullbackComp_inv_app_left_fst,
      overPullback_map_left_fst_assoc, reassoc_of% e₁, e₂, reassoc_of% e₃, hq]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  exact (hom_app_eq_map_unit_app F V hqr e he _ _ hm s _ hh₁).trans hh₂.symm

/-- `bijective_etaleSet_unit_map_of_flat` for abelian sheaves: inverse images commute with the
forgetful functor to sheaves of sets, compatibly with the units. -/
theorem bijective_addCommGrp_unit_map_of_flat {S X : Scheme.{u}} (p : X ⟶ S)
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) {V : S.Etale} {W : X.Etale}
    (φ : W ⟶ (b p).obj V) [Flat (φ.left ≫ pullback.fst V.hom p)]
    [QuasiCompact (φ.left ≫ pullback.fst V.hom p)]
    [GeometricallyConnected (φ.left ≫ pullback.fst V.hom p)] :
    Function.Bijective fun s : G.obj.obj (op V) ↦
      ((upperStar AddCommGrpCat.{u + 1} p).obj G).obj.map φ.op
        (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} p).unit.app G).hom.app (op V) s) := by
  obtain ⟨-, ea, da, -, -, -, -, hda, -, -, hunit, -⟩ := etaleInverseImageAlgebraicStructures X S p
  have h := bijective_etaleSet_unit_map_of_flat p ((sheafForget S.smallEtaleTopology).obj G) φ
  have e₁ := ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun k ↦ k.hom) (hunit G))
    (op V))
  have e : ∀ x : G.obj.obj (op V),
      (ea.hom.app G).hom.app (op ((b p).obj V))
        (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} p).unit.app G).hom.app (op V) x) =
      ((η[S, X] p).app ((sheafForget S.smallEtaleTopology).obj G)).hom.app (op V) x := by
    intro x
    refine Eq.trans ?_ (e₁ x)
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      ConcreteCategory.comp_apply]
    erw [hda]
    rfl
  refine (Function.Bijective.of_comp_iff' (bijective_hom_app_of_isIso (ea.hom.app G) (op W)) _).1
    ?_
  refine (congrArg Function.Bijective (funext fun s ↦ ?_)).mpr h
  refine Eq.trans ?_ (congrArg (((L p).obj ((sheafForget S.smallEtaleTopology).obj G)).obj.map
    φ.op) (e s))
  exact NatTrans.naturality_apply (ea.hom.app G).hom φ.op _

/-- `bijective_etaleSet_unit_map_of_flat` for sheaves of `Λ`-modules: inverse images commute
with the forgetful functor to abelian sheaves, compatibly with the units. -/
theorem bijective_moduleCat_unit_map_of_flat (Λ : Type (u + 1)) [CommRing Λ] {S X : Scheme.{u}}
    (p : X ⟶ S) (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {V : S.Etale}
    {W : X.Etale} (φ : W ⟶ (b p).obj V) [Flat (φ.left ≫ pullback.fst V.hom p)]
    [QuasiCompact (φ.left ≫ pullback.fst V.hom p)]
    [GeometricallyConnected (φ.left ≫ pullback.fst V.hom p)] :
    Function.Bijective fun s : G.obj.obj (op V) ↦
      ((upperStar (ModuleCat.{u + 1} Λ) p).obj G).obj.map φ.op
        (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app G).hom.app (op V) s) := by
  have h := bijective_addCommGrp_unit_map_of_flat p
    ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G) φ
  have e₁ := ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun k ↦ k.hom)
    (unit_comp_lowerStar_map_upperStarForget₂Comparison Λ p G)) (op V))
  have e : ∀ x : G.obj.obj (op V),
      (upperStarForget₂Comparison Λ p G).hom.app (op ((b p).obj V))
        (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} p).unit.app
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G)).hom.app
            (op V) x) =
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app G).hom.app (op V) x := by
    intro x
    have := e₁ x
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      ConcreteCategory.comp_apply] at this
    exact this
  refine (congrArg Function.Bijective (funext fun s ↦ ?_)).mpr
    ((bijective_hom_app_of_isIso (upperStarForget₂Comparison Λ p G) (op W)).comp h)
  refine Eq.trans ?_ (NatTrans.naturality_apply (upperStarForget₂Comparison Λ p G).hom φ.op _).symm
  exact congrArg (((upperStar (ModuleCat.{u + 1} Λ) p).obj G).obj.map φ.op) (e s).symm

end Etale

end AlgebraicGeometry
