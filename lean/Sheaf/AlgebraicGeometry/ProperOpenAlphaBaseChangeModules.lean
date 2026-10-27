/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.StrictTowerOrdinaryProperOpenArrows
import all Sheaf.AlgebraicGeometry.StrictTowerOrdinaryProperOpenArrows
import all Sheaf.CategoryTheory.ExactDerivedPastingComponents

/-! # Intrinsic alpha baseChange identity on module sheaves

Source: Stacks Project, Tag 0F7F, with the arbitrary-ring underived refinement.
(blueprint: lem-cbc-proper-open-alpha-base-change-modules)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.StrictTower
variable (B : Type (u + 1)) [CommRing B]

/-- Intrinsic alpha obeys cube pasting on module sheaves.
Source: Stacks, Tag 0F7F, and the parent restriction argument, steps 1--3 and 6
(blueprint: lem-cbc-proper-open-alpha-base-change-modules).
Proof: First detect equality of maps to open extension on module sheaves: the image of
their difference restricts to zero both on the open and its closed complement.
Exact inverse image and the open/closed short exact sequence force that image to vanish.
The inverse-transpose definition of beta gives its restriction normalization through
the specified open units. The clopen projector restricts to the identity, so intrinsic
alpha restricts to the canonical inverse-image square identification followed by
inverse image of the inverse open unit. All detection opens are quasi-compact.
For base change, restrict along k₁. The original-alpha route reduces through
ak₁ = kd to d* r*, then through rd = cr₁ to r₁* c*. The beta for k is exactly
the open-unit identification. On the changed-alpha route the beta for i first gives
that same open-unit identification, and intrinsic alpha for Q₁ reduces to r₁* c*.
The square identification for p₁ followed by b equal to a followed by p makes the
starting comparisons equal.
Detection gives the cube equation without proper direct-image base change.
Apply this calculation to every module sheaf M to obtain the displayed component
identity. Empty schemes and the zero coefficient ring give the unique zero maps;
identity opens give the unit-normalized inverse-image compositor identity. -/
theorem singleAlpha_baseChange {V W S T V₁ W₁ S₁ T₁ : Scheme.{u}}
    (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
    (k₁ : V₁ ⟶ W₁) (i₁ : S₁ ⟶ T₁) (r₁ : V₁ ⟶ S₁) (p₁ : W₁ ⟶ T₁)
    (a : W₁ ⟶ W) (b : T₁ ⟶ T) (c : S₁ ⟶ S) (d : V₁ ⟶ V)
    [IsOpenImmersion k] [IsOpenImmersion i]
    [IsOpenImmersion k₁] [IsOpenImmersion i₁]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact k₁] [QuasiCompact i₁]
    [IsProper r] [IsProper p] [IsProper r₁] [IsProper p₁]
    (h : k ≫ p = r ≫ i) (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
    (wk : d ≫ k = k₁ ≫ a) (wi : c ≫ i = i₁ ≫ b)
    (wp : a ≫ p = p₁ ≫ b) (wr : d ≫ r = r₁ ≫ c)
    (sk : IsPullback d k₁ k a) (si : IsPullback c i₁ i b)
    (sp : IsPullback a p₁ p b) (sr : IsPullback d r₁ r c) :
    ∀ M : Modules B S,
      (moduleSquareG B a p₁ p b wp).hom.app ((moduleJ B i).obj M) ≫
          (modulePullback B a).map ((singleAlpha B k r p i h).app M) ≫
          (openBetaModule B d k₁ k a wk sk).hom.app ((modulePullback B r).obj M) ≫
          (moduleJ B k₁).map ((moduleSquareG B d r₁ r c wr).inv.app M) =
        (modulePullback B p₁).map ((openBetaModule B c i₁ i b wi si).hom.app M) ≫
          (singleAlpha B k₁ r₁ p₁ i₁ h₁).app ((modulePullback B c).obj M) := by sorry


open CategoryTheory.ExactDerivedPasting
attribute [local irreducible] Functor.leftAdjoint modulePullback singleAlpha moduleGComp
attribute [local irreducible] moduleSquareG openBetaModule openBetaModuleJComp
set_option linter.unusedSimpArgs false

private structure NativeCubeData (Xv Xs Xw Xt Xv₁ Xs₁ Xw₁ Xt₁ : Scheme.{u}) where
  K : Modules B Xv ⥤ Modules B Xw
  V : Modules B Xs ⥤ Modules B Xt
  R : Modules B Xs ⥤ Modules B Xv
  P : Modules B Xt ⥤ Modules B Xw
  K₁ : Modules B Xv₁ ⥤ Modules B Xw₁
  V₁ : Modules B Xs₁ ⥤ Modules B Xt₁
  R₁ : Modules B Xs₁ ⥤ Modules B Xv₁
  P₁ : Modules B Xt₁ ⥤ Modules B Xw₁
  A : Modules B Xw ⥤ Modules B Xw₁
  B' : Modules B Xt ⥤ Modules B Xt₁
  C' : Modules B Xs ⥤ Modules B Xs₁
  D : Modules B Xv ⥤ Modules B Xv₁
  ao : V ⋙ P ⟶ R ⋙ K
  a₁ : V₁ ⋙ P₁ ⟶ R₁ ⋙ K₁
  bk : K ⋙ A ≅ D ⋙ K₁
  bi : V ⋙ B' ≅ C' ⋙ V₁
  sp : B' ⋙ P₁ ≅ P ⋙ A
  sr : C' ⋙ R₁ ≅ R ⋙ D
  h : ∀ M : Modules B Xs,
      sp.hom.app (V.obj M) ≫ A.map (ao.app M) ≫ bk.hom.app (R.obj M) ≫
          K₁.map (sr.inv.app M) =
        P₁.map (bi.hom.app M) ≫ a₁.app (C'.obj M)

@[irreducible] private def nativeCubeData {V W S T V₁ W₁ S₁ T₁ : Scheme.{u}}
    (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
    (k₁ : V₁ ⟶ W₁) (i₁ : S₁ ⟶ T₁) (r₁ : V₁ ⟶ S₁) (p₁ : W₁ ⟶ T₁)
    (a : W₁ ⟶ W) (b : T₁ ⟶ T) (c : S₁ ⟶ S) (d : V₁ ⟶ V)
    [IsOpenImmersion k] [IsOpenImmersion i]
    [IsOpenImmersion k₁] [IsOpenImmersion i₁]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact k₁] [QuasiCompact i₁]
    [IsProper r] [IsProper p] [IsProper r₁] [IsProper p₁]
    (h : k ≫ p = r ≫ i) (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
    (wk : d ≫ k = k₁ ≫ a) (wi : c ≫ i = i₁ ≫ b)
    (wp : a ≫ p = p₁ ≫ b) (wr : d ≫ r = r₁ ≫ c)
    (sk : IsPullback d k₁ k a) (si : IsPullback c i₁ i b)
    (hp : IsPullback a p₁ p b) (hr : IsPullback d r₁ r c) :
    NativeCubeData B V S W T V₁ S₁ W₁ T₁ where
  K := moduleJ B k
  V := moduleJ B i
  R := modulePullback B r
  P := modulePullback B p
  K₁ := moduleJ B k₁
  V₁ := moduleJ B i₁
  R₁ := modulePullback B r₁
  P₁ := modulePullback B p₁
  A := modulePullback B a
  B' := modulePullback B b
  C' := modulePullback B c
  D := modulePullback B d
  ao := singleAlpha B k r p i h
  a₁ := singleAlpha B k₁ r₁ p₁ i₁ h₁
  bk := openBetaModule B d k₁ k a wk sk
  bi := openBetaModule B c i₁ i b wi si
  sp := moduleSquareG B a p₁ p b wp
  sr := moduleSquareG B d r₁ r c wr
  h := singleAlpha_baseChange B k i r p k₁ i₁ r₁ p₁ a b c d h h₁ wk wi wp wr sk si hp hr

private theorem nativeCubeLaw {V S W T V₁ S₁ W₁ T₁ : Scheme.{u}}
    (T₀ : NativeCubeData B V S W T V₁ S₁ W₁ T₁) :
    Functor.whiskerLeft (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.V) (twIso (fun X :
      Scheme.{u} ↦ Modules B X) T₀.B' T₀.P₁ T₀.P T₀.A T₀.sp).hom ≫
        (Functor.associator (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.V) (twFunctor (fun X
      : Scheme.{u} ↦ Modules B X) T₀.P) (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.A)).inv ≫
        Functor.whiskerRight
          (Functor.termwiseCompositeTransformation ℕᵒᵖ _ _ _ _ T₀.V T₀.P T₀.R T₀.K T₀.ao)
          (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.A) ≫
        (Functor.associator (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.R) (twFunctor (fun X
      : Scheme.{u} ↦ Modules B X) T₀.K) (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.A)).hom ≫
        Functor.whiskerLeft (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.R) (twIso (fun X :
      Scheme.{u} ↦ Modules B X) T₀.K T₀.A T₀.D T₀.K₁ T₀.bk).hom ≫
        (Functor.associator (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.R) (twFunctor (fun X
      : Scheme.{u} ↦ Modules B X) T₀.D) (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.K₁)).inv ≫
        Functor.whiskerRight (twIso (fun X : Scheme.{u} ↦ Modules B X) T₀.C' T₀.R₁ T₀.R T₀.D
      T₀.sr).inv (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.K₁) =
      (Functor.associator (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.V) (twFunctor (fun X :
      Scheme.{u} ↦ Modules B X) T₀.B') (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.P₁)).inv ≫
        Functor.whiskerRight (twIso (fun X : Scheme.{u} ↦ Modules B X) T₀.V T₀.B' T₀.C' T₀.V₁
      T₀.bi).hom (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.P₁) ≫
        (Functor.associator (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.C') (twFunctor (fun
      X : Scheme.{u} ↦ Modules B X) T₀.V₁) (twFunctor (fun X : Scheme.{u} ↦ Modules B X)
      T₀.P₁)).hom ≫
        Functor.whiskerLeft (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.C')
          (Functor.termwiseCompositeTransformation ℕᵒᵖ _ _ _ _ T₀.V₁ T₀.P₁ T₀.R₁ T₀.K₁ T₀.a₁) ≫
        (Functor.associator (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.C') (twFunctor (fun
      X : Scheme.{u} ↦ Modules B X) T₀.R₁) (twFunctor (fun X : Scheme.{u} ↦ Modules B X)
      T₀.K₁)).inv :=
  @cubeTowerLaw Scheme.{u} (fun X : Scheme.{u} ↦ Modules B X)
    (fun X ↦ inferInstanceAs (Category.{u + 1} (Modules B X))) V S W T V₁ S₁ W₁ T₁
    T₀.K T₀.V T₀.R T₀.P T₀.K₁ T₀.V₁ T₀.R₁ T₀.P₁ T₀.A T₀.B' T₀.C' T₀.D T₀.ao T₀.a₁ T₀.bk T₀.bi
      T₀.sp T₀.sr T₀.h

private theorem towerAlpha_baseChange {V W S T V₁ W₁ S₁ T₁ : Scheme.{u}}
    (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
    (k₁ : V₁ ⟶ W₁) (i₁ : S₁ ⟶ T₁) (r₁ : V₁ ⟶ S₁) (p₁ : W₁ ⟶ T₁)
    (a : W₁ ⟶ W) (b : T₁ ⟶ T) (c : S₁ ⟶ S) (d : V₁ ⟶ V)
    [IsOpenImmersion k] [IsOpenImmersion i]
    [IsOpenImmersion k₁] [IsOpenImmersion i₁]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact k₁] [QuasiCompact i₁]
    [IsProper r] [IsProper p] [IsProper r₁] [IsProper p₁]
    (h : k ≫ p = r ≫ i) (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
    (wk : d ≫ k = k₁ ≫ a) (wi : c ≫ i = i₁ ≫ b)
    (wp : a ≫ p = p₁ ≫ b) (wr : d ≫ r = r₁ ≫ c)
    (sk : IsPullback d k₁ k a) (si : IsPullback c i₁ i b)
    (hp : IsPullback a p₁ p b) (hr : IsPullback d r₁ r c) :
    Functor.whiskerLeft (towerJ B i) ((towerSquare (modulePullback B b) (modulePullback B p₁)
      (modulePullback B p) (modulePullback B a) (moduleSquareG B a p₁ p b wp)).hom) ≫
      (Functor.associator (towerJ B i) (towerPullback B p) (towerPullback B a)).inv ≫
        Functor.whiskerRight (towerAlpha B k r p i h) (towerPullback B a) ≫ (Functor.associator
      (towerPullback B r) (towerJ B k) (towerPullback B a)).hom ≫
        Functor.whiskerLeft (towerPullback B r) ((openBetaTower B d k₁ k a wk sk).hom) ≫
      (Functor.associator (towerPullback B r) (towerPullback B d) (towerJ B k₁)).inv ≫
        Functor.whiskerRight ((towerSquare (modulePullback B c) (modulePullback B r₁)
      (modulePullback B r) (modulePullback B d) (moduleSquareG B d r₁ r c wr)).inv) (towerJ B k₁) =
      (Functor.associator (towerJ B i) (towerPullback B b) (towerPullback B p₁)).inv ≫
      Functor.whiskerRight ((openBetaTower B c i₁ i b wi si).hom) (towerPullback B p₁) ≫
        (Functor.associator (towerPullback B c) (towerJ B i₁) (towerPullback B p₁)).hom ≫
      Functor.whiskerLeft (towerPullback B c) (towerAlpha B k₁ r₁ p₁ i₁ h₁) ≫
        (Functor.associator (towerPullback B c) (towerPullback B r₁) (towerJ B k₁)).inv := by
  with_unfolding_all
    exact nativeCubeLaw B (nativeCubeData B k i r p k₁ i₁ r₁ p₁ a b c d h h₁ wk wi wp wr sk si hp
      hr)


-- Capture the public derived-category instances before installing the tower instance.
private abbrev nativeCubeDerivedFunctor (X Y : Scheme.{u}) :=
  Derived B X ⥤ Derived B Y

section DerivedTransport
attribute [local instance] exactPairAdditive
attribute [local instance] clopenTowerAbelian towers_hasDerivedCategory
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] G J alpha beta gComp jComp squareG

private theorem nativeCubeDerivedExternal {Xv Xs Xw Xt Xv₁ Xs₁ Xw₁ Xt₁ : Scheme.{u}}
    (K : Towers B Xv ⥤ₑ Towers B Xw)
    (V : Towers B Xs ⥤ₑ Towers B Xt)
    (R : Towers B Xs ⥤ₑ Towers B Xv)
    (P : Towers B Xt ⥤ₑ Towers B Xw)
    (K₁ : Towers B Xv₁ ⥤ₑ Towers B Xw₁)
    (V₁ : Towers B Xs₁ ⥤ₑ Towers B Xt₁)
    (R₁ : Towers B Xs₁ ⥤ₑ Towers B Xv₁)
    (P₁ : Towers B Xt₁ ⥤ₑ Towers B Xw₁)
    (A : Towers B Xw ⥤ₑ Towers B Xw₁)
    (B' : Towers B Xt ⥤ₑ Towers B Xt₁)
    (C' : Towers B Xs ⥤ₑ Towers B Xs₁)
    (D : Towers B Xv ⥤ₑ Towers B Xv₁)
    (KD : nativeCubeDerivedFunctor B Xv Xw)
    (VD : nativeCubeDerivedFunctor B Xs Xt)
    (RD : nativeCubeDerivedFunctor B Xs Xv)
    (PD : nativeCubeDerivedFunctor B Xt Xw)
    (K₁D : nativeCubeDerivedFunctor B Xv₁ Xw₁)
    (V₁D : nativeCubeDerivedFunctor B Xs₁ Xt₁)
    (R₁D : nativeCubeDerivedFunctor B Xs₁ Xv₁)
    (P₁D : nativeCubeDerivedFunctor B Xt₁ Xw₁)
    (AD : nativeCubeDerivedFunctor B Xw Xw₁)
    (BD : nativeCubeDerivedFunctor B Xt Xt₁)
    (CD : nativeCubeDerivedFunctor B Xs Xs₁)
    (DD : nativeCubeDerivedFunctor B Xv Xv₁)
    (hKD : K.obj.mapDerivedCategory = KD)
    (hVD : V.obj.mapDerivedCategory = VD)
    (hRD : R.obj.mapDerivedCategory = RD)
    (hPD : P.obj.mapDerivedCategory = PD)
    (hK₁D : K₁.obj.mapDerivedCategory = K₁D)
    (hV₁D : V₁.obj.mapDerivedCategory = V₁D)
    (hR₁D : R₁.obj.mapDerivedCategory = R₁D)
    (hP₁D : P₁.obj.mapDerivedCategory = P₁D)
    (hAD : A.obj.mapDerivedCategory = AD)
    (hBD : B'.obj.mapDerivedCategory = BD)
    (hCD : C'.obj.mapDerivedCategory = CD)
    (hDD : D.obj.mapDerivedCategory = DD)
    (ao : V.obj ⋙ P.obj ⟶ R.obj ⋙ K.obj)
    (a₁ : V₁.obj ⋙ P₁.obj ⟶ R₁.obj ⋙ K₁.obj)
    (bk : K.obj ⋙ A.obj ⟶ D.obj ⋙ K₁.obj)
    (bi : V.obj ⋙ B'.obj ⟶ C'.obj ⋙ V₁.obj)
    (sp : B'.obj ⋙ P₁.obj ⟶ P.obj ⋙ A.obj)
    (sr : R.obj ⋙ D.obj ⟶ C'.obj ⋙ R₁.obj)
    (d₀ : VD ⋙ PD ⟶
      RD ⋙ KD)
    (d₁ : V₁D ⋙ P₁D ⟶
      R₁D ⋙ K₁D)
    (dbk : KD ⋙ AD ⟶
      DD ⋙ K₁D)
    (dbi : VD ⋙ BD ⟶
      CD ⋙ V₁D)
    (dp : BD ⋙ P₁D ⟶
      PD ⋙ AD)
    (dr : RD ⋙ DD ⟶
      CD ⋙ R₁D)
    (c₀ : HEq (Word.cell (pastingCategories B) (P := .comp (.edge V) (.edge P))
      (R := .comp (.edge R) (.edge K)) ao) d₀)
    (c₁ : HEq (Word.cell (pastingCategories B) (P := .comp (.edge V₁) (.edge P₁))
      (R := .comp (.edge R₁) (.edge K₁)) a₁) d₁)
    (ckFac : HEq (Word.cell (pastingCategories B) (P := .comp (.edge K) (.edge A))
      (R := .comp (.edge D) (.edge K₁)) bk) dbk)
    (ciFac : HEq (Word.cell (pastingCategories B) (P := .comp (.edge V) (.edge B'))
      (R := .comp (.edge C') (.edge V₁)) bi) dbi)
    (cpFac : HEq (Word.cell (pastingCategories B) (P := .comp (.edge B') (.edge P₁))
      (R := .comp (.edge P) (.edge A)) sp) dp)
    (crFac : HEq (Word.cell (pastingCategories B) (P := .comp (.edge R) (.edge D))
      (R := .comp (.edge C') (.edge R₁)) sr) dr)
    (law : Functor.whiskerLeft V.obj sp ≫ (Functor.associator V.obj P.obj A.obj).inv ≫
        Functor.whiskerRight ao A.obj ≫ (Functor.associator R.obj K.obj A.obj).hom ≫
        Functor.whiskerLeft R.obj bk ≫ (Functor.associator R.obj D.obj K₁.obj).inv ≫
        Functor.whiskerRight sr K₁.obj =
      (Functor.associator V.obj B'.obj P₁.obj).inv ≫ Functor.whiskerRight bi P₁.obj ≫
        (Functor.associator C'.obj V₁.obj P₁.obj).hom ≫ Functor.whiskerLeft C'.obj a₁ ≫
        (Functor.associator C'.obj R₁.obj K₁.obj).inv)
    : ∀ N : Derived B Xs,
      dp.app (VD.obj N) ≫ AD.map (d₀.app
      N) ≫
          dbk.app (RD.obj N) ≫ K₁D.map
      (dr.app N) =
        P₁D.map (dbi.app N) ≫ d₁.app
      (CD.obj N) := by
  cases hKD
  cases hVD
  cases hRD
  cases hPD
  cases hK₁D
  cases hV₁D
  cases hR₁D
  cases hP₁D
  cases hAD
  cases hBD
  cases hCD
  cases hDD
  exact
    @genericCubeDerived Scheme.{u} (pastingCategories B)
      (fun X ↦ inferInstanceAs (Category.{u + 1} (Towers B X)))
      (fun X ↦ clopenTowerAbelian B X) (fun X ↦ towers_hasDerivedCategory B X)
      Xv Xs Xw Xt Xv₁ Xs₁ Xw₁ Xt₁
      K V R P K₁ V₁ R₁ P₁ A B' C' D ao a₁ bk bi
        sp sr d₀ d₁ dbk dbi dp dr (eq_of_heq c₀) (eq_of_heq c₁) (eq_of_heq ckFac)
        (eq_of_heq ciFac) (eq_of_heq cpFac)
        (eq_of_heq crFac) law

private theorem cube_derived {V W S T V₁ W₁ S₁ T₁ : Scheme.{u}}
    (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
    (k₁ : V₁ ⟶ W₁) (i₁ : S₁ ⟶ T₁) (r₁ : V₁ ⟶ S₁) (p₁ : W₁ ⟶ T₁)
    (a : W₁ ⟶ W) (b : T₁ ⟶ T) (c : S₁ ⟶ S) (d : V₁ ⟶ V)
    [IsOpenImmersion k] [IsOpenImmersion i]
    [IsOpenImmersion k₁] [IsOpenImmersion i₁]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact k₁] [QuasiCompact i₁]
    [IsProper r] [IsProper p] [IsProper r₁] [IsProper p₁]
    (h : k ≫ p = r ≫ i) (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
    (wk : d ≫ k = k₁ ≫ a) (wi : c ≫ i = i₁ ≫ b)
    (wp : a ≫ p = p₁ ≫ b) (wr : d ≫ r = r₁ ≫ c)
    (sk : IsPullback d k₁ k a) (si : IsPullback c i₁ i b)
    (hp : IsPullback a p₁ p b) (hr : IsPullback d r₁ r c) :
    ∀ N : Derived B S,
      (squareG B a p₁ p b wp).hom.app ((J B i).obj N) ≫
          (G B a).map ((alpha B k r p i h).app N) ≫
          (beta B d k₁ k a wk sk).hom.app ((G B r).obj N) ≫
          (J B k₁).map ((squareG B d r₁ r c wr).inv.app N) =
        (G B p₁).map ((beta B c i₁ i b wi si).hom.app N) ≫
          (alpha B k₁ r₁ p₁ i₁ h₁).app ((G B c).obj N) := by
  exact @nativeCubeDerivedExternal B _ V S W T V₁ S₁ W₁ T₁
    (ExactFunctor.of (towerJ B k))
    (ExactFunctor.of (towerJ B i))
    (ExactFunctor.of (towerPullback B r))
    (ExactFunctor.of (towerPullback B p))
    (ExactFunctor.of (towerJ B k₁))
    (ExactFunctor.of (towerJ B i₁))
    (ExactFunctor.of (towerPullback B r₁))
    (ExactFunctor.of (towerPullback B p₁))
    (ExactFunctor.of (towerPullback B a))
    (ExactFunctor.of (towerPullback B b))
    (ExactFunctor.of (towerPullback B c))
    (ExactFunctor.of (towerPullback B d))
    (by
      with_unfolding_all
        exact J B k)
    (by
      with_unfolding_all
        exact J B i)
    (by
      with_unfolding_all
        exact G B r)
    (by
      with_unfolding_all
        exact G B p)
    (by
      with_unfolding_all
        exact J B k₁)
    (by
      with_unfolding_all
        exact J B i₁)
    (by
      with_unfolding_all
        exact G B r₁)
    (by
      with_unfolding_all
        exact G B p₁)
    (by
      with_unfolding_all
        exact G B a)
    (by
      with_unfolding_all
        exact G B b)
    (by
      with_unfolding_all
        exact G B c)
    (by
      with_unfolding_all
        exact G B d)
    (by
      with_unfolding_all rfl)
    (by
      with_unfolding_all rfl)
    (by
      with_unfolding_all rfl)
    (by
      with_unfolding_all rfl)
    (by
      with_unfolding_all rfl)
    (by
      with_unfolding_all rfl)
    (by
      with_unfolding_all rfl)
    (by
      with_unfolding_all rfl)
    (by
      with_unfolding_all rfl)
    (by
      with_unfolding_all rfl)
    (by
      with_unfolding_all rfl)
    (by
      with_unfolding_all rfl)
    (towerAlpha B k r p i h)
    (towerAlpha B k₁ r₁ p₁ i₁ h₁)
    ((openBetaTower B d k₁ k a wk sk).hom)
    ((openBetaTower B c i₁ i b wi si).hom)
    ((towerSquare (modulePullback B b) (modulePullback B p₁) (modulePullback B p)
        (modulePullback B a) (moduleSquareG B a p₁ p b wp)).hom)
    ((towerSquare (modulePullback B c) (modulePullback B r₁) (modulePullback B r)
        (modulePullback B d) (moduleSquareG B d r₁ r c wr)).inv)
    (by
      with_unfolding_all
        exact alpha B k r p i h)
    (by
      with_unfolding_all
        exact alpha B k₁ r₁ p₁ i₁ h₁)
    (by
      with_unfolding_all
        exact (beta B d k₁ k a wk sk).hom)
    (by
      with_unfolding_all
        exact (beta B c i₁ i b wi si).hom)
    (by
      with_unfolding_all
        exact (squareG B a p₁ p b wp).hom)
    (by
      with_unfolding_all
        exact (squareG B d r₁ r c wr).inv)
    (by
      with_unfolding_all
        exact heq_of_eq (pastingAlpha B k r p i h))
    (by
      with_unfolding_all
        exact heq_of_eq (pastingAlpha B k₁ r₁ p₁ i₁ h₁))
    (by
      with_unfolding_all
        exact heq_of_eq (pastingBeta B d k₁ k a wk sk))
    (by
      with_unfolding_all
        exact heq_of_eq (pastingBeta B c i₁ i b wi si))
    (by
      with_unfolding_all
        exact heq_of_eq (pastingSquare B a p₁ p b wp))
    (by
      with_unfolding_all
        exact heq_of_eq (pastingSquareInv B d r₁ r c wr))
    (by
      exact towerAlpha_baseChange B k i r p k₁ i₁ r₁ p₁ a b c d h h₁ wk wi wp wr sk si hp hr)

end DerivedTransport

end AlgebraicGeometry.ProEtale.StrictTower
