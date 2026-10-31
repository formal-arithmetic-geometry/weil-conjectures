/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralQuotientDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.CondensedAmbientExchange
public import WeilConjectures.AlgebraicGeometry.SectionDerivedPushpullNormalization
public import WeilConjectures.CategoryTheory.InternalSectionScalarAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.ScalarGeometricExchangeRectangle
import all WeilConjectures.AlgebraicGeometry.ScalarGeometricExchangeRectangle
import all WeilConjectures.AlgebraicGeometry.NormalizedScalarRestrictionPush
import WeilConjectures.AlgebraicGeometry.NormalizedScalarSectionFamily

/-! # Reduction of the actual unbounded integral exchange

Source: blueprint main-20261015, integral proper-base-change proof, paragraph (3);
Stacks Project, Tags 07A7, 0E47 and 0E48
(blueprint: lem-sfb-integral-quotient-exchange-comparison).

The equality is an equality of natural transformations. Its section-module realization
uses the independently specified ringed adjunctions and geometric compositors. Scalar
comparisons retain their balanced-generator and K-flat computation normalizations.
As in the direct-image comparison, n denotes quotient exponent n + 1.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProEtale.QuotientChange
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory
  mateEquiv AlgebraicGeometry.ProEtale.upperStarFromPoint
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedFunctor
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedPullback
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedPushforward
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedAdjunction
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedPullComparison
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedPushComparison
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedPullbackComposition
  AlgebraicGeometry.ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction
  AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarComp


open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct ChangeOfRings

private theorem section_natTrans_ext
    {A B C : Type*} [Category A] [Category B] [Category C]
    (E : A ⥤ B) [E.EssSurj] {F G : B ⥤ C} (α β : F ⟶ G)
    (h : ∀ X : A, α.app (E.obj X) = β.app (E.obj X)) : α = β := by
  apply NatTrans.ext
  funext Y
  let e := E.objObjPreimageIso Y
  rw [← cancel_epi (F.map e.hom), α.naturality, β.naturality, h]

private theorem route_natTrans_ext
    {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : Type*}
    [Category A₀] [Category A₁] [Category A₂] [Category A₃]
    [Category B₀] [Category B₁] [Category B₂] [Category B₃]
    {rf : A₁ ⥤ A₀} {c : A₀ ⥤ A₂} {rg : A₃ ⥤ A₂} {h : A₁ ⥤ A₃}
    {T₀ : A₀ ⥤ B₀} {T₁ : A₁ ⥤ B₁} {T₃ : A₃ ⥤ B₃}
    {rfb : B₁ ⥤ B₀} {ab : B₁ ⥤ B₃} {rgb : B₃ ⥤ B₂}
    (cb : B₀ ⥤ B₂) (T₂ : A₂ ⥤ B₂)
    (r : rf ⋙ T₀ ⟶ T₁ ⋙ rfb) (eb : rfb ⋙ cb ⟶ ab ⋙ rgb)
    (la : T₁ ⋙ ab ⟶ h ⋙ T₃) (lc : T₀ ⋙ cb ⟶ c ⋙ T₂)
    (e : rf ⋙ c ⟶ h ⋙ rg) (t : rg ⋙ T₂ ⟶ T₃ ⋙ rgb)
    (he : ∀ J, mateRouteLeft cb r eb la J = mateRouteRight T₂ lc e t J) :
    Functor.whiskerRight r cb ≫ Functor.whiskerLeft T₁ eb ≫
        Functor.whiskerRight la rgb =
      Functor.whiskerLeft rf lc ≫ Functor.whiskerRight e T₂ ≫
        Functor.whiskerLeft h t := by
  apply NatTrans.ext
  funext J
  exact he J

private theorem route_natTrans_ext_inv
    {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ C : Type*}
    [Category A₀] [Category A₁] [Category A₂] [Category A₃]
    [Category B₀] [Category B₁] [Category B₂] [Category B₃] [Category C]
    {rf : A₁ ⥤ A₀} {c : A₀ ⥤ A₂} {rg : A₃ ⥤ A₂} {h : A₁ ⥤ A₃}
    {T₀ : A₀ ⥤ B₀} {T₁ : A₁ ⥤ B₁} {T₃ : A₃ ⥤ B₃}
    {rfb : B₁ ⥤ B₀} {ab : B₁ ⥤ B₃} {rgb : B₃ ⥤ B₂}
    (cb : B₀ ⥤ B₂) (T₂ : A₂ ⥤ B₂)
    (r : rf ⋙ T₀ ⟶ T₁ ⋙ rfb) (eb : rfb ⋙ cb ⟶ ab ⋙ rgb)
    (la : T₁ ⋙ ab ≅ h ⋙ T₃) (lc : T₀ ⋙ cb ⟶ c ⋙ T₂)
    (e : rf ⋙ c ⟶ h ⋙ rg) (t : rg ⋙ T₂ ⟶ T₃ ⋙ rgb)
    (E : C ⥤ A₁) [E.EssSurj]
    (he : ∀ J, mateRouteLeft cb r eb la.hom (E.obj J) =
      mateRouteRight T₂ lc e t (E.obj J)) :
    Functor.whiskerRight r cb ≫ Functor.whiskerLeft T₁ eb =
      Functor.whiskerLeft rf lc ≫ Functor.whiskerRight e T₂ ≫
        Functor.whiskerLeft h t ≫ Functor.whiskerRight la.inv rgb := by
  apply section_natTrans_ext E
  intro J
  dsimp only [mateRouteLeft, mateRouteRight] at he
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    ← Category.assoc]
  apply (rgb.mapIso (la.app (E.obj J))).eq_comp_inv.mpr
  simpa only [Category.assoc, Functor.mapIso_hom, Iso.app_hom] using he J

namespace AlgebraicGeometry.ProEtale.IntegralQuotient

section Ambient

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The recorded actual ambient exchange, with the direct-image comparison's typed
interfaces. Source: Stacks 07A7
(blueprint: lem-sfb-integral-quotient-exchange-comparison). -/
def ambient (sq : ChosenCartesianSquare h f' f g) :
    F Λ f ⋙ L Λ g ⟶ L Λ h ⋙ F Λ f' :=
  (mateEquiv (adj Λ f) (adj Λ f')
    (TwoSquare.mk _ _ _ _ (scalarPullbackSquare Λ sq).hom)).natTrans

variable [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T)]

/-- The independently specified section-module geometric square: compose the actual
ringed derived pullbacks along the two equal scheme composites.
Source: Stacks 0D6D and 07A7
(blueprint: lem-sfb-integral-quotient-exchange-comparison). -/
def sectionSquare (sq : ChosenCartesianSquare h f' f g) :
    ModuleRingedComparison.derivedPullback Λ g ⋙
        ModuleRingedComparison.derivedPullback Λ f' ≅
      ModuleRingedComparison.derivedPullback Λ f ⋙
        ModuleRingedComparison.derivedPullback Λ h :=
  (ModuleRingedComparison.derivedPullbackComposition Λ f' g).symm ≪≫
    eqToIso (congrArg
      (fun k : X' ⟶ Y ↦ ModuleRingedComparison.derivedPullback Λ k)
      sq.toCommSq.w.symm) ≪≫
    ModuleRingedComparison.derivedPullbackComposition Λ h f

/-- The actual ringed exchange, formed with the independently derived section-module
adjunctions and the geometric square, before any completeness condition.
Source: Stacks 07A7 (blueprint: lem-sfb-integral-quotient-exchange-comparison). -/
def sectionExchange (sq : ChosenCartesianSquare h f' f g) :
    ModuleRingedComparison.derivedPushforward Λ f ⋙
        ModuleRingedComparison.derivedPullback Λ g ⟶
      ModuleRingedComparison.derivedPullback Λ h ⋙
        ModuleRingedComparison.derivedPushforward Λ f' :=
  (mateEquiv (ModuleRingedComparison.derivedAdjunction Λ f)
    (ModuleRingedComparison.derivedAdjunction Λ f')
    (TwoSquare.mk _ _ _ _ (sectionSquare Λ sq).hom)).natTrans

/-- The existing normalized pullback comparison, with its internal endpoint made explicit.
Source: Stacks 07A6 (blueprint: lem-sfb-integral-quotient-exchange-comparison). -/
def pullSection {U V : Scheme.{u}} (u : U ⟶ V) :
    L Λ u ⋙ ModuleRingedComparison.derivedFunctor Λ U ≅
      ModuleRingedComparison.derivedFunctor Λ V ⋙ ModuleRingedComparison.derivedPullback Λ u :=
  scalarSectionPullComparison Λ u

/-- The existing normalized pushforward comparison, with its internal endpoint explicit.
Source: Stacks 07A6 (blueprint: lem-sfb-integral-quotient-exchange-comparison). -/
def pushSection {U V : Scheme.{u}} (u : U ⟶ V) :
    F Λ u ⋙ ModuleRingedComparison.derivedFunctor Λ V ≅
      ModuleRingedComparison.derivedFunctor Λ U ⋙
        ModuleRingedComparison.derivedPushforward Λ u :=
  scalarSectionPushComparison Λ u

/-- Identification of the actual exchanges under the fixed termwise section equivalences
and their normalized push/pull comparisons. This asserts equality of the transformations,
including the unit, geometric square and counit, rather than just their endpoints.
Source: Stacks 07A7 and 09T5
(blueprint: lem-sfb-integral-quotient-exchange-comparison). -/
def ExchangeRealized (sq : ChosenCartesianSquare h f' f g) : Prop :=
  ∀ K : DerivedCategory (Modules Λ X),
    mateRouteLeft (ModuleRingedComparison.derivedFunctor Λ Y')
        (ambient Λ sq) (pushSection Λ f').hom (pullSection Λ h).hom K =
      mateRouteRight (ModuleRingedComparison.derivedPullback Λ g)
        (pullSection Λ g).hom (pushSection Λ f).hom (sectionExchange Λ sq) K

attribute [local irreducible] ambient sectionSquare sectionExchange pullSection pushSection
  scalarAmbientExchange scalarSectionPushComparison scalarSectionPullComparison
  sectionRectangleExchange

omit [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T)] in
private theorem ambient_eq_scalar (sq : ChosenCartesianSquare h f' f g) :
    ambient Λ sq = scalarAmbientExchange Λ sq := by
  delta ambient scalarAmbientExchange
  rfl

private theorem pullSection_eq {U V : Scheme.{u}} (a : U ⟶ V) :
    pullSection Λ a = scalarSectionPullComparison Λ a := by
  delta pullSection
  rfl

private theorem pushSection_hom_eq {U V : Scheme.{u}} (a : U ⟶ V) :
    (pushSection Λ a).hom = (scalarSectionPushComparison Λ a).hom := by
  delta pushSection
  rfl

private theorem sectionExchange_eq (sq : ChosenCartesianSquare h f' f g) :
    sectionExchange Λ sq = sectionRectangleExchange Λ sq := by
  delta sectionExchange sectionRectangleExchange sectionSquare
  rfl

private theorem exchange_realized (sq : ChosenCartesianSquare h f' f g) :
    ExchangeRealized Λ sq := by
  unfold ExchangeRealized
  intro K
  rw [ambient_eq_scalar, sectionExchange_eq, pullSection_eq, pullSection_eq,
    pushSection_hom_eq, pushSection_hom_eq]
  exact exchange_section Λ sq K

end Ambient

set_option allowUnsafeReducibility true
attribute [local semireducible] ModuleRingedComparison.derivedFunctor

/-- Ordinary balanced generators and K-flat computation characterize the scalar
realization, before specializing the coefficient map.
Source: Stacks 03EK, 06YY and 09T5
(blueprint: lem-sfb-integral-quotient-exchange-comparison). -/
def ScalarComparisonRealized
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R T)]
    [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules S T)]
    (a : R ⟶ S) [IsMonHom a] (T : Scheme.{u})
    (q : SheafOfModules.ScalarDerivedPair
      (J := Scheme.ProEt.topology T)
      (R := ModuleRingedComparison.ring R T)
      (S := ModuleRingedComparison.ring S T)
      (InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
        (Scheme.ProEt.topology T) (coefficientMap a T)))
    (e₀ : extension a T ⋙
        (ModuleRingedComparison.equivalence S T).functor ≅
      (ModuleRingedComparison.equivalence R T).functor ⋙ q.extension)
    (e : D a T ⋙
        ModuleRingedComparison.derivedFunctor S T ≅
      ModuleRingedComparison.derivedFunctor R T ⋙ q.derived) : Prop :=
  (∀ (M : Modules R T) (U : T.ProEtᵒᵖ)
      (s : (condensedRingObj S T).obj.obj U) (m : M.X.obj.obj U),
    ((eqToHom (q.extension_obj
      ((ModuleRingedComparison.equivalence R T).functor.obj M))).val.app U)
        ((e₀.hom.app M).val.app U
          (InternalAbelianSheafModule.internalScalarGenerator (Scheme.ProEt.topology T)
            (coefficientMap a T) M U s m)) =
      (toSheafify (Scheme.ProEt.topology T)
        (SheafOfModules.changeOfRingsPresheaf
          (InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
            (Scheme.ProEt.topology T) (coefficientMap a T))
          ((ModuleRingedComparison.equivalence R T).functor.obj M)).presheaf).app U
        (s ⊗ₜ[(ModuleRingedComparison.ring R T).obj.obj U,
            ((InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
              (Scheme.ProEt.topology T) (coefficientMap a T)).hom.app U).hom] m)) ∧
  (∀ P : CochainComplex (Modules R T) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients
        (R := ModuleRingedComparison.ring R T)
        (((ModuleRingedComparison.equivalence R T).functor.mapHomologicalComplex
          (.up ℤ)).obj P) →
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology T)
      (R := ModuleRingedComparison.ring R T)
      ((ModuleRingedComparison.equivalence R T).functor.obj (P.X i))) →
    (ModuleRingedComparison.derivedFunctor S T).map
        (compute a T P) ≫
        (Functor.mapDerivedCategoryFactors
          (ModuleRingedComparison.equivalence S T).functor).hom.app
            (((extension a T).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e₀ (.up ℤ)).hom.app P) =
      e.hom.app (DerivedCategory.Q.obj P) ≫
        q.derived.map
          (ModuleRingedComparison.sectionLocalizationComparison R T P).hom ≫
        SheafOfModules.scalarPairComplexComparison q.extension q.extension_additive
          q.derived q.counit
          (((ModuleRingedComparison.equivalence R T).functor.mapHomologicalComplex
          (.up ℤ)).obj P))


private theorem scalar_comparison_realized
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R T)]
    [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules S T)]
    (a : R ⟶ S) [IsMonHom a] (T : Scheme.{u})
    (s : SectionScalarComparison a T) (hs : SectionScalarNormalized a T s) :
    ScalarComparisonRealized a T s.pair s.ordinary s.derived := by
  exact ⟨hs.2.1, hs.2.2⟩


section ScalarSectionRealization

variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules S T)]
  (a : R ⟶ S) [IsMonHom a]

private theorem internal_rectangle
    (b : ∀ {U V : Scheme.{u}} (u : U ⟶ V),
      D a V ⋙ L S u ≅ L R u ⋙ D a U)
    (hb : ∀ {U V : Scheme.{u}} (u : U ⟶ V), PullNormalized a u (b u))
    {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare h f' f g) :
    (Functor.whiskerRight (rho a f (b f)) (L S g) ≫
        Functor.whiskerLeft (D a X) (ambient S sq) ≫
        Functor.whiskerRight (b h).hom (F S f') =
      Functor.whiskerLeft (F R f) (b g).hom ≫
        Functor.whiskerRight (ambient R sq) (D a Y') ≫
        Functor.whiskerLeft (L R h) (rho a f' (b f'))) := by
  simp only [ambient_eq_scalar]
  exact route_natTrans_ext (L S g) (D a Y')
    (rho a f (b f)) (scalarAmbientExchange S sq) (b h).hom (b g).hom
    (scalarAmbientExchange R sq) (rho a f' (b f'))
    (fun K ↦ (scalar_geometric_exchange_rectangle a sq b hb K).1)

/-- The actual section scalar/geometric mate for a general coefficient map.
Source: Stacks 07A7 and 0E48
(blueprint: lem-sfb-integral-quotient-exchange-comparison). -/
def sectionScalarProjection
    (q : ∀ T : Scheme.{u}, SheafOfModules.ScalarDerivedPair
      (J := Scheme.ProEt.topology T)
      (R := ModuleRingedComparison.ring R T)
      (S := ModuleRingedComparison.ring S T)
      (InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
        (Scheme.ProEt.topology T) (coefficientMap a T)))
    {U V : Scheme.{u}} (u : U ⟶ V)
    (χ : (q V).derived ⋙ ModuleRingedComparison.derivedPullback S u ≅
      ModuleRingedComparison.derivedPullback R u ⋙ (q U).derived) :
    ModuleRingedComparison.derivedPushforward R u ⋙ (q V).derived ⟶
      (q U).derived ⋙ ModuleRingedComparison.derivedPushforward S u :=
  (mateEquiv (ModuleRingedComparison.derivedAdjunction R u)
    (ModuleRingedComparison.derivedAdjunction S u)
    (TwoSquare.mk _ _ _ _ χ.hom)).natTrans

attribute [local irreducible] ScalarComparisonRealized sectionScalarProjection
  SectionScalarNormalized SectionPullNormalized rho scalarExchangeLeft scalarExchangeRight
  sectionRectangleLambda sectionRectangleRho sectionRectangleLeft sectionRectangleRight
  sectionRectangleSource sectionRectangleTarget

/-- Simultaneous realization of scalar change, balancing, its projection mate, and
both routes of the geometric exchange. This predicate names the full existential
section comparison; its scalar, geometric and mate maps are independently specified.
Source: Stacks 03EK, 06YY, 07A7, 09T5 and 0E48
(blueprint: lem-sfb-integral-quotient-exchange-comparison). -/
@[irreducible] def SectionExchangeRealized
    (b : ∀ {U V : Scheme.{u}} (u : U ⟶ V),
      D a V ⋙ L S u ≅ L R u ⋙ D a U)
    {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare h f' f g) : Prop :=
    ∃ q : ∀ T : Scheme.{u}, SheafOfModules.ScalarDerivedPair
      (J := Scheme.ProEt.topology T)
      (R := ModuleRingedComparison.ring R T)
      (S := ModuleRingedComparison.ring S T)
      (InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
        (Scheme.ProEt.topology T) (coefficientMap a T)),
    ∃ e₀ : ∀ T : Scheme.{u},
        extension a T ⋙
            (ModuleRingedComparison.equivalence S T).functor ≅
          (ModuleRingedComparison.equivalence R T).functor ⋙ (q T).extension,
    ∃ e : ∀ T : Scheme.{u},
        D a T ⋙ ModuleRingedComparison.derivedFunctor S T ≅
          ModuleRingedComparison.derivedFunctor R T ⋙ (q T).derived,
      (∀ T : Scheme.{u}, ScalarComparisonRealized a T (q T) (e₀ T) (e T)) ∧
    ∃ χ : ∀ {U V : Scheme.{u}} (u : U ⟶ V),
        (q V).derived ⋙ ModuleRingedComparison.derivedPullback S u ≅
          ModuleRingedComparison.derivedPullback R u ⋙ (q U).derived,
      (∀ {U V : Scheme.{u}} (u : U ⟶ V) (M : DerivedCategory (Modules R V)),
        (pullSection S u).hom.app
            ((D a V).obj M) ≫
            (ModuleRingedComparison.derivedPullback S u).map
              ((e V).hom.app M) ≫
            (χ u).hom.app ((ModuleRingedComparison.derivedFunctor R V).obj M) =
          (ModuleRingedComparison.derivedFunctor S U).map ((b u).hom.app M) ≫
            (e U).hom.app ((L R u).obj M) ≫
            (q U).derived.map
              ((pullSection R u).hom.app M)) ∧
      (∀ {U V : Scheme.{u}} (u : U ⟶ V) (K : DerivedCategory (Modules R U)),
        (ModuleRingedComparison.derivedFunctor S V).map
            ((rho a u (b u)).app K) ≫
            (pushSection S u).hom.app
              ((D a U).obj K) ≫
            (ModuleRingedComparison.derivedPushforward S u).map
              ((e U).hom.app K) =
          (e V).hom.app ((F R u).obj K) ≫
            (q V).derived.map
              ((pushSection R u).hom.app K) ≫
            (sectionScalarProjection a q u (χ u)).app
              ((ModuleRingedComparison.derivedFunctor R U).obj K)) ∧
      (Functor.whiskerRight (sectionScalarProjection a q f (χ f))
          (ModuleRingedComparison.derivedPullback S g) ≫
        Functor.whiskerLeft (q X).derived (sectionExchange S sq) =
      Functor.whiskerLeft (ModuleRingedComparison.derivedPushforward R f)
          (χ g).hom ≫
        Functor.whiskerRight (sectionExchange R sq) (q Y').derived ≫
        Functor.whiskerLeft (ModuleRingedComparison.derivedPullback R h)
          (sectionScalarProjection a q f' (χ f')) ≫
        Functor.whiskerRight (χ h).inv
          (ModuleRingedComparison.derivedPushforward S f'))

private theorem section_exchange_realized
    (b : ∀ {U V : Scheme.{u}} (u : U ⟶ V),
      D a V ⋙ L S u ≅ L R u ⋙ D a U)
    (hb : ∀ {U V : Scheme.{u}} (u : U ⟶ V), PullNormalized a u (b u))
    {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare h f' f g) : SectionExchangeRealized a b sq := by
  classical
  unfold SectionExchangeRealized
  obtain ⟨s, hs, p⟩ := normalized_scalar_section_family a b hb
  refine ⟨fun T ↦ (s T).pair, fun T ↦ (s T).ordinary, fun T ↦ (s T).derived, ?_,
    fun u ↦ sectionRectangleLambda a u _ _ (b u) (p u), ?_, ?_, ?_⟩
  · intro T
    exact scalar_comparison_realized a T (s T) (hs T)
  · intro U V u M
    simpa only [pullSection_eq, ModuleRingedComparison.derivedEquivalence,
      Functor.asEquivalence] using
      (lambda_section a u (s U) (s V) (b u) (p u) M).symm
  · intro U V u K
    simpa only [pushSection_hom_eq, sectionScalarProjection, sectionRectangleRho,
      ModuleRingedComparison.derivedEquivalence, Functor.asEquivalence] using
      rho_section a u (s U) (s V) (b u) (p u) K
  · have hrho : ∀ {U V : Scheme.{u}} (u : U ⟶ V),
        sectionScalarProjection a (fun T ↦ (s T).pair) u
            (sectionRectangleLambda a u (s U) (s V) (b u) (p u)) =
          sectionRectangleRho a u (s U) (s V) (b u) (p u) := by
      intro U V u
      delta sectionScalarProjection sectionRectangleRho
      rfl
    simp only [hrho, sectionExchange_eq]
    apply route_natTrans_ext_inv
      (ModuleRingedComparison.derivedPullback S g) (s Y').pair.derived
      (sectionRectangleRho a f (s X) (s Y) (b f) (p f))
      (sectionRectangleExchange S sq)
      (sectionRectangleLambda a h (s X') (s X) (b h) (p h))
      (sectionRectangleLambda a g (s Y') (s Y) (b g) (p g)).hom
      (sectionRectangleExchange R sq)
      (sectionRectangleRho a f' (s X') (s Y') (b f') (p f'))
      (ModuleRingedComparison.derivedFunctor R X)
    intro K
    have he := (scalar_geometric_exchange_rectangle a sq b hb K).1
    have hl := left_route_section a sq b s p K
    have hr := right_route_section a sq b s p K
    have hsec : sectionRectangleLeft a sq b s p K =
        sectionRectangleRight a sq b s p K := by
      apply (cancel_epi (sectionRectangleSource a f g (s Y) K).hom).mp
      exact hl.symm.trans ((congrArg (fun z ↦
        (ModuleRingedComparison.derivedFunctor S Y').map z ≫
          (sectionRectangleTarget a h f' (s X') K).hom) he).trans hr)
    simpa only [sectionRectangleLeft, sectionRectangleRight] using hsec
end ScalarSectionRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The actual finite projection reconstructed as a section-ring map.
Source: blueprint integral proof (3); Stacks 03EK
(blueprint: lem-sfb-integral-quotient-exchange-comparison). -/
abbrev sectionReduction (T : Scheme.{u}) (n : ℕ) :
    ModuleRingedComparison.ring (integral l E) T ⟶
      ModuleRingedComparison.ring (finite l E n) T :=
  InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
    (coefficientMap (reduction l E n) T)

variable (n : ℕ)
  [∀ T : Scheme.{u},
    HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules (integral l E) T)]
  [∀ T : Scheme.{u},
    HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules (finite l E n) T)]

/-- The complete normalization of the scalar realization: unchanged balanced generators
on ordinary sheafification and the universal comparison on flat-term K-flat complexes.
Thus the section scalar functor is the actual uncompleted derived extension, and the
comparison has no scalar twist. Source: Stacks 03EK, 06YY and 09T5
(blueprint: lem-sfb-integral-quotient-exchange-comparison). -/
def ScalarRealized (T : Scheme.{u})
    (q : SheafOfModules.ScalarDerivedPair
      (J := Scheme.ProEt.topology T)
      (R := ModuleRingedComparison.ring (integral l E) T)
      (S := ModuleRingedComparison.ring (finite l E n) T) (sectionReduction l E T n))
    (e₀ : extension (reduction l E n) T ⋙
        (ModuleRingedComparison.equivalence (finite l E n) T).functor ≅
      (ModuleRingedComparison.equivalence (integral l E) T).functor ⋙ q.extension)
    (e : D (reduction l E n) T ⋙
        ModuleRingedComparison.derivedFunctor (finite l E n) T ≅
      ModuleRingedComparison.derivedFunctor (integral l E) T ⋙ q.derived) : Prop :=
  ScalarComparisonRealized (reduction l E n) T q e₀ e

/-- The specified finite projection in section coordinates: it is the counit-adjunct
mate of the normalized scalar/pullback comparison under the actual ringed adjunctions.
Source: Stacks 07A7 and 0E48
(blueprint: lem-sfb-integral-quotient-exchange-comparison). -/
def sectionProjection
    (q : ∀ T : Scheme.{u}, SheafOfModules.ScalarDerivedPair
      (J := Scheme.ProEt.topology T)
      (R := ModuleRingedComparison.ring (integral l E) T)
      (S := ModuleRingedComparison.ring (finite l E n) T) (sectionReduction l E T n))
    {U V : Scheme.{u}} (u : U ⟶ V)
    (χ : (q V).derived ⋙ ModuleRingedComparison.derivedPullback (finite l E n) u ≅
      ModuleRingedComparison.derivedPullback (integral l E) u ⋙ (q U).derived) :
    ModuleRingedComparison.derivedPushforward (integral l E) u ⋙ (q V).derived ⟶
      (q U).derived ⋙ ModuleRingedComparison.derivedPushforward (finite l E n) u :=
  sectionScalarProjection (reduction l E n) q u χ

variable
    (b : ∀ {U V : Scheme.{u}} (u : U ⟶ V),
      D (reduction l E n) V ⋙ L (finite l E n) u ≅
        L (integral l E) u ⋙ D (reduction l E n) U)
    {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}


/-- The normalized unbounded integral exchange equality and its actual section-module
finite-rectangle realization, naturally in the input complex.

Source: blueprint main-20261015, integral proper-base-change proof, paragraph (3),
"the reduction of each canonical map is the corresponding canonical map for the torsion
reductions"; Stacks Tags 07A7, 0E47 and 0E48
(blueprint: lem-sfb-integral-quotient-exchange-comparison).

Proof:
1. Specialize scalar_geometric_exchange_rectangle to the actual condensed reduction
map and the given normalized b. Its ambient exchange is the one defined here, so
componentwise extensionality gives the asserted natural-transformation equality.
2. Normalized comparisons have the same inverse scalar-adjunction mate, by the
normalized_inverse calculation. Thus b equals the normalized comparison supplied
by integral_quotient_direct_image_comparison, and its two rho maps are invertible.
3. The generic rectangle's proved exchange_section calculation identifies the
actual geometric exchanges with sectionExchange. Its pull and push comparisons
are exactly pullSection and pushSection, giving both ExchangeRealized clauses.
4. Choose one simultaneous normalized section scalar family using
normalized_scalar_section_family. Its generator and K-flat counit equations are
ScalarRealized. Its specified sectionRectangleLambda gives chi; lambda_section
and rho_section identify balancing and its independently formed geometric mate.
5. For that same family, transport the internal rectangle with left_route_section
and right_route_section and cancel the source comparison. Naturality and essential
surjectivity of the section equivalence extend the equality to all section objects.
Postcomposing with direct image of chi_h.hom and cancelling its inverse gives the
last rectangle exactly as written. No exchange map is inverted and no properness,
completeness, boundedness, constructibility or coefficient-flatness is used. -/
theorem integral_quotient_exchange_comparison
    (hb : ∀ {U V : Scheme.{u}} (u : U ⟶ V),
      PullNormalized (reduction l E n) u (b u))
    (sq : ChosenCartesianSquare h f' f g) :
    (Functor.whiskerRight (rho (reduction l E n) f (b f)) (L (finite l E n) g) ≫
        Functor.whiskerLeft (D (reduction l E n) X) (ambient (finite l E n) sq) ≫
        Functor.whiskerRight (b h).hom (F (finite l E n) f') =
      Functor.whiskerLeft (F (integral l E) f) (b g).hom ≫
        Functor.whiskerRight (ambient (integral l E) sq) (D (reduction l E n) Y') ≫
        Functor.whiskerLeft (L (integral l E) h) (rho (reduction l E n) f' (b f'))) ∧
    IsIso (rho (reduction l E n) f (b f)) ∧
    IsIso (rho (reduction l E n) f' (b f')) ∧
    ExchangeRealized (integral l E) sq ∧ ExchangeRealized (finite l E n) sq ∧
    SectionExchangeRealized (reduction l E n) b sq := by
  classical
  have hi : ∀ {U V : Scheme.{u}} (a : U ⟶ V),
      IsIso (rho (reduction l E n) a (b a)) := by
    intro U V a
    obtain ⟨_, _, _, c, hc, hci, _⟩ := integral_quotient_direct_image_comparison l E
    have he : b a = c a n := by
      apply Iso.symm_eq_iff.mp
      apply Iso.ext
      exact (normalized_inverse (reduction l E n) a (b a) (hb a)).trans
        (normalized_inverse (reduction l E n) a (c a n) (hc a n)).symm
    rw [he]
    exact hci a n
  refine ⟨?_, hi f, hi f', exchange_realized _ sq, exchange_realized _ sq, ?_⟩
  · exact internal_rectangle (reduction l E n) b hb sq
  · exact section_exchange_realized (reduction l E n) b hb sq


end AlgebraicGeometry.ProEtale.IntegralQuotient
