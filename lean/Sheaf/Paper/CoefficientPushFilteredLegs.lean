/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.ModuleRingedToposDerivedComparison
public import Sheaf.Paper.IntegralResidueTensorPullPresentation
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Sheaf.Paper.CanonicalCoefficientTensorNormalization
import Sheaf.Paper.FilteredFlatTensorCohomology
import Sheaf.Paper.RestrictedCoefficientMateProjection

/-!
# Flat coefficient push comparison and its filtered cocone legs

Source: blueprint main-20261015, rational proper base change, paragraph (1),
localization and finite-extension colimits (blueprint: lem-sfb-coefficient-push-filtered-legs).

The projection arrows and the restricted scalar tensor presentation below are the
existing canonical constructions, including their tensor symmetry normalization.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint AlgebraicGeometry.ProEtale.upperStar

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open ModuleRingedComparison
  (internalModules internalDerivedPullback internalDerivedPushforward internalProjection
    comparisonSource)

variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]

/-- Exact scalar restriction with its two internal module categories exposed.
Its body is the recorded levelwise restriction functor, without any new data.
Source: Stacks 07A6; blueprint rational proper base change, paragraph (1)
(blueprint: lem-sfb-coefficient-push-filtered-legs). -/
def filteredCoefficientRestriction (Z : Scheme.{u}) :
    DerivedCategory (internalModules S Z) ⥤ DerivedCategory (internalModules R Z) :=
  (Mod.comap (coefficientMap a Z)).mapDerivedCategory

/-- Scalar extension with its internal module categories exposed. The body is
exactly the existing total left derived scalar extension.
Source: Stacks 07A6; blueprint rational proper base change, paragraph (1)
(blueprint: lem-sfb-coefficient-push-filtered-legs). -/
def filteredCoefficientExtension (Z : Scheme.{u}) :
    DerivedCategory (internalModules R Z) ⥤ DerivedCategory (internalModules S Z) :=
  (fun {T : DerivedCategory (internalModules R Z) ⥤
      DerivedCategory (internalModules S Z)}
    {U : DerivedCategory (internalModules S Z) ⥤ DerivedCategory (internalModules R Z)}
    (_adj : T ⊣ U) ↦ T)
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Z))

/-- The existing balanced derived scalar tensor presentation, with its category
endpoints exposed to avoid repeatedly inferring the derived restriction data.
The symmetric structure explicitly retains the existing named sheaf braiding;
its symmetry proof is the existing sheaf symmetry. This fixes structural data,
without choosing a new monoidal structure or any comparison map.
Source: Stacks 07A6; blueprint rational proper base change, paragraph (1)
(blueprint: lem-sfb-coefficient-push-filtered-legs). -/
def filteredCoefficientTensorIso (Z : Scheme.{u}) :
    filteredCoefficientExtension a Z ⋙ filteredCoefficientRestriction a Z ≅
      (derivedTensor R Z).flip.obj
        ((DerivedCategory.singleFunctor (internalModules R Z) 0).obj
          ((Mod.comap (coefficientMap a Z)).obj (Mod.regular (condensedRingObj S Z)))) := by
  let e := (QuotientChange.canonicalCoefficientTensorNormalization a Z).derived
  unfold QuotientChange.D at e
  -- The kernel checks the existing scalar-functor and tensor endpoint aliases.
  run_tac Lean.Elab.Tactic.withMainContext do
    let e ← Lean.Meta.getLocalDeclFromUserName `e
    (← Lean.Elab.Tactic.getMainGoal).assign e.toExpr
    Lean.Elab.Tactic.replaceMainGoal []

/-- The recorded restriction/pushforward comparison with its endpoints exposed.
Source: Stacks 07A6; blueprint rational proper base change, paragraph (1)
(blueprint: lem-sfb-coefficient-push-filtered-legs). -/
def filteredCoefficientRestrictPushIso
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    internalDerivedPushforward S f ⋙ filteredCoefficientRestriction a Y ≅
      filteredCoefficientRestriction a X ⋙ internalDerivedPushforward R f :=
  derivedComapLowerStarIso a f

/-- The recorded coefficient push mate with the four functor endpoints exposed.
This definition is exactly derivedPushHom, not an unspecified map.
Source: Stacks 07A6; blueprint rational proper base change, paragraph (1)
(blueprint: lem-sfb-coefficient-push-filtered-legs). -/
def filteredCoefficientPushHom
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    internalDerivedPushforward R f ⋙ filteredCoefficientExtension a Y ⟶
      filteredCoefficientExtension a X ⋙ internalDerivedPushforward S f :=
  derivedPushHom a f

/-- The existing restricted-regular pullback comparison, with its total derived
pullback endpoint exposed. No comparison is chosen: this is precisely
`residueRestrictedRegularPullIso`, constructed from exact pullback/single,
restriction/pullback and the ordinary regular-module unit.
Source: Stacks 07A4 and 07A6; blueprint rational proper base change, paragraph (1)
(blueprint: lem-sfb-coefficient-push-filtered-legs). -/
def filteredCoefficientPullIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (internalDerivedPullback R f).obj
        ((DerivedCategory.singleFunctor (internalModules R Y) 0).obj
          ((Mod.comap (coefficientMap a Y)).obj (Mod.regular (condensedRingObj S Y)))) ≅
      (DerivedCategory.singleFunctor (internalModules R X) 0).obj
        ((Mod.comap (coefficientMap a X)).obj (Mod.regular (condensedRingObj S X))) := by
  unfold internalDerivedPullback comparisonSource
  exact @id _ (by
    simpa only [residueExchangeUpperStar] using residueRestrictedRegularPullIso R S a f)

attribute [local irreducible] filteredCoefficientExtension filteredCoefficientRestriction
  filteredCoefficientTensorIso filteredCoefficientPullIso
  filteredCoefficientPushHom
  filteredCoefficientRestrictPushIso internalDerivedPullback internalDerivedPushforward
  internalProjection

set_option backward.isDefEq.respectTransparency false in
private theorem projection_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (internalModules R X))
    {M N : DerivedCategory (internalModules R Y)} (q : M ⟶ N) :
    ((derivedTensor R Y).obj ((internalDerivedPushforward R f).obj K)).map q ≫
        internalProjection R f K N =
      internalProjection R f K M ≫ (internalDerivedPushforward R f).map
        (((derivedTensor R X).obj K).map ((internalDerivedPullback R f).map q)) := by
  let adj : internalDerivedPullback R f ⊣ internalDerivedPushforward R f := by
    unfold internalDerivedPullback internalDerivedPushforward comparisonSource
    exact derivedUpperStarLowerStarAdjunction R f
  have h := ((adj.rightAdjointProjectionMap
    (ModuleRingedComparison.internalDelta R f)).app K).naturality q
  -- Avoid elaborating the sheaf tensor structure again; the kernel checks conversion.
  run_tac Lean.Elab.Tactic.withMainContext do
    let h ← Lean.Meta.getLocalDeclFromUserName `h
    (← Lean.Elab.Tactic.getMainGoal).assign h.toExpr
    Lean.Elab.Tactic.replaceMainGoal []

private theorem iso_at_cocone_vertex
    {C D : Type*} [Category C] [Category D] [Abelian D] [HasDerivedCategory D]
    {J : Type*} [Category J] {P : J ⥤ C} (c : Cocone P)
    (F G : C ⥤ DerivedCategory D) (t : F ⟶ G)
    (ht : ∀ i : J, IsIso (t.app (P.obj i)))
    (hc : ∀ q : ℤ,
      Nonempty (IsColimit ((F ⋙ DerivedCategory.homologyFunctor D q).mapCocone c)) ∧
      Nonempty (IsColimit ((G ⋙ DerivedCategory.homologyFunctor D q).mapCocone c))) :
    IsIso (t.app c.pt) := by
  rw [DerivedCategory.isIso_iff]
  intro q
  let H := DerivedCategory.homologyFunctor D q
  obtain ⟨⟨hs⟩, ⟨ht'⟩⟩ := hc q
  let (i : J) : IsIso (t.app (P.obj i)) := ht i
  let e : P ⋙ F ⋙ H ≅ P ⋙ G ⋙ H :=
    NatIso.ofComponents (fun i ↦ asIso (H.map (t.app (P.obj i)))) (by
      intro i j f
      simpa only [Functor.comp_map, asIso_hom, H.map_comp] using
        congrArg H.map (t.naturality (P.map f)))
  have he : H.map (t.app c.pt) = (hs.coconePointsIsoOfNatIso ht' e).hom := by
    apply hs.hom_ext
    intro i
    rw [IsColimit.comp_coconePointsIsoOfNatIso_hom]
    change H.map (F.map (c.ι.app i)) ≫ H.map (t.app c.pt) =
      H.map (t.app (P.obj i)) ≫ H.map (G.map (c.ι.app i))
    simpa only [Functor.map_comp, Functor.const_obj_obj] using
      congrArg H.map (t.naturality (c.ι.app i))
  rw [he]
  infer_instance

private theorem restriction_reflects_derived_iso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.ReflectsIsomorphisms] : F.mapDerivedCategory.ReflectsIsomorphisms := by
  refine ⟨fun g _ ↦ ?_⟩
  rw [DerivedCategory.isIso_iff]
  intro n
  have : IsIso (F.map ((DerivedCategory.homologyFunctor C n).map g)) :=
    (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso n) g).2
      (by change IsIso ((DerivedCategory.homologyFunctor D n).map
        (F.mapDerivedCategory.map g)); infer_instance)
  exact isIso_of_reflects_iso _ F

/-- A bounded filtered flat presentation detects the canonical flat coefficient
push comparison, and its cocone legs are the projection-formula legs.
Source: blueprint main-20261015, rational proper base change, paragraph (1);
Stacks 03DB, 03EP, 07A4, 07A6 and 0B56; Hemo--Richarz--Scholbach Lemma 5.3(1)
(blueprint: lem-sfb-coefficient-push-filtered-legs).

Proof. The canonical scalar-tensor presentation satisfies the computation
normalization, and its exact-single regular pullback comparison is the fixed
residue comparison. The restricted coefficient-mate theorem therefore identifies
the given push map with the projection at the cocone vertex, conjugated by the
specified tensor, restriction/pushforward and regular pullback isomorphisms.
The filtered flat tensor cohomology theorem supplies colimit cocones after each
homology functor on both sides of the projection. Naturality gives a map of
these cocones whose components are the assumed invertible stage projections.
The induced colimit isomorphism equals homology of the vertex projection by the
colimit uniqueness property. Homology detects its invertibility, and exact
restriction reflects derived isomorphisms. Finally projection naturality at each
v_i gives the displayed equality with the actual cocone legs. -/
theorem coefficientPush_isIso_of_filtered_flat_legs
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
    (ℓ p : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [CharP k p]
    (_hp : 0 < p) (_hne : p ≠ ℓ)
    {X Y : Over (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [QuasiCompact f.left] [QuasiSeparated f.left]
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
    (P : I ⥤ internalModules R Y.left)
    (_hP : ∀ i : I, ObjectProperty.flat (P.obj i))
    (_hfP : ∀ i : I, ObjectProperty.flat ((upperStar R f.left).obj (P.obj i)))
    (v : P ⟶ (Functor.const I).obj
      ((Mod.comap (coefficientMap a Y.left)).obj (Mod.regular (condensedRingObj S Y.left))))
    (_hv : IsColimit (Cocone.mk _ v))
    (K : DerivedCategory (internalModules R X.left)) (_hK : ∃ n : ℤ, K.IsGE n)
    (_hδ : ∀ i : I, IsIso (internalProjection R f.left K
      ((DerivedCategory.singleFunctor (internalModules R Y.left) 0).obj (P.obj i)))) :
    IsIso ((filteredCoefficientPushHom a f.left).app K) ∧
      ∀ i : I,
        ((derivedTensor R Y.left).obj ((internalDerivedPushforward R f.left).obj K)).map
            ((DerivedCategory.singleFunctor (internalModules R Y.left) 0).map (v.app i)) ≫
          (filteredCoefficientTensorIso a Y.left).inv.app
            ((internalDerivedPushforward R f.left).obj K) ≫
          (filteredCoefficientRestriction a Y.left).map
            ((filteredCoefficientPushHom a f.left).app K) ≫
          (filteredCoefficientRestrictPushIso a f.left).hom.app
            ((filteredCoefficientExtension a X.left).obj K) =
        internalProjection R f.left K
            ((DerivedCategory.singleFunctor (internalModules R Y.left) 0).obj (P.obj i)) ≫
          (internalDerivedPushforward R f.left).map
            (((derivedTensor R X.left).obj K).map
                ((internalDerivedPullback R f.left).map
                  ((DerivedCategory.singleFunctor (internalModules R Y.left) 0).map (v.app i))) ≫
              ((derivedTensor R X.left).obj K).map (filteredCoefficientPullIso a f.left).hom ≫
              (filteredCoefficientTensorIso a X.left).inv.app K) := by
  let : ∀ T : Scheme.{u},
      HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R T) := fun T ↦ by
    let : IsGrothendieckAbelian.{u + 1} (ModuleRingedComparison.modules R T) :=
      IsGrothendieckAbelian.of_equivalence (ModuleRingedComparison.equivalence R T)
    exact HasDerivedCategory.ofIsGrothendieckAbelian _
  let TX := QuotientChange.canonicalCoefficientTensorNormalization a X.left
  let TY := QuotientChange.canonicalCoefficientTensorNormalization a Y.left
  obtain ⟨hnorm, hpull⟩ :=
    QuotientChange.canonicalCoefficientTensorNormalization_normalized a
  have hmate := (RestrictedCoefficientMate.restricted_coefficient_mate_projection a
    ℓ p k _hp _hne f TX TY (hnorm X.left) (hnorm Y.left)).2.1 K
  have hcanonical :
      (filteredCoefficientTensorIso a Y.left).inv.app
          ((internalDerivedPushforward R f.left).obj K) ≫
        (filteredCoefficientRestriction a Y.left).map
          ((filteredCoefficientPushHom a f.left).app K) ≫
        (filteredCoefficientRestrictPushIso a f.left).hom.app
          ((filteredCoefficientExtension a X.left).obj K) =
      internalProjection R f.left K
          ((DerivedCategory.singleFunctor (internalModules R Y.left) 0).obj
            ((Mod.comap (coefficientMap a Y.left)).obj
              (Mod.regular (condensedRingObj S Y.left)))) ≫
        (internalDerivedPushforward R f.left).map
          (((derivedTensor R X.left).obj K).map (filteredCoefficientPullIso a f.left).hom ≫
            (filteredCoefficientTensorIso a X.left).inv.app K) := by
    have hh := hmate
    dsimp only [RestrictedCoefficientMate.restrictedMap] at hh
    rw [hpull] at hh
    have hh' :
        (filteredCoefficientTensorIso a Y.left).inv.app
            ((internalDerivedPushforward R f.left).obj K) ≫
          (filteredCoefficientRestriction a Y.left).map
            ((filteredCoefficientPushHom a f.left).app K) ≫
          (filteredCoefficientRestrictPushIso a f.left).hom.app
            ((filteredCoefficientExtension a X.left).obj K) ≫
          (internalDerivedPushforward R f.left).map
            ((filteredCoefficientTensorIso a X.left).hom.app K) =
        internalProjection R f.left K
            ((DerivedCategory.singleFunctor (internalModules R Y.left) 0).obj
              ((Mod.comap (coefficientMap a Y.left)).obj
                (Mod.regular (condensedRingObj S Y.left)))) ≫
          (internalDerivedPushforward R f.left).map
            (((derivedTensor R X.left).obj K).map
              (filteredCoefficientPullIso a f.left).hom) := by
      run_tac Lean.Elab.Tactic.withMainContext do
        let hh ← Lean.Meta.getLocalDeclFromUserName `hh
        (← Lean.Elab.Tactic.getMainGoal).assign hh.toExpr
        Lean.Elab.Tactic.replaceMainGoal []
    let e := (internalDerivedPushforward R f.left).mapIso
      ((filteredCoefficientTensorIso a X.left).app K)
    let r := (filteredCoefficientTensorIso a Y.left).inv.app
        ((internalDerivedPushforward R f.left).obj K) ≫
      (filteredCoefficientRestriction a Y.left).map
        ((filteredCoefficientPushHom a f.left).app K) ≫
      (filteredCoefficientRestrictPushIso a f.left).hom.app
        ((filteredCoefficientExtension a X.left).obj K)
    let s := internalProjection R f.left K
        ((DerivedCategory.singleFunctor (internalModules R Y.left) 0).obj
          ((Mod.comap (coefficientMap a Y.left)).obj
            (Mod.regular (condensedRingObj S Y.left)))) ≫
      (internalDerivedPushforward R f.left).map
        (((derivedTensor R X.left).obj K).map (filteredCoefficientPullIso a f.left).hom)
    have hh'' : r ≫ e.hom = s := by
      simpa only [r, s, e, Functor.mapIso_hom, Iso.app_hom, Category.assoc] using hh'
    have he := (Iso.eq_comp_inv e (f := s) (g := r)).2 hh''
    simpa only [r, s, e, Functor.mapIso_inv, Iso.app_inv, Functor.map_comp,
      Category.assoc] using he
  let A : internalModules R Y.left ⥤ DerivedCategory (internalModules R Y.left) :=
    DerivedCategory.singleFunctor _ 0 ⋙
      (derivedTensor R Y.left).obj ((internalDerivedPushforward R f.left).obj K)
  let B : internalModules R Y.left ⥤ DerivedCategory (internalModules R Y.left) :=
    DerivedCategory.singleFunctor _ 0 ⋙ internalDerivedPullback R f.left ⋙
      (derivedTensor R X.left).obj K ⋙ internalDerivedPushforward R f.left
  let t : A ⟶ B :=
    { app := fun M ↦ internalProjection R f.left K
        ((DerivedCategory.singleFunctor _ 0).obj M)
      naturality := fun M N q ↦ projection_naturality f.left K
        ((DerivedCategory.singleFunctor _ 0).map q) }
  have hproj : IsIso (t.app ((Cocone.mk _ v).pt)) :=
    iso_at_cocone_vertex (Cocone.mk _ v) A B t _hδ
      (filtered_flat_tensor_cohomology_cocones R ℓ p k _hp _hne f P
        (Cocone.mk _ v) _hv _hP _hfP K _hK)
  refine ⟨?_, ?_⟩
  · let := restriction_reflects_derived_iso
      (Mod.comap (D := Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
        (coefficientMap a Y.left))
    have : (filteredCoefficientRestriction a Y.left).ReflectsIsomorphisms := by
      unfold filteredCoefficientRestriction
      infer_instance
    have hi : IsIso
        ((filteredCoefficientTensorIso a Y.left).inv.app
            ((internalDerivedPushforward R f.left).obj K) ≫
          (filteredCoefficientRestriction a Y.left).map
            ((filteredCoefficientPushHom a f.left).app K) ≫
          (filteredCoefficientRestrictPushIso a f.left).hom.app
            ((filteredCoefficientExtension a X.left).obj K)) := by
      rw [hcanonical]
      infer_instance
    have hi' := IsIso.of_isIso_comp_left
      ((filteredCoefficientTensorIso a Y.left).inv.app
        ((internalDerivedPushforward R f.left).obj K))
      ((filteredCoefficientRestriction a Y.left).map
          ((filteredCoefficientPushHom a f.left).app K) ≫
        (filteredCoefficientRestrictPushIso a f.left).hom.app
          ((filteredCoefficientExtension a X.left).obj K))
    have : IsIso ((filteredCoefficientRestriction a Y.left).map
        ((filteredCoefficientPushHom a f.left).app K)) :=
      IsIso.of_isIso_comp_right _
        ((filteredCoefficientRestrictPushIso a f.left).hom.app
          ((filteredCoefficientExtension a X.left).obj K))
    exact isIso_of_reflects_iso _ (filteredCoefficientRestriction a Y.left)
  · intro i
    let q := (DerivedCategory.singleFunctor (internalModules R Y.left) 0).map (v.app i)
    let b := (internalDerivedPushforward R f.left).map
      (((derivedTensor R X.left).obj K).map (filteredCoefficientPullIso a f.left).hom ≫
        (filteredCoefficientTensorIso a X.left).inv.app K)
    have h := congrArg (fun z ↦ z ≫ b) (projection_naturality f.left K q)
    rw [hcanonical]
    simpa only [q, b, Functor.map_comp, Category.assoc,
      Functor.const_obj_obj, Functor.comp_obj] using h

end AlgebraicGeometry.ProEtale.CondensedRing
