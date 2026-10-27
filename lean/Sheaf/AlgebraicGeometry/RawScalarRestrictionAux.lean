/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CoherentHigherImageClasses
public import Sheaf.AlgebraicGeometry.RawPullbackNaturalityAux
public import Sheaf.AlgebraicGeometry.RawRestrictedClassNormalizationData
import Sheaf.AlgebraicGeometry.UnitStructureCoefficientIso
import WeilConjectures.ConstructibleSheaf.EtaleMorphismDescent

/-! # Local scalars and restriction before higher-image sheafification

Source: Stacks Project, Tags 03Q8 and 03DR.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false
attribute [local irreducible] affineRealizationRawEquiv coherentEtaleMap
  tensorPullback tensorPullbackObj coherentEtaleRestrictionIso
  Etale.sheafHDerivedEquiv Etale.sheafHToDerived CategoryTheory.derivedExtEvaluation
  Etale.rawRestrictedCohomologyComparison
  Etale.rawAffineComplexPullback
  Etale.upperStarComp Etale.upperStar Etale.cohomology
  Etale.rightDerivedGlobalSections tensorSectionsComp
attribute [local instance] Etale.RawRestrictedComparison.etaleComposition
  Etale.RawRestrictedComparison.etaleIdentities Etale.RawRestrictedComparison.etalePullbacks
  Etale.RawRestrictedComparison.etaleBaseChange Etale.RawRestrictedComparison.sheafifyInstance
  Etale.RawRestrictedComparison.weakSheafifyInstance

private theorem restriction_inv_coordinate {X Y : Scheme.{u}} (j : Y ⟶ X)
    [AlgebraicGeometry.Etale j] (G : X.Modules) [G.IsQuasicoherent]
    [(tensorPullback j).obj G |>.IsQuasicoherent] (T : Y.Etale)
    (x : (liftedCoherentEtaleSheaf ((tensorPullback j).obj G)).obj.obj (op T)) :
    (((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1}
      j inferInstance).hom.app (liftedCoherentEtaleSheaf G)).hom.app (op T))
        ((coherentEtaleRestrictionIso j G).inv.hom.app (op T) x) =
      ULift.up (((tensorSectionsComp T.hom j).hom.app G).app ⊤ x.down) := by
  let K := coherentEtaleRestrictionIso j G
  let ρ := (Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1}
    j inferInstance).app (liftedCoherentEtaleSheaf G)
  let p := (tensorSectionsComp T.hom j).app G
  let s := p.hom.app ⊤ x.down
  have hk : K.hom.hom.app (op T) (ρ.inv.hom.app (op T) (ULift.up s)) =
      ULift.up (p.inv.app ⊤ s) := by
    dsimp only [K]
    unfold coherentEtaleRestrictionIso
    exact (Classical.choose_spec (existsUnique_coherentEtaleRestrictionIso j G)).1 T s
  have hp : p.inv.app ⊤ s = x.down :=
    ConcreteCategory.congr_hom (congrArg (fun a ↦ a.app ⊤) p.hom_inv_id) x.down
  rw [hp] at hk
  have hki : K.inv.hom.app (op T) x = ρ.inv.hom.app (op T) (ULift.up s) := by
    have h := congrArg (fun y ↦ K.inv.hom.app (op T) y) hk
    have hc := congrArg (fun a ↦ a.hom.app (op T)
      (ρ.inv.hom.app (op T) (ULift.up s))) K.hom_inv_id
    change K.inv.hom.app (op T) (K.hom.hom.app (op T)
      (ρ.inv.hom.app (op T) (ULift.up s))) = _ at hc
    rw [hc] at h
    exact h.symm
  change ρ.hom.hom.app (op T) (K.inv.hom.app (op T) x) = _
  rw [hki]
  exact congrArg (fun a ↦ a.hom.app (op T) (ULift.up s)) ρ.inv_hom_id

/-- Scalar multiplication on an inverse-image coefficient, conjugated by the fixed
coherent restriction isomorphism. It is the displayed composite of actual maps.
Source: Stacks Project, Tag 03DR.
(blueprint: def-weil-pbc-restriction-scalar-endomorphism). -/
noncomputable def restrictionScalar {X Y : Scheme.{u}} (j : Y ⟶ X)
    [AlgebraicGeometry.Etale j] (G : X.Modules) [G.IsQuasicoherent]
    [(tensorPullback j).obj G |>.IsQuasicoherent] (r : Γ(Y, ⊤)) :
    (Etale.upperStar AddCommGrpCat.{u + 1} j).obj (liftedCoherentEtaleSheaf G) ⟶
      (Etale.upperStar AddCommGrpCat.{u + 1} j).obj (liftedCoherentEtaleSheaf G) :=
  (coherentEtaleRestrictionIso j G).hom ≫
    coherentEtaleMap _ _ (((tensorPullback j).obj G).smulHom r) ≫
      (coherentEtaleRestrictionIso j G).inv

private theorem restriction_scalar_coordinate {X Y : Scheme.{u}} (j : Y ⟶ X)
    [AlgebraicGeometry.Etale j] (G : X.Modules) [G.IsQuasicoherent]
    [(tensorPullback j).obj G |>.IsQuasicoherent] (r : Γ(Y, ⊤)) (T : Y.Etale)
    (x : ((Etale.upperStar AddCommGrpCat.{u + 1} j).obj
      (liftedCoherentEtaleSheaf G)).obj.obj (op T)) :
    let ρ := (Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1}
      j inferInstance).app (liftedCoherentEtaleSheaf G)
    ρ.hom.hom.app (op T) ((restrictionScalar j G r).hom.app (op T) x) =
      ULift.up (T.hom.appTop r •
        @id Γ((tensorPullback (T.hom ≫ j)).obj G, ⊤)
          (ρ.hom.hom.app (op T) x).down) := by
  dsimp only
  change (((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1}
      j inferInstance).hom.app (liftedCoherentEtaleSheaf G)).hom.app (op T))
    ((coherentEtaleRestrictionIso j G).inv.hom.app (op T)
      ((coherentEtaleMap _ _ (((tensorPullback j).obj G).smulHom r)).hom.app (op T)
        ((coherentEtaleRestrictionIso j G).hom.hom.app (op T) x))) = _
  rw [restriction_inv_coordinate, coherentEtaleMap_smulHom_app, Hom.app_smul]
  have hc := congrArg (fun a ↦ a.hom.app (op T) x)
    (coherentEtaleRestrictionIso j G).hom_inv_id
  change (coherentEtaleRestrictionIso j G).inv.hom.app (op T)
    ((coherentEtaleRestrictionIso j G).hom.hom.app (op T) x) = x at hc
  have h := restriction_inv_coordinate j G T
    ((coherentEtaleRestrictionIso j G).hom.hom.app (op T) x)
  rw [hc] at h
  apply ULift.ext
  exact congrArg (fun y ↦ T.hom.appTop r •
    @id Γ((tensorPullback (T.hom ≫ j)).obj G, ⊤) y.down) h.symm

private theorem lifted_restriction_map {X : Scheme.{u}} (G : X.Modules)
    [G.IsQuasicoherent] {U V : X.Etale} (p : V ⟶ U) :
    (liftedCoherentEtaleSheaf G).obj.map p.op =
      AddCommGrpCat.uliftFunctor.{u + 1, u}.map (etaleTensorSectionsRestriction G p) := by
  rfl

private theorem ulift_smul_apply {Y : Scheme.{u}} (M : Y.Modules)
    (r : Γ(Y, ⊤)) (x : ULift.{u + 1} Γ(M, ⊤)) :
    (AddCommGrpCat.uliftFunctor.{u + 1, u}.map (M.smul r)) x =
      ULift.up (r • x.down) := by rfl

private theorem lifted_restriction_smul_map {X : Scheme.{u}} (G : X.Modules)
    [G.IsQuasicoherent] {U V : X.Etale} (p : V ⟶ U) (r : Γ(U.left, ⊤)) :
    AddCommGrpCat.uliftFunctor.{u + 1, u}.map
      (((tensorPullback U.hom).obj G).smul r) ≫
        (liftedCoherentEtaleSheaf G).obj.map p.op =
      (liftedCoherentEtaleSheaf G).obj.map p.op ≫
        AddCommGrpCat.uliftFunctor.{u + 1, u}.map
          (((tensorPullback V.hom).obj G).smul (p.left.appTop r)) := by
  rw [lifted_restriction_map, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg AddCommGrpCat.uliftFunctor.map (etaleTensorSectionsRestriction_smul G p r)

private theorem restriction_scalar_map {X Y : Scheme.{u}} (j : Y ⟶ X)
    [AlgebraicGeometry.Etale j] (G : X.Modules) [G.IsQuasicoherent]
    [(tensorPullback j).obj G |>.IsQuasicoherent] (r : Γ(Y, ⊤)) (T : Y.Etale) :
    (restrictionScalar j G r).hom.app (op T) ≫
      (((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1}
        j inferInstance).app (liftedCoherentEtaleSheaf G)).hom.hom.app (op T)) =
    (((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1}
        j inferInstance).app (liftedCoherentEtaleSheaf G)).hom.hom.app (op T)) ≫
      AddCommGrpCat.uliftFunctor.{u + 1, u}.map
        (((tensorPullback (T.hom ≫ j)).obj G).smul (T.hom.appTop r)) := by
  apply ConcreteCategory.hom_ext
  intro x
  change (((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1}
    j inferInstance).app (liftedCoherentEtaleSheaf G)).hom.hom.app (op T))
      ((restrictionScalar j G r).hom.app (op T) x) =
    AddCommGrpCat.uliftFunctor.map
      (((tensorPullback (T.hom ≫ j)).obj G).smul (T.hom.appTop r)) _
  exact (restriction_scalar_coordinate j G r T x).trans
    (ulift_smul_apply _ _ _).symm

/-- The normalized coherent coefficient scalar commutes with inverse-image composition.
Source: Stacks Project, Descent Tag 03DR and Etale Cohomology Tag 03Q8.
(blueprint: lem-weil-pbc-coherent-restricted-scalar-composition).
Proof: identify each etale inverse image with localization restriction. The chosen
coherent restriction isomorphism has component the inverse tensor-composition
isomorphism. Conjugating multiplication through it is multiplication by the scalar
restricted to each etale test scheme, since tensor-composition maps are module-linear.
The comparison of inverse-image composition with localization restriction composition
is upperStarIsoLocalizationRestriction_comp. Its localization component restricts
along the mapComp isomorphism of test objects, whose underlying scheme map is the
identity. The semilinearity equation etaleTensorSectionsRestriction_smul therefore
identifies the two scalar endomorphisms. Cancel the localization and composition
isomorphisms. All equalities also hold for zero modules, empty schemes, identity
morphisms, and the zero or unit scalar. This is a sheaf-level coefficient assertion;
it contains neither raw higher-image classes nor any cohomological degree. -/
theorem restrictionScalar_comp_aux {X Y Z : Scheme.{u}} (j : Y ⟶ X)
    (b : Z ⟶ Y) (k : Z ⟶ X) (hk : k = b ≫ j)
    [AlgebraicGeometry.Etale j] [AlgebraicGeometry.Etale b] [AlgebraicGeometry.Etale k]
    (G : X.Modules) [G.IsQuasicoherent]
    [(tensorPullback j).obj G |>.IsQuasicoherent]
    [(tensorPullback k).obj G |>.IsQuasicoherent] (r : Γ(Y, ⊤)) :
    (Etale.upperStar AddCommGrpCat.{u + 1} b).map (restrictionScalar j G r) ≫
        (Etale.upperStarComp AddCommGrpCat.{u + 1} b j k hk).inv.app
          (liftedCoherentEtaleSheaf G) =
      (Etale.upperStarComp AddCommGrpCat.{u + 1} b j k hk).inv.app
          (liftedCoherentEtaleSheaf G) ≫ restrictionScalar k G (b.appTop r) := by
  let F := liftedCoherentEtaleSheaf G
  let L := Etale.upperStar AddCommGrpCat.{u + 1} b
  let R := Etale.localizationRestriction AddCommGrpCat.{u + 1} b inferInstance
  let ρj := (Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1}
    j inferInstance).app F
  let ρk := (Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1}
    k inferInstance).app F
  let c := (Etale.upperStarComp AddCommGrpCat.{u + 1} b j k hk).app F
  let d := (Etale.localizationRestrictionComp' AddCommGrpCat.{u + 1} b j k hk).app F
  let e := (Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1}
    b inferInstance).app ((Etale.upperStar AddCommGrpCat.{u + 1} j).obj F)
  have hc : ρk.hom ≫ d.hom = c.hom ≫ e.hom ≫ R.map ρj.hom := by
    have h := Etale.upperStarIsoLocalizationRestriction_comp
      AddCommGrpCat.{u + 1} b j k hk F
    have hn := (Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1}
      b inferInstance).hom.naturality ρj.hom
    exact h.trans (congrArg (fun a ↦ c.hom ≫ a) hn)
  have hc' : c.inv ≫ ρk.hom ≫ d.hom = e.hom ≫ R.map ρj.hom := by
    rw [hc, Iso.inv_hom_id_assoc]
  have hs : R.map (restrictionScalar j G r) ≫ R.map ρj.hom =
      R.map ρj.hom ≫ d.inv ≫ ρk.inv ≫ restrictionScalar k G (b.appTop r) ≫
        ρk.hom ≫ d.hom := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext T
    induction T using Opposite.rec
    rename_i T
    let U : Y.Etale :=
      (MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale b)).obj T
    let α := ρj.hom.hom.app (op U)
    let β := ρk.hom.hom.app (op T)
    let δ := d.hom.hom.app (op T)
    let δi := d.inv.hom.app (op T)
    let βi := ρk.inv.hom.app (op T)
    let m := AddCommGrpCat.uliftFunctor.{u + 1, u}.map
      (((tensorPullback (U.hom ≫ j)).obj G).smul (U.hom.appTop r))
    let n := AddCommGrpCat.uliftFunctor.{u + 1, u}.map
      (((tensorPullback (T.hom ≫ k)).obj G).smul (T.hom.appTop (b.appTop r)))
    have hj : (restrictionScalar j G r).hom.app (op U) ≫ α = α ≫ m :=
      restriction_scalar_map j G r U
    have hk' : (restrictionScalar k G (b.appTop r)).hom.app (op T) ≫ β = β ≫ n :=
      restriction_scalar_map k G (b.appTop r) T
    have hd : n ≫ δ = δ ≫ m := by
      let pp := (MorphismProperty.Over.mapComp (Q := ⊤) (P := @AlgebraicGeometry.Etale)
        (hf := inferInstance) (hg := inferInstance) k hk).inv.app T
      have hp := lifted_restriction_smul_map G pp (T.hom.appTop (b.appTop r))
      dsimp only [δ, d, Iso.app_hom]
      rw [Etale.localizationRestrictionComp'_hom_app_hom_app]
      have hrU : U.hom.appTop r = T.hom.appTop (b.appTop r) := by
        change (T.hom ≫ b).appTop r = _
        rw [Scheme.Hom.comp_appTop]
        rfl
      dsimp only [m, n]
      rw [hrU]
      have hid : pp.left.appTop (T.hom.appTop (b.appTop r)) =
          T.hom.appTop (b.appTop r) := by
        have hpLeft : pp.left = 𝟙 T.left := rfl
        rw [hpLeft, Scheme.Hom.id_appTop]
        rfl
      rw [hid] at hp
      exact hp
    have hβ : βi ≫ β = 𝟙 _ :=
      congrArg (fun a ↦ a.hom.app (op T)) ρk.inv_hom_id
    have hδ : δi ≫ δ = 𝟙 _ :=
      congrArg (fun a ↦ a.hom.app (op T)) d.inv_hom_id
    change (restrictionScalar j G r).hom.app (op U) ≫ α =
      α ≫ δi ≫ βi ≫ (restrictionScalar k G (b.appTop r)).hom.app (op T) ≫ β ≫ δ
    rw [hj]
    symm
    calc
      _ = α ≫ δi ≫ βi ≫
          ((restrictionScalar k G (b.appTop r)).hom.app (op T) ≫ β) ≫ δ := by
        simp only [Category.assoc]
      _ = α ≫ δi ≫ βi ≫ (β ≫ n) ≫ δ := by rw [hk']
      _ = α ≫ δi ≫ n ≫ δ := by simp only [← Category.assoc, hβ, Category.comp_id]
      _ = α ≫ δi ≫ (n ≫ δ) := rfl
      _ = α ≫ m := by
        rw [hd]
        have hid : α ≫ δi ≫ δ = α := by
          rw [hδ]
          change α ≫ 𝟙 _ = α
          exact Category.comp_id α
        simpa only [← Category.assoc] using congrArg (fun a ↦ a ≫ m) hid
  have hn : L.map (restrictionScalar j G r) ≫ e.hom =
      e.hom ≫ R.map (restrictionScalar j G r) :=
    (Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1}
      b inferInstance).hom.naturality (restrictionScalar j G r)
  apply (cancel_mono (ρk.hom ≫ d.hom)).mp
  change (L.map (restrictionScalar j G r) ≫ c.inv) ≫ (ρk.hom ≫ d.hom) =
    (c.inv ≫ restrictionScalar k G (b.appTop r)) ≫ (ρk.hom ≫ d.hom)
  calc
    _ = L.map (restrictionScalar j G r) ≫ e.hom ≫ R.map ρj.hom := by
      simpa only [Category.assoc] using
        congrArg (fun a ↦ L.map (restrictionScalar j G r) ≫ a) hc'
    _ = e.hom ≫ (R.map (restrictionScalar j G r) ≫ R.map ρj.hom) := by
      rw [← Category.assoc, hn, Category.assoc]
    _ = e.hom ≫ R.map ρj.hom ≫ d.inv ≫ ρk.inv ≫
        restrictionScalar k G (b.appTop r) ≫ ρk.hom ≫ d.hom := by rw [hs]
    _ = _ := by
      have h := congrArg (fun a ↦ a ≫ d.inv ≫ ρk.inv ≫
        restrictionScalar k G (b.appTop r) ≫ ρk.hom ≫ d.hom) hc'.symm
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h

/-- Cohomology of a specified endomorphism of the coefficient on a chart.
Source: Stacks Project, Tags 03Q8 and 0EZM.
(blueprint: def-weil-pbc-normalization-cohomology-square).
Apply the single-complex functor, Q, and degree-q cohomology. The named raw chart
object retains the endpoint without computing the derived cohomology carrier. -/
@[irreducible] noncomputable def normalizationCohomologyAction
    {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (V : S.Etale)
    (ν : End ((Etale.upperStar AddCommGrpCat.{u + 1} (pullback.snd V.hom f)).obj F)) :
    Etale.rawAffineRestrictedCohomology f q F V ⟶
      Etale.rawAffineRestrictedCohomology f q F V :=
  (Etale.cohomology AddCommGrpCat.{u + 1} (Limits.pullback V.hom f) (q : ℤ)).map
    (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map ν))

/-- Formula for the named chart cohomology action.
Source: Stacks Project, Tag 03Q8.
(blueprint: def-weil-pbc-normalization-cohomology-square).
Proof: unfold the explicitly constructed action. -/
theorem normalizationCohomologyAction_formula
    {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (V : S.Etale)
    (ν : End ((Etale.upperStar AddCommGrpCat.{u + 1} (pullback.snd V.hom f)).obj F)) :
    normalizationCohomologyAction f q F V ν =
      (Etale.cohomology AddCommGrpCat.{u + 1} (Limits.pullback V.hom f) (q : ℤ)).map
        (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map ν)) := by
  unfold normalizationCohomologyAction
  rfl

attribute [local semireducible] normalizationCohomologyAction

/-- The coefficient square, with the prescribed raw chart groups as endpoints.
Source: Stacks Project, Tags 03Q8 and 0EZM.
(blueprint: def-weil-pbc-normalization-cohomology-square).
Construct the maps from the specified cohomology actions and normalization
restriction. Their commutation is single-complex coefficient naturality, since
normalization restriction is the raw complex pullback followed by the inverse-image
composition comparison. This retains the named chart endpoints in the interface. -/
@[irreducible] noncomputable def normalizationCohomologySquare
    {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {V V' : S.Etale} (h : V' ⟶ V)
    (ν : End ((Etale.upperStar AddCommGrpCat.{u + 1} (pullback.snd V.hom f)).obj F))
    (ν' : End ((Etale.upperStar AddCommGrpCat.{u + 1} (pullback.snd V'.hom f)).obj F))
    (hν : (Etale.upperStar AddCommGrpCat.{u + 1}
        (Etale.normalizationChartMap f h)).map ν ≫
      (Etale.upperStarComp AddCommGrpCat.{u + 1} (Etale.normalizationChartMap f h)
        (pullback.snd V.hom f) (pullback.snd V'.hom f)
        (MorphismProperty.Over.w
          ((MorphismProperty.Over.pullback @Etale ⊤ f).map h)).symm).inv.app F =
      (Etale.upperStarComp AddCommGrpCat.{u + 1} (Etale.normalizationChartMap f h)
        (pullback.snd V.hom f) (pullback.snd V'.hom f)
        (MorphismProperty.Over.w
          ((MorphismProperty.Over.pullback @Etale ⊤ f).map h)).symm).inv.app F ≫ ν') :
    CohomologySquareData (Etale.normalizationCohomologyRestriction f q F h)
      (normalizationCohomologyAction f q F V ν)
      (normalizationCohomologyAction f q F V' ν') :=
  coefficientCohomologySquare
    (CochainComplex.singleFunctor _ 0) (CochainComplex.singleFunctor _ 0)
    (Etale.upperStar AddCommGrpCat.{u + 1} (Etale.normalizationChartMap f h))
    ((Etale.upperStar AddCommGrpCat.{u + 1}
      (Etale.normalizationChartMap f h)).mapHomologicalComplex (.up ℤ))
    (DerivedCategory.Q ⋙ Etale.cohomology AddCommGrpCat.{u + 1}
      (Limits.pullback V.hom f) (q : ℤ))
    (DerivedCategory.Q ⋙ Etale.cohomology AddCommGrpCat.{u + 1}
      (Limits.pullback V'.hom f) (q : ℤ))
    (complexCohomologyPullbackTransformation (Etale.normalizationChartMap f h) q)
    ((Etale.upperStar AddCommGrpCat.{u + 1}
      (Etale.normalizationChartMap f h)).mapCochainComplexSingleFunctor 0).hom
    _ ν ν' _
    (complexCohomologyPullbackTransformation_app (Etale.normalizationChartMap f h) q _) hν

end AlgebraicGeometry.Scheme.Modules
