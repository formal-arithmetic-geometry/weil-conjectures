/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Sheaf.Paper.CechComplexAugmentations
public import Sheaf.Paper.CechRefinementCochainMap
import Sheaf.Paper.CechPushforwardTupleTotal

/-! # Tuplewise refinement of the pushed-forward target resolution

Source: Stacks Project, Tag 01FD, the right upper square and augmentation pentagon.
(blueprint: lem-sc-cech-refinement-pushforward-total)
-/

@[expose] public section

universe v
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

attribute [local irreducible] tensorPullback tensorPullbackObj
attribute [local instance 2000]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf

/-- The adjunction unit followed by the pushed-forward resolution augmentation.
Source: Stacks 01FD (blueprint: lem-sc-cech-refinement-pushforward-total). -/
def cechPushforwardAugmentation {X X' : Scheme.{v}} (f : X' ⟶ X)
    (F : X.Modules) (I : InjectiveResolution ((tensorPullback f).obj F)) :
    F ⟶ (pushforward f).obj (I.cocomplex.X 0) :=
  ((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app F) ≫
    (pushforward f).map (I.ι.f 0)

/-- The pushed-forward augmentation is a cocycle.
Source: Stacks 01FD (blueprint: lem-sc-cech-refinement-pushforward-total). -/
theorem cechPushforwardAugmentation_d {X X' : Scheme.{v}} (f : X' ⟶ X)
    (F : X.Modules) (I : InjectiveResolution ((tensorPullback f).obj F)) :
    cechPushforwardAugmentation f F I ≫ (pushforward f).map (I.cocomplex.d 0 1) = 0 := by
  dsimp only [cechPushforwardAugmentation]
  rw [Category.assoc, ← Functor.map_comp]
  have h : I.ι.f 0 ≫ I.cocomplex.d 0 1 = 0 := by simp
  rw [h, Functor.map_zero, comp_zero]

set_option backward.isDefEq.respectTransparency false in
private theorem moduleCechZero_tuple {X : Scheme.{v}} {ι : Type v}
    (U : ι → X.Opens) (G : X.Modules)
    (x : (RingedSpace.globalSectionsFunctor X.toRingedSpace).obj G)
    (y : Fin 1 → ι) :
    TopCat.Presheaf.cechComplexFunctorXAddEquiv U G.presheafModuleCat 0
      (moduleCechZero U G x) y =
    G.presheaf.map (homOfLE (le_top (a := ⨅ j, U (y j)))).op x := by
  rw [TopCat.Presheaf.cechComplexFunctorXAddEquiv_apply]
  have h : moduleCechZero U G ≫
      TopCat.Presheaf.cechComplexFunctorπ U G.presheafModuleCat 0 y =
    (ModuleCat.restrictScalarsId'App _ (moduleCech_top_restriction X)
      (G.val.obj (op ⊤))).inv ≫
      G.presheafModuleCat.map (homOfLE (le_top (a := ∏ᶜ fun l ↦ U (y l)))).op := by
    dsimp [moduleCechZero, TopCat.Presheaf.cechComplexFunctorπ]
    erw [Category.assoc, Pi.lift_π]
  erw [← ConcreteCategory.comp_apply (moduleCechZero U G), h,
    ConcreteCategory.comp_apply]
  change G.presheaf.map _ (G.presheaf.map _ x) = G.presheaf.map _ x
  rw [← ConcreteCategory.comp_apply, ← G.presheaf.map_comp]
  congr 2

set_option backward.isDefEq.respectTransparency false in
private theorem cechPushforwardTupleMap_zero {X X' : Scheme.{v}} (f : X' ⟶ X)
    {ι ι' : Type v} (U : ι → X.Opens) (U' : ι' → X'.Opens)
    (refine : ι' → ι) (hrefine : ∀ i, U' i ≤ f ⁻¹ᵁ U (refine i))
    (G : X'.Modules) :
    (forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v}).map
        (moduleCechZero U ((pushforward f).obj G)) ≫
      cechPushforwardTupleMap f U U' refine hrefine G 0 =
    G.presheaf.map
        (eqToHom (by simp) : (⊤ : X'.Opens) ⟶ f ⁻¹ᵁ (⊤ : X.Opens)).op ≫
      (forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat.{v}).map
        (moduleCechZero U' G) := by
  apply AddCommGrpCat.ext
  intro x
  apply (TopCat.Presheaf.cechComplexFunctorXAddEquiv U' G.presheafModuleCat 0).injective
  funext y
  change TopCat.Presheaf.cechComplexFunctorXAddEquiv U' G.presheafModuleCat 0
      (cechPushforwardTupleMap f U U' refine hrefine G 0
        (moduleCechZero U ((pushforward f).obj G) x)) y =
    TopCat.Presheaf.cechComplexFunctorXAddEquiv U' G.presheafModuleCat 0
      (moduleCechZero U' G (G.presheaf.map _ x)) y
  rw [cechPushforwardTupleMap_apply, moduleCechZero_tuple, moduleCechZero_tuple]
  change G.presheaf.map _ (G.presheaf.map _ x) =
    G.presheaf.map _ (G.presheaf.map _ x)
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← G.presheaf.map_comp, ← G.presheaf.map_comp]
  congr 2

/-- Naturality of forgetting-scalars homology transports a cochain square. -/
private theorem forgotten_homology_square {R R' : Type v} [Ring R] [Ring R']
    {A B : CochainComplex (ModuleCat.{v} R) ℕ}
    {A' B' : CochainComplex (ModuleCat.{v} R') ℕ}
    (u : A ⟶ B) (u' : A' ⟶ B')
    (g : ((forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj A ⟶
      ((forget₂ (ModuleCat.{v} R') AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj A')
    (t : ((forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj B ⟶
      ((forget₂ (ModuleCat.{v} R') AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj B')
    (h : ((forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).map u ≫ t =
      g ≫ ((forget₂ (ModuleCat.{v} R') AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).map u') (p : ℕ) :
    let e := forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}
    let e' := forget₂ (ModuleCat.{v} R') AddCommGrpCat.{v}
    e.map (HomologicalComplex.homologyMap u p) ≫
        ((B.sc p).mapHomologyIso e).inv ≫ HomologicalComplex.homologyMap t p ≫
          ((B'.sc p).mapHomologyIso e').hom =
      ((A.sc p).mapHomologyIso e).inv ≫ HomologicalComplex.homologyMap g p ≫
        ((A'.sc p).mapHomologyIso e').hom ≫
          e'.map (HomologicalComplex.homologyMap u' p) := by
  let e := forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}
  let e' := forget₂ (ModuleCat.{v} R') AddCommGrpCat.{v}
  have hp := congrArg (fun k ↦ HomologicalComplex.homologyMap k p) h
  simp only [HomologicalComplex.homologyMap_comp] at hp
  have hl := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ p).map u) e
  have hr := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ p).map u') e'
  change e.map (HomologicalComplex.homologyMap u p) ≫ ((B.sc p).mapHomologyIso e).inv =
    ((A.sc p).mapHomologyIso e).inv ≫ HomologicalComplex.homologyMap
      ((e.mapHomologicalComplex (ComplexShape.up ℕ)).map u) p at hl
  change HomologicalComplex.homologyMap
      ((e'.mapHomologicalComplex (ComplexShape.up ℕ)).map u') p ≫
        ((B'.sc p).mapHomologyIso e').hom =
    ((A'.sc p).mapHomologyIso e').hom ≫
      e'.map (HomologicalComplex.homologyMap u' p) at hr
  calc
    _ = ((A.sc p).mapHomologyIso e).inv ≫
        HomologicalComplex.homologyMap
          ((e.mapHomologicalComplex (ComplexShape.up ℕ)).map u) p ≫
        HomologicalComplex.homologyMap t p ≫ ((B'.sc p).mapHomologyIso e').hom := by
      simpa only [Category.assoc] using
        congrArg (fun k ↦ k ≫ HomologicalComplex.homologyMap t p ≫
          ((B'.sc p).mapHomologyIso e').hom) hl
    _ = ((A.sc p).mapHomologyIso e).inv ≫ HomologicalComplex.homologyMap g p ≫
        HomologicalComplex.homologyMap
          ((e'.mapHomologicalComplex (ComplexShape.up ℕ)).map u') p ≫
        ((B'.sc p).mapHomologyIso e').hom := by
      rw [← Category.assoc (HomologicalComplex.homologyMap _ p), hp, Category.assoc]
    _ = _ := by rw [hr]

set_option maxHeartbeats 500000 in
-- The component and homology transports cross two coefficient rings.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Tuple restriction on the pushed-forward resolution preserves both augmentations.
This statement involves only the target resolution: there is no source resolution,
resolution lift, injective replacement, covering assumption, or inverse total map.
Source: Stacks Project, Tag 01FD, the map B-double-prime to A in the displayed diagram.
(blueprint: lem-sc-cech-refinement-pushforward-total)

Proof: In bidegree (r,q), send a tuple section of f_*I^r to its component indexed
by refine composed with the target tuple, then restrict it to the target intersection.
Pushforward evaluates on the inverse-image open, so this is a section of I^r on the
required intersection. Restrictions commute with I's differential and with all face
maps. The alternating face sums and the total signs are therefore preserved, giving
a cochain map between the forgotten module total complexes. Apply homology and
transport the two ends through the canonical forgetful homology isomorphisms to
obtain s. On the alpha summands (r,0), restrictions of global sections commute with
this map. The given component formula for a.inv identifies the source global
sections with those on X', proving the first equality. On beta summands (0,q),
naturality of I's augmentation moves it past the restrictions. The remaining tuple
formula is hgamma, proving the second equality. This needs no cover on either side;
empty families give zero tuple products, and the same formulas apply in degree zero.
-/
theorem exists_cechRefinement_pushforward_total
    {X X' : Scheme.{v}} (f : X' ⟶ X) {ι ι' : Type v}
    (U : ι → X.Opens) (U' : ι' → X'.Opens)
    (refine : ι' → ι) (hrefine : ∀ i, U' i ≤ f ⁻¹ᵁ U (refine i))
    (F : X.Modules) (I : InjectiveResolution ((tensorPullback f).obj F)) (p : ℕ)
    (gamma : ((forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor U).obj F.presheafModuleCat) ⟶
      ((forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          ((cechComplexFunctor U').obj ((tensorPullback f).obj F).presheafModuleCat))
    (hgamma : IsCechRefinementMap f U U' refine hrefine F gamma)
    (a : ((RingedSpace.globalSectionsFunctor X'.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{v}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          I.cocomplex ≅
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{v}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex))
    (ha : ∀ n : ℕ, a.inv.f n = (Scheme.Modules.presheaf (I.cocomplex.X n)).map
      (eqToHom (by simp) : (⊤ : X'.Opens) ⟶ f ⁻¹ᵁ (⊤ : X.Opens)).op) :
    let P := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let e := forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v}
    let e' := forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat.{v}
    let S := (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)
    ∃ s : e.obj (((moduleCechTotalFunctor U).obj P).homology p) ⟶
        e'.obj (((moduleCechDouble U' I).total (ComplexShape.up ℕ)).homology p),
      e.map (HomologicalComplex.homologyMap (moduleCechComplexAlpha U P) p) ≫ s =
        (((S.obj P).sc p).mapHomologyIso e).inv ≫
          HomologicalComplex.homologyMap a.inv p ≫
          (((RingedSpace.globalSectionsComplex I).sc p).mapHomologyIso e').hom ≫
          e'.map (HomologicalComplex.homologyMap (moduleCechAlpha U' I) p) ∧
      e.map (HomologicalComplex.homologyMap
          (moduleCechComplexBeta U P (cechPushforwardAugmentation f F I)
            (cechPushforwardAugmentation_d f F I)) p) ≫ s =
        cechRefinementHomology gamma p ≫
          e'.map (HomologicalComplex.homologyMap (moduleCechBeta U' I) p) := by
  let P := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let e := forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v}
  let e' := forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat.{v}
  let S := (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
    (ComplexShape.up ℕ)
  obtain ⟨t, ht, _⟩ := exists_unique_cechPushforward_tuple_total
    f U U' refine hrefine I.cocomplex
  have coeff_apply : ∀ {X : Scheme.{v}} {ι : Type v}
      (U : ι → X.Opens) {F H : X.Modules} (φ : F ⟶ H) (n : ℕ)
      (a : ((cechComplexFunctor U).obj F.presheafModuleCat).X n)
      (y : Fin (n + 1) → ι),
      TopCat.Presheaf.cechComplexFunctorXAddEquiv U H.presheafModuleCat n
          (((cechComplexFunctor U).map
            ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
              φ.val)).f n a) y =
        φ.val.app (op (⨅ j, U (y j)))
          (TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat n a y) := by
    intro X ι U F H φ n a y
    let ψ := (PresheafOfModules.forgetToPresheafModuleCat
      (op ⊤) isTerminalTop.op).map φ.val
    have hπ := TopCat.Presheaf.cechComplexFunctor_map_f_π U F.presheafModuleCat ψ n y
    have hπa := congrArg (fun k ↦ k a) hπ
    change TopCat.Presheaf.cechComplexFunctorπ U H.presheafModuleCat n y
      (((cechComplexFunctor U).map ψ).f n a) =
      ψ.app _ (TopCat.Presheaf.cechComplexFunctorπ U F.presheafModuleCat n y a) at hπa
    change H.presheaf.map _
      (TopCat.Presheaf.cechComplexFunctorπ U H.presheafModuleCat n y
        (((cechComplexFunctor U).map ψ).f n a)) = _
    rw [hπa]
    exact (PresheafOfModules.naturality_apply φ.val
      (homOfLE (TopCat.Presheaf.iInf_le_piObj U y)).op
      (TopCat.Presheaf.cechComplexFunctorπ U F.presheafModuleCat n y a)).symm
  have hα : (e.mapHomologicalComplex (ComplexShape.up ℕ)).map
        (moduleCechComplexAlpha U P) ≫ t =
      a.inv ≫ (e'.mapHomologicalComplex (ComplexShape.up ℕ)).map
        (moduleCechAlpha U' I) := by
    apply HomologicalComplex.Hom.ext
    funext n
    change e.map (moduleCechZero U (P.X n) ≫ _) ≫ t.f n =
      a.inv.f n ≫ e'.map (moduleCechZero U' (I.cocomplex.X n) ≫ _)
    rw [e.map_comp, Category.assoc, ht n 0 n (by simp)]
    rw [e'.map_comp, ha n]
    have hz := cechPushforwardTupleMap_zero f U U' refine hrefine (I.cocomplex.X n)
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k ↦ k ≫ e'.map
        ((moduleCechDouble U' I).ιTotal (ComplexShape.up ℕ) n 0 n (by simp))) hz).trans
        (Category.assoc _ _ _))
  have hβ : (e.mapHomologicalComplex (ComplexShape.up ℕ)).map
        (moduleCechComplexBeta U P (cechPushforwardAugmentation f F I)
          (cechPushforwardAugmentation_d f F I)) ≫ t =
      gamma ≫ (e'.mapHomologicalComplex (ComplexShape.up ℕ)).map
        (moduleCechBeta U' I) := by
    apply HomologicalComplex.Hom.ext
    funext n
    change e.map (_ ≫ _) ≫ t.f n = gamma.f n ≫ e'.map (_ ≫ _)
    rw [e.map_comp, Category.assoc, ht 0 n n (by simp), e'.map_comp]
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    apply AddCommGrpCat.ext
    intro x
    apply (TopCat.Presheaf.cechComplexFunctorXAddEquiv U'
      (I.cocomplex.X 0).presheafModuleCat n).injective
    funext y
    change TopCat.Presheaf.cechComplexFunctorXAddEquiv U'
        (I.cocomplex.X 0).presheafModuleCat n
        (cechPushforwardTupleMap f U U' refine hrefine (I.cocomplex.X 0) n
          (((cechComplexFunctor U).map
            ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
              (cechPushforwardAugmentation f F I).val)).f n x)) y =
      TopCat.Presheaf.cechComplexFunctorXAddEquiv U'
        (I.cocomplex.X 0).presheafModuleCat n
        (((cechComplexFunctor U').map
          ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            (I.ι.f 0).val)).f n (gamma.f n x)) y
    rw [cechPushforwardTupleMap_apply, coeff_apply,
      coeff_apply]
    erw [hgamma n x y]
    dsimp only [cechPushforwardAugmentation, Hom.comp_app, pushforward_map_app]
    exact (PresheafOfModules.naturality_apply (I.ι.f 0).val
      (cechRefinementIntersection f U U' refine hrefine n y).op _).symm
  let TP := (moduleCechTotalFunctor U).obj P
  let TI := (moduleCechDouble U' I).total (ComplexShape.up ℕ)
  refine ⟨((TP.sc p).mapHomologyIso e).inv ≫
    HomologicalComplex.homologyMap t p ≫ ((TI.sc p).mapHomologyIso e').hom, ?_, ?_⟩
  · exact forgotten_homology_square
      (A := S.obj P) (B := TP) (A' := RingedSpace.globalSectionsComplex I) (B' := TI)
      (moduleCechComplexAlpha U P)
      (moduleCechAlpha U' I) a.inv t hα p
  · exact forgotten_homology_square
      (A := (cechComplexFunctor U).obj F.presheafModuleCat) (B := TP)
      (A' := (cechComplexFunctor U').obj ((tensorPullback f).obj F).presheafModuleCat)
      (B' := TI)
      (moduleCechComplexBeta U P (cechPushforwardAugmentation f F I)
        (cechPushforwardAugmentation_d f F I))
      (moduleCechBeta U' I) gamma t hβ p

end
end AlgebraicGeometry.Scheme.Modules
