/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.Paper.ModuleCupResolutionData
public import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap
import all Sheaf.AlgebraicGeometry.ModuleCohomologyFMap
import Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial
import WeilConjectures.Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-! # Maps of computing resolutions across a scheme morphism

Source: Stacks Project, Tag 01FD, the injective resolution comparison diagram.
-/

@[expose] public section

universe v
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- The canonical identification of global sections with sections of a pushforward.
Source: Stacks Project, Remark 01FB (blueprint: lem-sc-module-cup-resolution-fmap). -/
def cupPushforwardSectionsIso {X X' : Scheme.{v}} (f : X' ⟶ X)
    (K : CochainComplex X'.Modules ℕ) :
    ((RingedSpace.globalSectionsFunctor X'.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat.{v}).mapHomologicalComplex (ComplexShape.up ℕ)).obj K ≅
    ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat.{v}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj K) := by
  refine (HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (presheaf (K.X n)).mapIso
      (eqToIso (by simp) : op (f ⁻¹ᵁ (⊤ : X.Opens)) ≅ op (⊤ : X'.Opens))) ?_).symm
  intro n m _
  change (presheaf (K.X n)).map _ ≫
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map (K.d n m)).app _ =
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map (K.d n m)).app _ ≫
      (presheaf (K.X m)).map _
  exact ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
    (K.d n m)).naturality _

/-- Take global sections of a sheaf cochain f-map and restrict along f-inverse(top)=top.
Source: Stacks Project, Remark 01FB (blueprint: lem-sc-module-cup-resolution-fmap). -/
def cupResolutionGlobalMap {X X' : Scheme.{v}} (f : X' ⟶ X)
    {K : CochainComplex X.Modules ℕ} {L : CochainComplex X'.Modules ℕ}
    (u : K ⟶ ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj L) :
    ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat.{v}).mapHomologicalComplex (ComplexShape.up ℕ)).obj K ⟶
    ((RingedSpace.globalSectionsFunctor X'.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat.{v}).mapHomologicalComplex (ComplexShape.up ℕ)).obj L :=
  ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
    forget₂ _ AddCommGrpCat.{v}).mapHomologicalComplex (ComplexShape.up ℕ)).map u ≫
      (cupPushforwardSectionsIso f L).inv

/-- Maps from an augmented resolution to an injective complex are homotopic
when they agree on the augmentation. -/
private def augmentedHomotopyZero {X : Scheme.{v}} {F : X.Modules}
    {K L : CochainComplex X.Modules ℕ}
    (a : (CochainComplex.single₀ X.Modules).obj F ⟶ K) [QuasiIso a]
    (hL : ∀ n, Injective (L.X n)) (u : K ⟶ L) (ha : a ≫ u = 0) :
    Homotopy u 0 := by
  let : ∀ n, Injective (L.X n) := hL
  let s₀ : K.X 1 ⟶ L.X 0 :=
    (CochainComplex.exact₀_of_quasiIso_single₀ a).descToInjective (u.f 0)
      (HomologicalComplex.congr_hom ha 0)
  have hs₀ : K.d 0 1 ≫ s₀ = u.f 0 :=
    (CochainComplex.exact₀_of_quasiIso_single₀ a).comp_descToInjective _ _
  let s₁ : K.X 2 ⟶ L.X 1 :=
    (CochainComplex.exact_succ_of_quasiIso_single₀ a 0).descToInjective
      (u.f 1 - s₀ ≫ L.d 0 1) (by
        rw [Preadditive.comp_sub, ← Category.assoc, hs₀, u.comm, sub_self])
  have hs₁ : K.d 1 2 ≫ s₁ = u.f 1 - s₀ ≫ L.d 0 1 :=
    (CochainComplex.exact_succ_of_quasiIso_single₀ a 0).comp_descToInjective _ _
  refine Homotopy.mkCoinductive _ s₀ (by simpa using hs₀.symm)
    s₁ (by simp [hs₁]) ?_
  intro n data
  rcases data with ⟨g, g', w⟩
  have hw : u.f (n + 1) = K.d (n + 1) (n + 2) ≫ g' + g ≫ L.d n (n + 1) := by
    simpa [add_comm] using w
  let s : K.X (n + 3) ⟶ L.X (n + 2) :=
    (CochainComplex.exact_succ_of_quasiIso_single₀ a (n + 1)).descToInjective
      (u.f (n + 2) - g' ≫ L.d _ _) (by
        rw [Preadditive.comp_sub, ← u.comm, hw, Preadditive.add_comp,
          Category.assoc, Category.assoc, HomologicalComplex.d_comp_d,
          comp_zero, add_zero, sub_self])
  have hs : K.d (n + 2) (n + 3) ≫ s = u.f (n + 2) - g' ≫ L.d _ _ :=
    (CochainComplex.exact_succ_of_quasiIso_single₀ a (n + 1)).comp_descToInjective _ _
  exact ⟨s, by simp [hs]⟩

private def augmentedHomotopy {X : Scheme.{v}} {F : X.Modules}
    {K L : CochainComplex X.Modules ℕ}
    (a : (CochainComplex.single₀ X.Modules).obj F ⟶ K) [QuasiIso a]
    (hL : ∀ n, Injective (L.X n)) (u w : K ⟶ L) (h : a ≫ u = a ≫ w) :
    Homotopy u w :=
  Homotopy.equivSubZero.invFun
    (augmentedHomotopyZero a hL (u - w) (by simp [Preadditive.comp_sub, h]))

private theorem forgetCupHomologyπ {R : Type v} [Ring R]
    (S : ShortComplex (ModuleCat.{v} R)) :
    (forget₂ _ AddCommGrpCat.{v}).map S.homologyπ ≫
        (S.mapHomologyIso (forget₂ _ AddCommGrpCat.{v})).inv =
      (S.mapCyclesIso (forget₂ _ AddCommGrpCat.{v})).inv ≫
        (S.map (forget₂ _ AddCommGrpCat.{v})).homologyπ := by
  let U := forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}
  let hl := S.homologyData.left
  rw [hl.mapHomologyIso_eq U, hl.mapCyclesIso_eq U]
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Category.assoc]
  rw [← U.map_comp_assoc, hl.homologyπ_comp_homologyIso_hom]
  simp only [Functor.map_comp, Category.assoc]
  erw [(hl.map U).π_comp_homologyIso_inv]

private def additiveCycle {R : Type v} [Ring R]
    (K : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (a : (K.sc n).moduleCatLeftHomologyData.K) :
    (((forget₂ _ AddCommGrpCat.{v}).mapHomologicalComplex (ComplexShape.up ℕ)).obj K).cycles
      n :=
  ((K.sc n).mapCyclesIso (forget₂ _ AddCommGrpCat.{v})).inv
    ((K.sc n).moduleCatCyclesIso.inv a)

private theorem additiveCycle_val {R : Type v} [Ring R]
    (K : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (a : (K.sc n).moduleCatLeftHomologyData.K) :
    HomologicalComplex.iCycles
      (((forget₂ _ AddCommGrpCat.{v}).mapHomologicalComplex (ComplexShape.up ℕ)).obj K) n
        (additiveCycle K n a) = a.val := by
  let S := K.sc n
  let U := forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}
  have h : U.map S.moduleCatCyclesIso.inv ≫ (S.mapCyclesIso U).inv ≫
      (S.map U).iCycles = U.map S.moduleCatLeftHomologyData.i := by
    rw [← ShortComplex.mapCyclesIso_hom_iCycles, Iso.inv_hom_id_assoc,
      ← U.map_comp, ShortComplex.moduleCatCyclesIso_inv_iCycles]
  exact ConcreteCategory.congr_hom h a

private theorem additiveCycle_class {R : Type v} [Ring R]
    (K : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (a : (K.sc n).moduleCatLeftHomologyData.K) :
    HomologicalComplex.homologyπ
      (((forget₂ _ AddCommGrpCat.{v}).mapHomologicalComplex (ComplexShape.up ℕ)).obj K) n
        (additiveCycle K n a) =
      ((K.sc n).mapHomologyIso (forget₂ _ AddCommGrpCat.{v})).inv (cupCycleClass K n a) :=
  (ConcreteCategory.congr_hom (forgetCupHomologyπ (K.sc n))
    ((K.sc n).moduleCatCyclesIso.inv a)).symm

private theorem additiveCycle_naturality {R R' : Type v} [Ring R] [Ring R']
    (K : CochainComplex (ModuleCat.{v} R) ℕ)
    (L : CochainComplex (ModuleCat.{v} R') ℕ)
    (u : ((forget₂ _ AddCommGrpCat.{v}).mapHomologicalComplex (ComplexShape.up ℕ)).obj K ⟶
      ((forget₂ _ AddCommGrpCat.{v}).mapHomologicalComplex (ComplexShape.up ℕ)).obj L)
    (n : ℕ) (a : (K.sc n).moduleCatLeftHomologyData.K)
    (b : (L.sc n).moduleCatLeftHomologyData.K) (hab : b.val = u.f n a.val) :
    HomologicalComplex.homologyMap u n
        (((K.sc n).mapHomologyIso (forget₂ _ AddCommGrpCat.{v})).inv
          (cupCycleClass K n a)) =
      ((L.sc n).mapHomologyIso (forget₂ _ AddCommGrpCat.{v})).inv (cupCycleClass L n b) := by
  have hcycles : HomologicalComplex.cyclesMap u n (additiveCycle K n a) =
      additiveCycle L n b := by
    apply (AddCommGrpCat.mono_iff_injective (HomologicalComplex.iCycles _ n)).mp
      inferInstance
    have h := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i u n)
      (additiveCycle K n a)
    simpa only [ConcreteCategory.comp_apply, additiveCycle_val, hab] using h
  have h := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality u n)
    (additiveCycle K n a)
  simpa only [ConcreteCategory.comp_apply, hcycles, additiveCycle_class] using h

set_option maxHeartbeats 800000 in
-- Comparing homology across two scalar rings requires additional elaboration steps.
/-- A sheaf cochain f-map over a coefficient f-map induces that coefficient map
on computing resolution classes. No tensor pairing is needed.
Source: Stacks Project, Tag 01FD, resolution comparison diagram, and Remark 01FB.
(blueprint: lem-sc-module-cup-resolution-fmap).

Proof: choose the injective resolutions already stored in D and E, and resolve the
pushforward of E.I by a nonnegative injective complex J. Lift the coefficient map
from D.I to J. The composite of D.comparison with this lift and the composite of
u with the pushforward of E.comparison and the replacement map agree on the
augmentation. Since D.augmentation is a quasi-isomorphism and J is termwise
injective, these two composites are homotopic. Apply global sections and homology.
The canonical sections identification commutes with E.comparison. Cancel the
invertible replacement homology map. Transport through the injective-resolution
isomorphisms and the forgetting-scalars homology isomorphisms. Independence of
the injective choices identifies the resulting map with moduleCohomologyFMap.
Finally naturality of the cycles-to-homology projection identifies its value on a
kernel cycle with the class of any cycle having the displayed underlying section.
This works in degree zero, for zero coefficients, and on the empty scheme. -/
theorem cupResolution_class_fmap {X X' : Scheme.{v}} (f : X' ⟶ X)
    {F : X.Modules} {F' : X'.Modules}
    (D : CupAcyclicResolution F) (E : CupAcyclicResolution F')
    (φ : F ⟶ (pushforward f).obj F')
    (u : D.K ⟶ ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj E.K)
    (hu : D.augmentation.f 0 ≫ u.f 0 =
      φ ≫ (pushforward f).map (E.augmentation.f 0))
    (n : ℕ)
    (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.K).sc n).moduleCatLeftHomologyData.K)
    (a' : ((((RingedSpace.globalSectionsFunctor X'.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj E.K).sc n).moduleCatLeftHomologyData.K)
    (ha : a'.val = (cupResolutionGlobalMap f u).f n a.val) :
    E.class n a' = moduleCohomologyFMap f φ n (D.class n a) := by
  have : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  have : EnoughInjectives X'.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X'.toRingedSpace).2
  let SX := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let SY := RingedSpace.globalSectionsFunctor X'.toRingedSpace
  have : SX.Additive := RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
  have : SY.Additive := RingedSpace.globalSectionsFunctor_additive X'.toRingedSpace
  let UX := forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v}
  let UY := forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat.{v}
  let HX := (SX ⋙ UX).mapHomologicalComplex (ComplexShape.up ℕ)
  let HY := (SY ⋙ UY).mapHomologicalComplex (ComplexShape.up ℕ)
  let P := pushforward f
  let PP := P.mapHomologicalComplex (ComplexShape.up ℕ)
  have : QuasiIso D.augmentation := D.quasiIso
  obtain ⟨J, lam, hJ, hlam⟩ := nat_complex_injective_resolution (PP.obj E.I.cocomplex)
  let γ := φ ≫ P.map (E.I.ι.f 0) ≫ lam.f 0
  have hγ : γ ≫ J.d 0 1 = 0 := by
    dsimp [γ]
    rw [Category.assoc, Category.assoc, lam.comm]
    change φ ≫ P.map (E.I.ι.f 0) ≫ P.map (E.I.cocomplex.d 0 1) ≫ lam.f 1 = 0
    rw [← Functor.map_comp_assoc, E.I.ι_f_zero_comp_complex_d, Functor.map_zero]
    simp
  obtain ⟨β, hβ⟩ := lift_to_nat_injectives D.I J hJ γ hγ
  have : QuasiIso (HX.map lam) :=
    nat_quasiIso_globalSections_pushforward_injectives f E.I.cocomplex J
      (fun n ↦ inferInstance) hJ lam hlam
  let C : ModuleCohomologyFMapData f F F' φ := {
    I := E.I
    J := D.I
    K := J
    injective := hJ
    lambda := lam
    quasiIso := hlam
    β := β
    compatible := hβ
    a := cupPushforwardSectionsIso f E.I.cocomplex
    sections := fun n ↦ rfl
    invertible := fun k ↦ by
      have : IsIso (HomologicalComplex.homologyMap (HX.map lam) k) := by infer_instance
      change IsIso (HomologicalComplex.homologyMap
        ((cupPushforwardSectionsIso f E.I.cocomplex).hom ≫ HX.map lam) k)
      rw [HomologicalComplex.homologyMap_comp]
      infer_instance }
  have hchoice : moduleCohomologyFMap f φ n = C.map n := by
    exact moduleCohomologyFMap_independent f φ
      (Classical.choice (moduleCohomologyFMapData_nonempty f F F' φ)) C n
  have haug : D.augmentation ≫ (u ≫ PP.map E.comparison ≫ lam) =
      D.augmentation ≫ (D.comparison ≫ β) := by
    apply HomologicalComplex.from_single_hom_ext
    simp only [HomologicalComplex.comp_f]
    change D.augmentation.f 0 ≫ u.f 0 ≫ P.map (E.comparison.f 0) ≫ lam.f 0 =
      D.augmentation.f 0 ≫ D.comparison.f 0 ≫ β.f 0
    rw [← Category.assoc, hu, Category.assoc, ← P.map_comp_assoc]
    have he := HomologicalComplex.congr_hom E.over 0
    simp only [HomologicalComplex.comp_f] at he
    rw [he]
    have hd := HomologicalComplex.congr_hom D.over 0
    simp only [HomologicalComplex.comp_f] at hd
    rw [← Category.assoc (D.augmentation.f 0), hd]
    exact hβ.symm
  let h := augmentedHomotopy D.augmentation hJ
    (u ≫ PP.map E.comparison ≫ lam) (D.comparison ≫ β) haug
  have hhom := ((SX ⋙ UX).mapHomotopy h).homologyMap_eq n
  change HomologicalComplex.homologyMap (HX.map (u ≫ PP.map E.comparison ≫ lam)) n =
    HomologicalComplex.homologyMap (HX.map (D.comparison ≫ β)) n at hhom
  simp only [Functor.map_comp, HomologicalComplex.homologyMap_comp] at hhom
  have hs : (cupPushforwardSectionsIso f E.K).hom ≫ HX.map (PP.map E.comparison) =
      HY.map E.comparison ≫ (cupPushforwardSectionsIso f E.I.cocomplex).hom := by
    rw [← cancel_mono (cupPushforwardSectionsIso f E.I.cocomplex).inv,
      Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      ← cancel_epi (cupPushforwardSectionsIso f E.K).inv, Iso.inv_hom_id_assoc]
    ext1 k
    change ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
      (E.comparison.f k)).app _ ≫ (presheaf (E.I.cocomplex.X k)).map _ =
        (presheaf (E.K.X k)).map _ ≫
          ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
            (E.comparison.f k)).app _
    exact ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
      (E.comparison.f k)).naturality _ |>.symm
  let δ := cupResolutionGlobalMap f u
  let μ := (cupPushforwardSectionsIso f E.I.cocomplex).hom ≫ HX.map lam
  have hδ : δ ≫ HY.map E.comparison ≫ μ = HX.map u ≫
      HX.map (PP.map E.comparison) ≫ HX.map lam := by
    dsimp only [δ, μ, cupResolutionGlobalMap]
    rw [Category.assoc, ← Category.assoc (HY.map E.comparison), ← hs]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rfl
  have heq : HomologicalComplex.homologyMap δ n ≫
      HomologicalComplex.homologyMap (HY.map E.comparison) n ≫
        HomologicalComplex.homologyMap μ n =
      HomologicalComplex.homologyMap (HX.map D.comparison) n ≫
        HomologicalComplex.homologyMap (HX.map β) n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      hδ]
    simpa only [HomologicalComplex.homologyMap_comp] using hhom
  let TX := SX.mapHomologicalComplex (ComplexShape.up ℕ)
  let TY := SY.mapHomologicalComplex (ComplexShape.up ℕ)
  let rD := UX.mapIso (D.I.isoRightDerivedObj SX n) ≪≫
    (((RingedSpace.globalSectionsComplex D.I).sc n).mapHomologyIso UX).symm
  let rE := UY.mapIso (E.I.isoRightDerivedObj SY n) ≪≫
    (((RingedSpace.globalSectionsComplex E.I).sc n).mapHomologyIso UY).symm
  let z := ((TX.obj D.K).sc n).mapHomologyIso UX |>.inv (cupCycleClass (TX.obj D.K) n a)
  let z' := ((TY.obj E.K).sc n).mapHomologyIso UY |>.inv (cupCycleClass (TY.obj E.K) n a')
  have hD : rD.hom (D.class n a) =
      HomologicalComplex.homologyMap (HX.map D.comparison) n z := by
    change (((RingedSpace.globalSectionsComplex D.I).sc n).mapHomologyIso UX).inv
      ((D.I.isoRightDerivedObj SX n).hom ((D.I.isoRightDerivedObj SX n).inv
        (HomologicalComplex.homologyMap (TX.map D.comparison) n
          (cupCycleClass (TX.obj D.K) n a)))) = _
    rw [Iso.inv_hom_id_apply]
    exact ConcreteCategory.congr_hom
      (ShortComplex.mapHomologyIso_inv_naturality
        ((HomologicalComplex.shortComplexFunctor _ _ n).map (TX.map D.comparison)) UX)
      (cupCycleClass (TX.obj D.K) n a)
  have hE : rE.hom (E.class n a') =
      HomologicalComplex.homologyMap (HY.map E.comparison) n z' := by
    change (((RingedSpace.globalSectionsComplex E.I).sc n).mapHomologyIso UY).inv
      ((E.I.isoRightDerivedObj SY n).hom ((E.I.isoRightDerivedObj SY n).inv
        (HomologicalComplex.homologyMap (TY.map E.comparison) n
          (cupCycleClass (TY.obj E.K) n a')))) = _
    rw [Iso.inv_hom_id_apply]
    exact ConcreteCategory.congr_hom
      (ShortComplex.mapHomologyIso_inv_naturality
        ((HomologicalComplex.shortComplexFunctor _ _ n).map (TY.map E.comparison)) UY)
      (cupCycleClass (TY.obj E.K) n a')
  have hz : HomologicalComplex.homologyMap δ n z = z' :=
    additiveCycle_naturality (TX.obj D.K) (TY.obj E.K) δ n a a' ha
  have hm : IsIso (HomologicalComplex.homologyMap μ n) := C.invertible n
  have hvalue :
      HomologicalComplex.homologyMap (HY.map E.comparison) n z' =
        inv (HomologicalComplex.homologyMap μ n)
          (HomologicalComplex.homologyMap (HX.map β) n
            (HomologicalComplex.homologyMap (HX.map D.comparison) n z)) := by
    have hv := ConcreteCategory.congr_hom heq z
    simp only [ConcreteCategory.comp_apply, hz] at hv
    have hv' := congrArg (fun x ↦ inv (HomologicalComplex.homologyMap μ n) x) hv
    have hinv := ConcreteCategory.congr_hom
      (IsIso.hom_inv_id (HomologicalComplex.homologyMap μ n))
      (HomologicalComplex.homologyMap (HY.map E.comparison) n z')
    exact hinv.symm.trans hv'
  have hC : C.map n = rD.hom ≫ HomologicalComplex.homologyMap (HX.map β) n ≫
      inv (HomologicalComplex.homologyMap μ n) ≫ rE.inv := by
    simp only [C, ModuleCohomologyFMapData.map, rD, rE, μ, Iso.trans_hom,
      Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom,
      Functor.mapIso_inv, Category.assoc]
    rfl
  apply (AddCommGrpCat.mono_iff_injective rE.hom).mp inferInstance
  rw [hE, hchoice, hC]
  simp only [ConcreteCategory.comp_apply]
  calc
    HomologicalComplex.homologyMap (HY.map E.comparison) n z' =
        inv (HomologicalComplex.homologyMap μ n)
          (HomologicalComplex.homologyMap (HX.map β) n (rD.hom (D.class n a))) := by
      rw [hD]
      exact hvalue
    _ = rE.hom (rE.inv (inv (HomologicalComplex.homologyMap μ n)
        (HomologicalComplex.homologyMap (HX.map β) n (rD.hom (D.class n a))))) :=
      (ConcreteCategory.congr_hom rE.inv_hom_id _).symm

end
end AlgebraicGeometry.Scheme.Modules
