/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.Paper.ModuleCupResolutionData
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
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

private def resolutionSectionsIso {A : Type*} [Category* A] [Abelian A]
    [EnoughInjectives A] {R : Type v} [Ring R]
    (Γ : A ⥤ ModuleCat.{v} R) [Γ.Additive] {F : A}
    (I : InjectiveResolution F) (p : ℕ) :=
  (forget₂ _ AddCommGrpCat.{v}).mapIso (I.isoRightDerivedObj Γ p) ≪≫
    ((((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).sc p).mapHomologyIso
      (forget₂ _ AddCommGrpCat.{v})).symm

private theorem resolutionSectionsIso_naturality {A : Type*} [Category* A] [Abelian A]
    [EnoughInjectives A] {R : Type v} [Ring R]
    (Γ : A ⥤ ModuleCat.{v} R) [Γ.Additive] {F : A}
    (I I' : InjectiveResolution F) (p : ℕ) :
    (resolutionSectionsIso Γ I p).hom ≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℕ) p).map
        (((Γ ⋙ forget₂ _ AddCommGrpCat.{v}).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (InjectiveResolution.desc (𝟙 F) I' I)) =
      (resolutionSectionsIso Γ I' p).hom := by
  let U := forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}
  let α := InjectiveResolution.desc (𝟙 F) I' I
  let S := ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).sc p
  let S' := ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj I'.cocomplex).sc p
  have hn := I.isoRightDerivedObj_hom_naturality (𝟙 F) I' α (by simp [α]) Γ p
  simp only [CategoryTheory.Functor.map_id, Category.id_comp] at hn
  have hs := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℕ) p).map
      ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map α)) U
  change U.map ((Γ.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
      HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) p).map α) ≫
      (S'.mapHomologyIso U).inv =
    (S.mapHomologyIso U).inv ≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℕ) p).map
        (((Γ ⋙ U).mapHomologicalComplex (ComplexShape.up ℕ)).map α) at hs
  change U.map (I.isoRightDerivedObj Γ p).hom ≫
      (S.mapHomologyIso U).inv ≫ _ =
    U.map (I'.isoRightDerivedObj Γ p).hom ≫ (S'.mapHomologyIso U).inv
  rw [← hs, ← Category.assoc, ← Functor.map_comp]
  exact congrArg (fun f ↦ U.map f ≫ (S'.mapHomologyIso U).inv) hn.symm

private def cupClassMap {X : Scheme.{v}} {F : X.Modules}
    (D : CupAcyclicResolution F) (n : ℕ) :=
  HomologicalComplex.homologyMap
    (((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat.{v}).mapHomologicalComplex (ComplexShape.up ℕ)).map
        D.comparison) n ≫
    (resolutionSectionsIso (RingedSpace.globalSectionsFunctor X.toRingedSpace) D.I n).inv

set_option maxHeartbeats 800000 in
-- Comparing module-valued homology with its underlying additive group needs extra elaboration.
private theorem cupClassMap_cycle {X : Scheme.{v}} {F : X.Modules}
    (D : CupAcyclicResolution F) (n : ℕ)
    (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.K).sc n).moduleCatLeftHomologyData.K) :
    cupClassMap D n
      ((((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj D.K).sc n).mapHomologyIso
          (forget₂ _ AddCommGrpCat.{v})).inv (cupCycleClass _ n a)) = D.class n a := by
  let : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  have : (RingedSpace.globalSectionsFunctor X.toRingedSpace).Additive :=
    RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
  let Γ := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let U := forget₂ (ModuleCat.{v}
    ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat.{v}
  have hs := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℕ) n).map
      ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map D.comparison)) U
  have h : HomologicalComplex.homologyMap
      (((Γ ⋙ U).mapHomologicalComplex (ComplexShape.up ℕ)).map D.comparison) n ≫
        (((RingedSpace.globalSectionsComplex D.I).sc n).mapHomologyIso U).hom =
      ((((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj D.K).sc n).mapHomologyIso U).hom
        ≫ U.map (HomologicalComplex.homologyMap
          ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map D.comparison) n) := hs
  unfold cupClassMap resolutionSectionsIso
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv]
  erw [← Category.assoc, h]
  simp only [ConcreteCategory.comp_apply]
  have he := ConcreteCategory.congr_hom
    (((((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj D.K).sc n).mapHomologyIso
      U).inv_hom_id) (cupCycleClass _ n a)
  exact congrArg (fun z ↦ U.map (D.I.isoRightDerivedObj Γ n).inv
    (U.map (HomologicalComplex.homologyMap
      ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map D.comparison) n) z)) he

private theorem cupPushforwardSectionsIso_naturality {X X' : Scheme.{v}} (f : X' ⟶ X)
    {K L : CochainComplex X'.Modules ℕ} (w : K ⟶ L) :
    ((RingedSpace.globalSectionsFunctor X'.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat.{v}).mapHomologicalComplex (ComplexShape.up ℕ)).map w ≫
        (cupPushforwardSectionsIso f L).hom =
      (cupPushforwardSectionsIso f K).hom ≫
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
          forget₂ _ AddCommGrpCat.{v}).mapHomologicalComplex (ComplexShape.up ℕ)).map
            (((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).map w) := by
  ext n : 1
  change ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
    (w.f n)).app _ ≫ (presheaf (L.X n)).map _ =
      (presheaf (K.X n)).map _ ≫
        ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map (w.f n)).app _
  exact (((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
    (w.f n)).naturality _).symm

set_option maxHeartbeats 800000 in
-- Comparing homology across two scalar rings requires additional elaboration steps.
/-- A sheaf cochain f-map over a coefficient f-map induces that coefficient map
on computing resolution classes. No tensor pairing is needed.
Source: Stacks Project, Tag 01FD, resolution comparison diagram, and Remark 01FB.
(blueprint: lem-sc-module-cup-resolution-fmap).

Proof: use the resolution choices C already selected in moduleCohomologyFMap.
Lift the identity maps from D.I to C.J and from E.I to C.I. The composites
D.comparison followed by the first lift and C.beta, and u followed by the
pushforward of E.comparison and the second lift and C.lambda, agree on the
augmentation. Since D.augmentation is a quasi-isomorphism and C.K is termwise
injective, these maps are homotopic. Apply global sections and homology.
The canonical sections identification commutes with E.comparison and its lift;
C.sections identifies C.a with that canonical identification. Naturality of the
injective-resolution and forgetting-scalars homology isomorphisms transports
the identity lifts to the cohomology identifications. Cancel C's invertible
replacement homology map to obtain equality of the maps from global homology
to cohomology. Finally naturality of the cycles-to-homology projection identifies
the image of the source kernel cycle with the specified target kernel cycle.
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
  let : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let : EnoughInjectives X'.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X'.toRingedSpace).2
  have : (RingedSpace.globalSectionsFunctor X.toRingedSpace).Additive :=
    RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
  have : (RingedSpace.globalSectionsFunctor X'.toRingedSpace).Additive :=
    RingedSpace.globalSectionsFunctor_additive X'.toRingedSpace
  let C := Classical.choice (moduleCohomologyFMapData_nonempty f F F' φ)
  let Γ := RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
    forget₂ _ AddCommGrpCat.{v}
  let Γ' := RingedSpace.globalSectionsFunctor X'.toRingedSpace ⋙
    forget₂ _ AddCommGrpCat.{v}
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℕ) n
  let HX := Γ.mapHomologicalComplex (ComplexShape.up ℕ)
  let HX' := Γ'.mapHomologicalComplex (ComplexShape.up ℕ)
  let P := (pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)
  let j := InjectiveResolution.desc (𝟙 F) C.J D.I
  let i := InjectiveResolution.desc (𝟙 F') C.I E.I
  have hj : D.augmentation ≫ D.comparison ≫ j = C.J.ι := by
    rw [← Category.assoc, D.over]
    simp [j]
  have hi : E.augmentation ≫ E.comparison ≫ i = C.I.ι := by
    rw [← Category.assoc, E.over]
    simp [i]
  have haug : D.augmentation ≫ (D.comparison ≫ j ≫ C.β) =
      D.augmentation ≫ (u ≫ P.map (E.comparison ≫ i) ≫ C.lambda) := by
    apply HomologicalComplex.from_single_hom_ext
    change D.augmentation.f 0 ≫ D.comparison.f 0 ≫ j.f 0 ≫ C.β.f 0 =
      D.augmentation.f 0 ≫ u.f 0 ≫
        (pushforward f).map (E.comparison.f 0 ≫ i.f 0) ≫ C.lambda.f 0
    have hj0 := HomologicalComplex.congr_hom hj 0
    have hi0 := HomologicalComplex.congr_hom hi 0
    simp only [HomologicalComplex.comp_f] at hj0 hi0
    calc
      _ = C.J.ι.f 0 ≫ C.β.f 0 := by
        simpa only [Category.assoc] using
          congrArg (fun t ↦ t ≫ C.β.f 0) hj0
      _ = φ ≫ (pushforward f).map (C.I.ι.f 0) ≫ C.lambda.f 0 := C.compatible
      _ = _ := by
        rw [← hi0, Functor.map_comp, Functor.map_comp]
        rw [← Category.assoc (D.augmentation.f 0), hu]
        simp only [Category.assoc]
  have : QuasiIso D.augmentation := D.quasiIso
  have ht := augmentedHomotopy D.augmentation C.injective
    (D.comparison ≫ j ≫ C.β) (u ≫ P.map (E.comparison ≫ i) ≫ C.lambda) haug
  have hh := (Γ.mapHomotopy ht).homologyMap_eq n
  have haC : C.a = cupPushforwardSectionsIso f C.I.cocomplex := by
    apply Iso.ext_inv
    ext k : 1
    exact C.sections k
  have hn := cupPushforwardSectionsIso_naturality f (E.comparison ≫ i)
  rw [← haC] at hn
  have hglobal : cupResolutionGlobalMap f u ≫ HX'.map (E.comparison ≫ i) ≫
      C.a.hom ≫ HX.map C.lambda = HX.map (u ≫ P.map (E.comparison ≫ i) ≫ C.lambda) := by
    dsimp [cupResolutionGlobalMap]
    rw [Category.assoc, ← Category.assoc (HX'.map _), hn]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    simp only [Functor.map_comp, Category.assoc]
    rfl
  have hhom : H.map (HX.map D.comparison) ≫ H.map (HX.map j) ≫
      H.map (HX.map C.β) =
      H.map (cupResolutionGlobalMap f u) ≫ H.map (HX'.map E.comparison) ≫
        H.map (HX'.map i) ≫ H.map (C.a.hom ≫ HX.map C.lambda) := by
    calc
      _ = H.map (HX.map (D.comparison ≫ j ≫ C.β)) := by
        simp only [Functor.map_comp]
      _ = H.map (HX.map (u ≫ P.map (E.comparison ≫ i) ≫ C.lambda)) := hh
      _ = _ := by
        rw [← hglobal]
        simp only [Functor.map_comp, Category.assoc]
  let rD := resolutionSectionsIso (RingedSpace.globalSectionsFunctor X.toRingedSpace) D.I n
  let rE := resolutionSectionsIso (RingedSpace.globalSectionsFunctor X'.toRingedSpace) E.I n
  let rJ := resolutionSectionsIso (RingedSpace.globalSectionsFunctor X.toRingedSpace) C.J n
  let rI := resolutionSectionsIso (RingedSpace.globalSectionsFunctor X'.toRingedSpace) C.I n
  have hjr : rD.hom ≫ H.map (HX.map j) = rJ.hom :=
    resolutionSectionsIso_naturality _ D.I C.J n
  have hir : rE.hom ≫ H.map (HX'.map i) = rI.hom :=
    resolutionSectionsIso_naturality _ E.I C.I n
  have : IsIso (H.map (C.a.hom ≫ HX.map C.lambda)) := C.invertible n
  have hmap : H.map (cupResolutionGlobalMap f u) ≫ cupClassMap E n =
      cupClassMap D n ≫ C.map n := by
    change H.map (cupResolutionGlobalMap f u) ≫
        (H.map (HX'.map E.comparison) ≫ rE.inv) =
      (H.map (HX.map D.comparison) ≫ rD.inv) ≫
        (rJ.hom ≫ H.map (HX.map C.β) ≫
          inv (H.map (C.a.hom ≫ HX.map C.lambda)) ≫ rI.inv)
    have hj' : rD.inv ≫ rJ.hom = H.map (HX.map j) := by
      rw [← hjr, Iso.inv_hom_id_assoc]
    have hi' : rE.inv ≫ rI.hom = H.map (HX'.map i) := by
      rw [← hir, Iso.inv_hom_id_assoc]
    rw [← cancel_mono (rI.hom ≫ H.map (C.a.hom ≫ HX.map C.lambda))]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [← Category.assoc rE.inv, hi', ← Category.assoc rD.inv, hj']
    exact hhom.symm
  have hc := additiveCycle_naturality
    (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.K)
    (((RingedSpace.globalSectionsFunctor X'.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj E.K) (cupResolutionGlobalMap f u) n a a' ha
  have hv := ConcreteCategory.congr_hom hmap
    ((((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.K).sc n).mapHomologyIso
        (forget₂ _ AddCommGrpCat.{v})).inv (cupCycleClass _ n a))
  change cupClassMap E n (HomologicalComplex.homologyMap (cupResolutionGlobalMap f u) n
    _) = C.map n (cupClassMap D n _) at hv
  calc
    E.class n a' = cupClassMap E n _ := (cupClassMap_cycle E n a').symm
    _ = cupClassMap E n (HomologicalComplex.homologyMap
        (cupResolutionGlobalMap f u) n _) :=
      congrArg (fun z ↦ cupClassMap E n z) hc.symm
    _ = C.map n (cupClassMap D n _) := hv
    _ = C.map n (D.class n a) :=
      congrArg (fun z ↦ C.map n z) (cupClassMap_cycle D n a)

end
end AlgebraicGeometry.Scheme.Modules
