/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M6
-/
module

public import Sheaf.CategoryTheory.ScalarLocalizationCoefficientActions
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Sheaf.CategoryTheory.ScalarLocalizationRegularColimit
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison

/-!
# Scalar localization as an ordinary module-sheaf colimit

Source: Stacks Project, Tags 00CM, 03CY and 03EK.
(blueprint: lem-weil-pbc-scalar-localization-module-colimit)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2048

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ChangeOfRings


attribute [local irreducible] CategoryTheory.scalarLocalizationCoefficientMap
  SheafOfModules.tensorPresheafUnit SheafOfModules.regularTensorIso
  SheafOfModules.tensorObjIsoSheafification
  CategoryTheory.ringedLocalizationRing CategoryTheory.ringedLocalizationRingUnit

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

private theorem transport_scalar_colimit
    {B D : Type*} [Category B] [Category D]
    (X : B) (u : X ⟶ X) (Y : D) (v : Y ⟶ Y)
    (F : B ⥤ D) (e : F.obj X ≅ Y)
    (he : F.map u ≫ e.hom = e.hom ≫ v)
    (c : Cocone (Functor.ofSequence (X := fun _ : ℕ ↦ X) (fun _ ↦ u)))
    (hc : IsColimit c) [PreservesColimit
      (Functor.ofSequence (X := fun _ : ℕ ↦ X) (fun _ ↦ u)) F]
    {Z : D} (β : F.obj c.pt ≅ Z)
    (l : ℕ → (Y ⟶ Z)) (hl : ∀ n, v ≫ l (n + 1) = l n)
    (hz : F.map (c.ι.app 0) ≫ β.hom = e.hom ≫ l 0)
    (w : Z ⟶ Z) [Mono w]
    (hcenter : ∀ n, F.map u ≫ F.map (c.ι.app n) ≫ β.hom =
      F.map (c.ι.app n) ≫ β.hom ≫ w)
    (hcenterl : ∀ n, v ≫ l n = l n ≫ w) :
    ∃ d : Cocone (Functor.ofSequence (X := fun _ : ℕ ↦ Y) (fun _ ↦ v)),
      Nonempty (IsColimit d) ∧ ∃ γ : d.pt ≅ Z,
        ∀ n, d.ι.app n ≫ γ.hom = l n := by
  let S := Functor.ofSequence (X := fun _ : ℕ ↦ X) (fun _ ↦ u)
  let T := Functor.ofSequence (X := fun _ : ℕ ↦ Y) (fun _ ↦ v)
  let τ : S ⋙ F ⟶ T := NatTrans.ofSequence (fun _ ↦ e.hom) (by
    intro n
    simpa only [S, T, Functor.comp_map, Functor.ofSequence_map_homOfLE_succ] using he)
  let ε : S ⋙ F ≅ T := NatIso.ofComponents (fun _ ↦ e) (by
    intro n m f
    exact τ.naturality f)
  let d := (Cocone.precompose ε.inv).obj (F.mapCocone c)
  have hd : IsColimit d :=
    (IsColimit.precomposeHomEquiv ε.symm (F.mapCocone c)).symm
      (isColimitOfPreserves F hc)
  refine ⟨d, ⟨hd⟩, β, ?_⟩
  have h (n : ℕ) : F.map (c.ι.app n) ≫ β.hom = e.hom ≫ l n := by
    induction n with
    | zero => exact hz
    | succ n ih =>
      apply (cancel_mono w).1
      have hw := c.w (homOfLE (Nat.le_succ n))
      simp only [Functor.ofSequence_map_homOfLE_succ] at hw
      calc
        (F.map (c.ι.app (n + 1)) ≫ β.hom) ≫ w =
            F.map u ≫ F.map (c.ι.app (n + 1)) ≫ β.hom := by
          rw [Category.assoc, hcenter]
        _ = F.map (c.ι.app n) ≫ β.hom := by rw [← F.map_comp_assoc, hw]
        _ = e.hom ≫ l n := ih
        _ = (e.hom ≫ l (n + 1)) ≫ w := by
          rw [Category.assoc, ← hcenterl, ← hl n]
  intro n
  change (e.inv ≫ F.map (c.ι.app n)) ≫ β.hom = _
  rw [Category.assoc, h n]
  simp only [Iso.inv_hom_id_assoc]

private theorem regular_tensor_scalar_apply
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u})
    (M : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (f : SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⟶
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (V : Cᵒᵖ) (x : M.val.obj V) (r : R.obj.obj V)
    (hf : f.val.app V (1 : R.obj.obj V) = r) :
    letI := SheafOfModules.monoidalCategory R
    ∀ (e : (tensorRight M).obj
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ≅ M),
      (∀ y : M.val.obj V, e.inv.val.app V y =
        (SheafOfModules.tensorPresheafUnit
          (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) M
        ).app V ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] y)) →
      e.hom.val.app V (((tensorRight M).map f).val.app V (e.inv.val.app V x)) = r • x := by
  let := SheafOfModules.monoidalCategory R
  dsimp only
  intro e he
  let X := SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  have hn := SheafOfModules.tensorPresheafUnit_naturality f M
  have hn' := congrArg (fun g ↦ g.app V ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x)) hn
  have hnorm := congrArg (((tensorRight M).map f).val.app V) (he x)
  have ht : ((f.val ▷ M.val).app V) ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x) =
      r • ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x) := by
    change (f.val.app V (1 : R.obj.obj V)) ⊗ₜ[R.obj.obj V] x = _
    rw [hf]
    exact ((TensorProduct.smul_tmul' r (1 : R.obj.obj V) x).trans
      (congrArg (fun y : R.obj.obj V ↦ y ⊗ₜ[R.obj.obj V] x) (mul_one r))).symm
  have hp := congrArg ((SheafOfModules.tensorPresheafUnit X M).app V) ht
  have hs := ((SheafOfModules.tensorPresheafUnit X M).app V).hom.map_smul
    r ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x)
  have hnall := hnorm.trans (hn'.trans (hp.trans hs))
  have hmap := congrArg (e.hom.val.app V) hnall
  have he' := (e.hom.val.app V).hom.map_smul r
    ((SheafOfModules.tensorPresheafUnit X M).app V
      ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x))
  have hi := congrArg (fun g ↦ g.val.app V x) e.inv_hom_id
  change e.hom.val.app V (e.inv.val.app V x) = x at hi
  have hh := congrArg (fun y ↦ r • e.hom.val.app V y) (he x).symm
  exact hmap.trans (he'.trans (hh.trans (congrArg (fun y ↦ r • y) hi)))

private theorem isIso_scalar_of_inverse
    {B : Type*} [Category B] [Preadditive B]
    {T : Type*} [CommRing T] [Linear T B]
    (X : B) (r s : T) (h : r * s = 1) : IsIso (r • 𝟙 X) := by
  refine ⟨⟨s • 𝟙 X, ?_, ?_⟩⟩
  · simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul]
    rw [mul_comm s r, h, one_smul]
  · simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul]
    rw [h, one_smul]

private theorem inverse_scalar_legs_step
    {B D : Type*} [Category B] [Category D] [Preadditive B] [Preadditive D]
    {A S : Type*} [CommRing A] [CommRing S] [Linear A B] [Linear S D]
    (U : D ⥤ B) (X : B) (Y : D) (η : X ⟶ U.obj Y)
    (t : A) (r s : S) (hrs : r * s = 1)
    (hz : t • 𝟙 (U.obj Y) = U.map (r • 𝟙 Y)) (n : ℕ) :
    (t • 𝟙 X) ≫ (η ≫ U.map (s ^ (n + 1) • 𝟙 Y)) =
      η ≫ U.map (s ^ n • 𝟙 Y) := by
  rw [Linear.smul_comp, Category.id_comp, ← Linear.comp_smul]
  rw [← Category.id_comp (U.map (s ^ (n + 1) • 𝟙 Y)), ← Linear.smul_comp, hz,
    ← U.map_comp]
  apply congrArg (fun f ↦ η ≫ U.map f)
  simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul]
  congr 1
  calc
    s ^ (n + 1) * r = s ^ n * (r * s) := by ring
    _ = s ^ n := by rw [hrs, mul_one]

private theorem tensor_scalar_colimit
    {B D T : Type*} [Category B] [Category D] [Category T]
    [Preadditive D] [Preadditive T]
    {A S : Type*} [CommRing A] [CommRing S] [Linear A D] [Linear S T]
    (X : B) (u : X ⟶ X) (Y : D) (F : B ⥤ D) (e : F.obj X ≅ Y)
    (t : A) (he : F.map u ≫ e.hom = e.hom ≫ (t • 𝟙 Y))
    (c : Cocone (Functor.ofSequence (X := fun _ : ℕ ↦ X) (fun _ ↦ u)))
    (hc : IsColimit c) [PreservesColimit
      (Functor.ofSequence (X := fun _ : ℕ ↦ X) (fun _ ↦ u)) F]
    (U : T ⥤ D) (N : T) (η : Y ⟶ U.obj N) (β : F.obj c.pt ≅ U.obj N)
    (hzero : F.map (c.ι.app 0) ≫ β.hom = e.hom ≫ η)
    (r s : S) (hrs : r * s = 1) (hz : t • 𝟙 (U.obj N) = U.map (r • 𝟙 N)) :
    ∃ d : Cocone (Functor.ofSequence (X := fun _ : ℕ ↦ Y) (fun _ ↦ t • 𝟙 Y)),
      Nonempty (IsColimit d) ∧ ∃ γ : d.pt ≅ U.obj N,
        ∀ n : ℕ, d.ι.app n ≫ γ.hom = η ≫ U.map (s ^ n • 𝟙 N) := by
  have hu : F.map u = t • 𝟙 (F.obj X) := by
    apply (cancel_mono e.hom).1
    rw [he, Linear.comp_smul, Category.comp_id, Linear.smul_comp, Category.id_comp]
  have : IsIso (r • 𝟙 N) := isIso_scalar_of_inverse N r s hrs
  have : IsIso (t • 𝟙 (U.obj N)) := by rw [hz]; infer_instance
  refine transport_scalar_colimit X u Y (t • 𝟙 Y) F e he c hc β
    (fun n ↦ η ≫ U.map (s ^ n • 𝟙 N))
    (inverse_scalar_legs_step U Y N η t r s hrs hz) ?_ (t • 𝟙 (U.obj N)) ?_ ?_
  · simpa only [pow_zero, one_smul, Functor.map_id, Category.comp_id] using hzero
  · intro n
    rw [hu]
    simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]
  · intro n
    simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]

set_option linter.style.whitespace false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 400000 in
-- The sectionwise tensor normalization has a large elaborated type.
/-- The fraction legs exhibit restricted scalar extension as the module-sheaf colimit.
Source: Stacks Project, algebra.tex Tag 00CM; sites-modules.tex Tags 03CY and 03EK.
(blueprint: lem-weil-pbc-scalar-localization-module-colimit).

Proof: the sectionwise fraction maps from R into R[1/t] give a colimit: a
compatible family sends r/t^n to the stage-n image of r. The fraction equality
criterion gives equality at a common stage, including t-torsion. These maps
commute with restrictions and descend through module sheafification. Tensoring
with M preserves this colimit by tensor--Hom adjunction. The comparison between
restricted extension of scalars and the sheaf tensor identifies the resulting
object with U(N); the normalized unit fixes the zeroth leg, and multiplication
by the inverse powers of t fixes all the other legs. -/
theorem scalarLocalization_moduleColimit
    (A : Type v) [CommRing A]
    (R : Sheaf J CommRingCat.{u})
    (a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat))
    (t : A)
    (M : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (N : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
      (ringedLocalizationRing R (a t))))
    (hN : N = SheafOfModules.changeOfRings (ringedLocalizationRingUnit R (a t)) M)
    (U : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (ringedLocalizationRing R (a t))) ⥤
      ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (hU : U = SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map
        (ringedLocalizationRingUnit R (a t))))
    (η : M ⟶ U.obj N)
    (hη : scalarLocalizationTelescopeUnitSections (ringedLocalizationRingUnit R (a t))
      M N hN (η ≫ eqToHom (congrArg (fun T ↦ T.obj N) hU))) :
    (fun [_source : Linear A (ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
      [_target : Linear (Localization.Away t) (ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          (ringedLocalizationRing R (a t))))] ↦
      ∃ c : Cocone (Functor.ofSequence (X := fun _n : ℕ ↦ M) (fun _n ↦ t • 𝟙 M)),
        Nonempty (IsColimit c) ∧ ∃ β : c.pt ≅ U.obj N,
          ∀ n : ℕ, c.ι.app n ≫ β.hom = η ≫ U.map
            (((IsLocalization.Away.invSelf t : Localization.Away t) ^ n) • 𝟙 N))
      (_source := scalarLocalizationCoefficientLinear A R a)
      (_target := scalarLocalizationCoefficientLinear (Localization.Away t)
        (ringedLocalizationRing R (a t)) (scalarLocalizationCoefficientMap A R a t)) := by
  classical
  generalize hs : scalarLocalizationCoefficientLinear A R a = src
  generalize ht : scalarLocalizationCoefficientLinear (Localization.Away t)
    (ringedLocalizationRing R (a t)) (scalarLocalizationCoefficientMap A R a t) = tgt
  have : J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) := inferInstance
  have : J.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  have : HasWeakSheafify J AddCommGrpCat.{u} := inferInstance
  subst U
  subst N
  let O := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
  let S := ringedLocalizationRing R (a t)
  let φ := ringedLocalizationRingUnit R (a t)
  let U := SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  obtain ⟨eT, heT⟩ := SheafOfModules.exists_extensionTensorComparison φ M
  let : Linear A (SheafOfModules O) := src
  let : Linear (Localization.Away t) (SheafOfModules
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)) :=
    tgt
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let X := SheafOfModules.unit O
  let F := tensorRight M
  let ε : F.obj X ≅ M := SheafOfModules.regularTensorIso M
  have hεinv (V : Cᵒᵖ) (x : M.val.obj V) : ε.inv.val.app V x =
      (SheafOfModules.tensorPresheafUnit X M).app V
        ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x) :=
    SheafOfModules.regularTensorIso_inv_apply M V x
  clear_value ε
  obtain ⟨c, ⟨hc⟩, ec, hec⟩ := scalarLocalization_regularColimit R (a t)
  obtain ⟨eS, heS⟩ := ringedLocalizationRing_moduleComparison R (a t)
  let β : F.obj c.pt ≅ U.obj (SheafOfModules.changeOfRings.{u, u, u} φ M) :=
    F.mapIso ec ≪≫ F.mapIso eS.symm ≪≫ eT
  have : PreservesColimitsOfSize.{0, 0} F := by
    let e : tensorLeft M ≅ tensorRight M :=
      NatIso.ofComponents (fun Y ↦ β_ M Y)
        (fun f ↦ BraidedCategory.braiding_naturality_right M f)
    have := (SheafOfModules.tensorHomAdjunction R M).leftAdjoint_preservesColimits
    exact preservesColimits_of_natIso e
  have hh : F.map (c.ι.app 0) ≫ β.hom =
      F.map (c.ι.app 0 ≫ ec.hom ≫ eS.inv) ≫ eT.hom := by
    simp only [β, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      Functor.map_comp, Category.assoc]
  clear_value β
  have hbase (V : Cᵒᵖ) :
      (c.ι.app 0 ≫ ec.hom ≫ eS.inv).val.app V (1 : R.obj.obj V) =
        (1 : S.obj.obj V) := by
    rw [← Category.assoc, hec]
    have : IsIso eS.hom.val := (SheafOfModules.forget _).map_isIso eS.hom
    apply (ModuleCat.mono_iff_injective (eS.hom.val.app V)).1 inferInstance
    have h := heS V (1 : ringedSectionLocalizationCarrier R (a t) V)
    have hi := congrArg (fun f ↦ f.val.app V
      ((ringedSectionLocalizationUnit R (a t)).val.app V (1 : R.obj.obj V))) eS.inv_hom_id
    change (eS.hom.val.app V)
      ((eS.inv.val.app V)
        ((ringedSectionLocalizationUnit R (a t)).val.app V (1 : R.obj.obj V))) =
      (ringedSectionLocalizationUnit R (a t)).val.app V (1 : R.obj.obj V) at hi
    apply hi.trans
    change ((PresheafOfModules.sheafificationAdjunction (𝟙 O.obj)).unit.app
      (ringedSectionLocalizationPresheaf R (a t))).app V
        ((1 : R.obj.obj V) • (1 : ringedSectionLocalizationCarrier R (a t) V)) = _
    rw [one_smul]
    simp only [map_one] at h
    convert h.symm using 1 <;> (with_unfolding_all rfl)
  have hzero : F.map (c.ι.app 0) ≫ β.hom = ε.hom ≫ η := by
    apply (cancel_epi ε.inv).1
    simp only [Iso.inv_hom_id_assoc]
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (F.map (c.ι.app 0) ≫ β.hom).val.app V (ε.inv.val.app V x) = η.val.app V x
    have hhi := congrArg (fun f ↦ f.val.app V (ε.inv.val.app V x)) hh
    apply hhi.trans
    have hn := SheafOfModules.tensorPresheafUnit_naturality
      (c.ι.app 0 ≫ ec.hom ≫ eS.inv) M
    have hn' := congrArg (fun f ↦ f.app V ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x)) hn
    have hb := congrArg (fun y ↦
      (SheafOfModules.tensorPresheafUnit _ M).app V (y ⊗ₜ[R.obj.obj V] x)) (hbase V)
    have hnorm := congrArg ((F.map (c.ι.app 0 ≫ ec.hom ≫ eS.inv)).val.app V)
      (hεinv V x)
    exact (congrArg (eT.hom.val.app V) (hnorm.trans (hn'.trans hb))).trans
      ((heT V 1 x).trans (by
        simpa only [eqToHom_refl, Functor.map_id, Category.comp_id] using (hη V x).symm))
  have hscalar : F.map ((SheafOfModules.unitHomEquiv X).symm
      ⟨(a t).val, (a t).property⟩) ≫ ε.hom = ε.hom ≫ (t • 𝟙 M) := by
    apply (cancel_epi ε.inv).1
    simp only [Iso.inv_hom_id_assoc]
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    subst src
    change ε.hom.val.app V
      ((F.map ((SheafOfModules.unitHomEquiv X).symm
        ⟨(a t).val, (a t).property⟩)).val.app V (ε.inv.val.app V x)) = (a t).val V • x
    exact regular_tensor_scalar_apply R M _ V x ((a t).val V) (by
      exact one_smul ((R.obj ⋙ forget₂ CommRingCat RingCat).obj V) _) ε (hεinv V)
  let Z := U.obj (SheafOfModules.changeOfRings.{u, u, u} φ M)
  let z : Z ⟶ Z := t • 𝟙 Z
  have hz : z = U.map ((algebraMap A (Localization.Away t) t) •
      𝟙 (SheafOfModules.changeOfRings.{u, u, u} φ M)) := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    subst src
    subst tgt
    change (a t).val V • x =
      (scalarLocalizationCoefficientMap A R a t
        (algebraMap A (Localization.Away t) t)).val V •
          (show (SheafOfModules.changeOfRings φ M).val.obj V from x)
    have hb : scalarLocalizationCoefficientMap A R a t
        (algebraMap A (Localization.Away t) t) =
        scalarLocalizationSectionsMap φ (a t) :=
      by
        unfold scalarLocalizationCoefficientMap
        exact IsLocalization.Away.lift_eq (S := Localization.Away t) t
          (scalarLocalizationSections_isUnit A R a t) t
    exact (congrArg (fun b ↦ b.val V •
      (show (SheafOfModules.changeOfRings φ M).val.obj V from x)) hb).symm
  exact tensor_scalar_colimit X _ M F ε t hscalar c hc U _ η β hzero
    (algebraMap A (Localization.Away t) t)
    (IsLocalization.Away.invSelf t : Localization.Away t)
    (IsLocalization.Away.mul_invSelf t) hz

end CategoryTheory
