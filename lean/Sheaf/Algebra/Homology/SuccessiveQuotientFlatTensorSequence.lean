/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Category.Ring.Sheaf.PrincipalPowerQuotients
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Flat-term successive quotient tensor sequences

Source: blueprint main-20261015, integral criterion reductions, second paragraph;
Stacks Project, Modules on Sites, Tags 03DA, 03EK, 03ER.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v r wB wR wS wPrev wN wOne
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings
namespace SheafOfModules

section SheafificationAPI

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{r}] {R : Sheaf J RingCat.{r}}

private theorem moduleSheafification_unit_naturality
    {P Q : PresheafOfModules.{r} R.obj} (f : P ⟶ Q) :
    (PresheafOfModules.sheafificationAdjunction.{r} (𝟙 R.obj)).unit.app P ≫
        ((PresheafOfModules.sheafification.{r} (𝟙 R.obj)).map f).val =
      f ≫ (PresheafOfModules.sheafificationAdjunction.{r} (𝟙 R.obj)).unit.app Q := by
  exact ((PresheafOfModules.sheafificationAdjunction.{r}
    (𝟙 R.obj)).unit.naturality f).symm

private theorem moduleSheafification_hom_ext
    (P : PresheafOfModules.{r} R.obj) (A : SheafOfModules.{r} R)
    {f g : (PresheafOfModules.sheafification.{r} (𝟙 R.obj)).obj P ⟶ A}
    (h : (PresheafOfModules.sheafificationAdjunction.{r} (𝟙 R.obj)).unit.app P ≫ f.val =
      (PresheafOfModules.sheafificationAdjunction.{r} (𝟙 R.obj)).unit.app P ≫ g.val) : f = g := by
  exact (PresheafOfModules.sheafificationHomEquiv.{r} (𝟙 R.obj)).injective h

end SheafificationAPI




section

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  [HasSheafify J CommRingCat.{r}]

section Models
variable {B S : Sheaf J CommRingCat.{r}} {φ : B ⟶ S}
  [HasDerivedCategory.{wB} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J B))]
  [HasDerivedCategory.{wS} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J S))]

/-- The termwise extension in the recorded derived-change-of-rings presentation.
Source: Stacks 06YY (blueprint: lem-pe-successive-quotient-linear-triangle). -/
def successiveQuotientTensorModel (F : DerivedChangeOfRingsCochainModel φ)
    (P : CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)) ℤ) :
    CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J S)) ℤ :=
  (F.E.mapHomologicalComplex (.up ℤ)).obj P

/-- A pure tensor in the presented extension, using its fixed object equality.
The existing scalar-first convention writes the paper's x tensor s as s tensor x.
Source: Stacks 03EK, 06YY (blueprint: lem-pe-successive-quotient-linear-triangle). -/
def successiveQuotientTensorSection (F : DerivedChangeOfRingsCochainModel φ)
    (M : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J B))
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) : (F.E.obj M).val.obj U :=
  (eqToHom (F.obj_eq M).symm).val.app U
    ((toSheafify J (changeOfRingsPresheaf φ M).presheaf).app U
      (s ⊗ₜ[B.obj.obj U, (φ.hom.app U).hom] x))

/-- Restrict the scalar action on every term and differential of the tensor model.
Source: Stacks 03D7, 06YY (blueprint: lem-pe-successive-quotient-linear-triangle). -/
def successiveQuotientRestrictedModel {A : Sheaf J CommRingCat.{r}} (a : A ⟶ S)
    (F : DerivedChangeOfRingsCochainModel φ)
    (P : CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)) ℤ) :
    CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J A)) ℤ :=
  (Functor.mapHomologicalComplex
    (restrictScalars ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map a))
    (.up ℤ)).obj (successiveQuotientTensorModel F P)
end Models

section FlatTensorData

variable {B SPrev SN SOne : Sheaf J CommRingCat.{r}}
  [HasDerivedCategory.{wB} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J B))]
  [HasDerivedCategory.{wPrev} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J SPrev))]
  [HasDerivedCategory.{wN} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J SN))]
  [HasDerivedCategory.{wOne} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J SOne))]

/-- Ordinary coefficient-linear cochain data, packaged before specializing the rings.
Source: blueprint, integral criterion reductions, second paragraph; Stacks 03ER, 03DA
(blueprint: lem-pe-successive-quotient-flat-tensor-sequence). -/
structure SuccessiveQuotientFlatTensorData
    (t : (B.obj ⋙ CategoryTheory.forget CommRingCat.{r}).sections)
    (πPrev : B ⟶ SPrev) (πN : B ⟶ SN) (πOne : B ⟶ SOne)
    (FPrev : DerivedChangeOfRingsCochainModel.{u, v, r, wB, wPrev} πPrev)
    (FN : DerivedChangeOfRingsCochainModel.{u, v, r, wB, wN} πN)
    (FOne : DerivedChangeOfRingsCochainModel.{u, v, r, wB, wOne} πOne)
    (P : CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)) ℤ) where
  /-- The preceding quotient projection. -/
  rPrev : SN ⟶ SPrev
  /-- The first quotient projection. -/
  rOne : SN ⟶ SOne
  /-- Compatibility with B for the preceding quotient. -/
  rPrev_projection : πN ≫ rPrev = πPrev
  /-- Compatibility with B for the first quotient. -/
  rOne_projection : πN ≫ rOne = πOne
  /-- Multiplication by the regular section, linear over SN. -/
  α : successiveQuotientRestrictedModel rPrev FPrev P ⟶ successiveQuotientTensorModel FN P
  /-- Reduction modulo the section, linear over SN. -/
  β : successiveQuotientTensorModel FN P ⟶ successiveQuotientRestrictedModel rOne FOne P
  /-- The composite vanishes. -/
  zero : α ≫ β = 0
  /-- The ordinary sequence is short exact. -/
  shortExact : (ShortComplex.mk α β zero).ShortExact
  /-- Multiplication on local coefficient classes. -/
  alpha_formula : ∀ (i : ℤ) (U : Cᵒᵖ) (b : B.obj.obj U) (x : (P.X i).val.obj U),
    (α.f i).val.app U (successiveQuotientTensorSection FPrev (P.X i) U
      (πPrev.hom.app U b) x) =
    successiveQuotientTensorSection FN (P.X i) U
      (πN.hom.app U ((@id (B.obj.obj U) (t.val U)) * b)) x
  /-- Reduction on local coefficient classes. -/
  beta_formula : ∀ (i : ℤ) (U : Cᵒᵖ) (b : B.obj.obj U) (x : (P.X i).val.obj U),
    (β.f i).val.app U (successiveQuotientTensorSection FN (P.X i) U (πN.hom.app U b) x) =
    successiveQuotientTensorSection FOne (P.X i) U (πOne.hom.app U b) x

end FlatTensorData

end


namespace SuccessiveQuotientCoefficients

variable {R : Type*} [CommRing R] (t : R) (n : ℕ) (hn : 1 ≤ n)
private abbrev I (k : ℕ) : Ideal R := Ideal.span {t ^ k}
include hn
private theorem mul_mem (x : R) (hx : x ∈ I t (n - 1)) : t * x ∈ I t n := by
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.1 hx
  apply Ideal.mem_span_singleton.2
  refine ⟨y, ?_⟩
  rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hn]
private def a : R ⧸ I t (n - 1) →ₗ[R] R ⧸ I t n :=
  (I t (n - 1)).mapQ (I t n) (LinearMap.mulLeft R t) (mul_mem t n hn)
private theorem ideal_le : I t n ≤ I t 1 := by
  apply Ideal.span_le.2
  intro x hx
  obtain rfl := Set.mem_singleton_iff.1 hx
  exact Ideal.mem_span_singleton.2 (pow_dvd_pow t hn)
private def b : R ⧸ I t n →ₗ[R] R ⧸ I t 1 :=
  (I t n).mapQ (I t 1) LinearMap.id (ideal_le t n hn)
private theorem zero_comp : (b t n hn).comp (a t n hn) = 0 := by
  apply Submodule.linearMap_qext
  apply LinearMap.ext
  intro x
  change Ideal.Quotient.mk (I t 1) (t * x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton.2 (by simp)
private theorem a_injective (ht : Function.Injective (fun x : R ↦ t * x)) :
    Function.Injective (a t n hn) := by
  apply (LinearMap.ker_eq_bot).1
  apply LinearMap.ker_eq_bot'.2
  intro x hx
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk (I t n) (t * x) = 0 at hx
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 hx)
  apply Ideal.Quotient.eq_zero_iff_mem.2
  apply Ideal.mem_span_singleton.2
  refine ⟨y, ht ?_⟩
  change t * x = t * (t ^ (n - 1) * y)
  rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hn]
  exact hy
private theorem b_surjective : Function.Surjective (b t n hn) := by
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk (I t n) x, rfl⟩
private theorem exact_ab : Function.Exact (a t n hn) (b t n hn) := by
  intro x
  constructor
  · intro hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk (I t 1) x = 0 at hx
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 hx)
    refine ⟨Ideal.Quotient.mk (I t (n - 1)) y, ?_⟩
    change Ideal.Quotient.mk (I t n) (t * y) = Ideal.Quotient.mk (I t n) x
    simpa only [pow_one] using congrArg (Ideal.Quotient.mk (I t n)) hy.symm
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun (zero_comp t n hn) y

end SuccessiveQuotientCoefficients

private instance scalarSheafification_additive
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify J AddCommGrpCat.{r}]
    {R₀ : Cᵒᵖ ⥤ RingCat.{r}} {R : Sheaf J RingCat.{r}} (a : R₀ ⟶ R.obj)
    [Presheaf.IsLocallyInjective J a] [Presheaf.IsLocallySurjective J a] :
    (PresheafOfModules.sheafification.{r} a).Additive :=
  (PresheafOfModules.sheafificationAdjunction.{r} a).left_adjoint_additive

section LeftTensorAuxiliary

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{r}]
  {B : Sheaf J CommRingCat.{r}}

private def leftTensorPresheaf
    (N : PresheafOfModules.{r} (B.obj ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.{r} (B.obj ⋙ forget₂ CommRingCat RingCat) ⥤
      PresheafOfModules.{r} (B.obj ⋙ forget₂ CommRingCat RingCat) where
  obj M := siteTensorPresheaf N M
  map f := siteTensorSecondMap N f
  map_id M := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    rfl
  map_comp f g := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    rfl

private instance leftTensorPresheaf_additive
    (N : PresheafOfModules.{r} (B.obj ⋙ forget₂ CommRingCat RingCat)) :
    (leftTensorPresheaf N).Additive where
  map_add {M M' f g} := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    change x ⊗ₜ[B.obj.obj U] ((f.app U) y + (g.app U) y) =
      x ⊗ₜ[B.obj.obj U] (f.app U) y + x ⊗ₜ[B.obj.obj U] (g.app U) y
    exact TensorProduct.tmul_add _ _ _

private def leftTensorSheaf
    (N : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) :
    SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B) ⥤
      SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B) :=
  forget _ ⋙ leftTensorPresheaf N.val ⋙ PresheafOfModules.sheafification.{r} (𝟙 _)

private instance leftTensorSheaf_additive
    (N : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) :
    (leftTensorSheaf N).Additive := by
  have : (PresheafOfModules.sheafification.{r}
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj B) (𝟙 _)).Additive :=
    scalarSheafification_additive (R := _) (𝟙 _)
  have : (leftTensorPresheaf N.val).Additive := leftTensorPresheaf_additive N.val
  dsimp only [leftTensorSheaf]
  infer_instance

private def leftTensorSheafMap
    {N N' : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)}
    (f : N ⟶ N') : leftTensorSheaf N ⟶ leftTensorSheaf N' where
  app M := (siteSheafTensorRight M).map f
  naturality {_M _M'} g := (siteSheafTensorSecondMap_naturality f g).symm

private theorem leftTensorSheafMap_comp
    {N N' N'' : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)}
    (f : N ⟶ N') (g : N' ⟶ N'') :
    leftTensorSheafMap (f ≫ g) = leftTensorSheafMap f ≫ leftTensorSheafMap g := by
  apply NatTrans.ext
  funext M
  exact (siteSheafTensorRight M).map_comp f g

private theorem leftTensorSheafMap_zero
    (N N' : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) :
    leftTensorSheafMap (0 : N ⟶ N') = 0 := by
  apply NatTrans.ext
  funext M
  exact (siteSheafTensorRight M).map_zero N N'

private theorem tensorMap_tmul
    {N N' : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)}
    (f : N ⟶ N')
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))
    (U : Cᵒᵖ) (y : N.val.obj U) (x : M.val.obj U) :
    ((siteSheafTensorRight M).map f).val.app U (siteSheafTensorTmul N M U y x) =
      siteSheafTensorTmul N' M U (f.val.app U y) x := by
  exact congrArg (fun k ↦ (k.app U) (y ⊗ₜ[B.obj.obj U] x))
    (moduleSheafification_unit_naturality
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj B)
      (siteTensorHom f.val M.val))

end LeftTensorAuxiliary

section RestrictedTensorAuxiliary

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]

private def restrictedTensorPresheafIso {R S : Sheaf J CommRingCat.{r}}
    (φ : R ⟶ S)
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    siteTensorPresheaf
      ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
        (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))).val M.val ≅
      (PresheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).obj
          (changeOfRingsPresheaf φ M) := by
  refine PresheafOfModules.isoMk (fun V ↦ ?_) ?_
  · let e :
        (siteTensorPresheaf
          ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
            (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))).val M.val).obj V ≃ₗ[
              R.obj.obj V]
          ((PresheafOfModules.restrictScalars
            ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).obj
              (changeOfRingsPresheaf φ M)).obj V :=
      { toFun := fun x ↦ x
        invFun := fun x ↦ x
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := by
          intro b z
          induction z using TensorProduct.induction_on with
          | zero => simp only [smul_zero]
          | tmul s x => rfl
          | add z z' hz hz' => simpa only [smul_add] using congrArg₂ (· + ·) hz hz' }
    exact e.toModuleIso
  · intro V W f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul s m =>
      change S.obj.map f s ⊗ₜ[R.obj.obj W, (φ.hom.app W).hom] M.val.map f m =
        changeOfRingsMap φ M f (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m)
      exact (Classical.choose_spec (exists_changeOfRingsMap φ M f) s m).symm

omit [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})] in
private theorem sheafificationComparison {R : Sheaf J RingCat.{r}}
    (P : PresheafOfModules.{r} R.obj) (A : SheafOfModules.{r} R)
    (φ : P ⟶ A.val)
    [hinj : PresheafOfModules.IsLocallyInjective J φ]
    [hsurj : PresheafOfModules.IsLocallySurjective J φ] :
    ∃ e : (PresheafOfModules.sheafification.{r} (𝟙 R.obj)).obj P ≅ A,
      (PresheafOfModules.sheafificationAdjunction.{r} (𝟙 R.obj)).unit.app P ≫
        e.hom.val = φ := by
  let S := (PresheafOfModules.sheafification.{r} (𝟙 R.obj)).obj P
  let η : P ⟶ S.val := (PresheafOfModules.sheafificationAdjunction.{r} (𝟙 R.obj)).unit.app P
  let g : S ⟶ A := (PresheafOfModules.sheafificationHomEquiv.{r} (𝟙 R.obj)).symm φ
  have hg : η ≫ g.val = φ := by
    exact (PresheafOfModules.sheafificationHomEquiv.{r} (𝟙 R.obj)).apply_symm_apply φ
  let f : A ⟶ S := ⟨(PresheafOfModules.homEquivOfIsLocallyBijective
    (f := φ) S.isSheaf).symm η⟩
  have hf : φ ≫ f.val = η := by
    exact (PresheafOfModules.homEquivOfIsLocallyBijective
      (f := φ) S.isSheaf).apply_symm_apply η
  have hfg : f ≫ g = 𝟙 A := by
    apply (SheafOfModules.fullyFaithfulForget _).map_injective
    apply (PresheafOfModules.homEquivOfIsLocallyBijective (f := φ) A.isSheaf).injective
    change φ ≫ (f.val ≫ g.val) = φ ≫ 𝟙 A.val
    rw [← Category.assoc, hf, hg, Category.comp_id]
  have hgf : g ≫ f = 𝟙 S := by
    apply moduleSheafification_hom_ext P S
    change η ≫ (g.val ≫ f.val) = η ≫ 𝟙 S.val
    rw [← Category.assoc, hg, hf, Category.comp_id]
  exact ⟨⟨g, f, hgf, hfg⟩, hg⟩


end RestrictedTensorAuxiliary

section OrdinaryExtensionAuxiliary

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}}

private def ordinaryExtensionPresheaf (a : R ⟶ S) :
    ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R) ⥤
      PresheafOfModules.{r} (derivedChangeRingIndependentCoefficients J S).obj where
  obj := changeOfRingsPresheaf a
  map f :=
    { app U := (ModuleCat.extendScalars (a.hom.app U).hom).map (f.val.app U)
      naturality := changeOfRingsHom_naturality a _ f }
  map_id M := by
    apply PresheafOfModules.hom_ext
    intro U
    simp
    rfl
  map_comp f g := by
    apply PresheafOfModules.hom_ext
    intro U
    simp

private instance ordinaryExtensionPresheaf_additive (a : R ⟶ S) :
    (ordinaryExtensionPresheaf a).Additive := by
  have (U : Cᵒᵖ) : (ModuleCat.extendScalars (a.hom.app U).hom).Additive :=
    (ModuleCat.extendRestrictScalarsAdj (a.hom.app U).hom).left_adjoint_additive
  constructor
  intro M N f g
  apply PresheafOfModules.hom_ext
  intro U
  simpa only [ordinaryExtensionPresheaf, SheafOfModules.add_val,
    PresheafOfModules.add_app] using
      (ModuleCat.extendScalars (a.hom.app U).hom).map_add
        (f := f.val.app U) (g := g.val.app U)

private def ordinaryExtension (a : R ⟶ S) :
    ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R) ⥤
      ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J S) :=
  ordinaryExtensionPresheaf a ⋙ PresheafOfModules.sheafification.{r}
    (𝟙 (derivedChangeRingIndependentCoefficients J S).obj)

private instance ordinaryExtension_additive (a : R ⟶ S) :
    (ordinaryExtension a).Additive := by
  have : (PresheafOfModules.sheafification.{r}
      (𝟙 (derivedChangeRingIndependentCoefficients J S).obj)).Additive :=
    (PresheafOfModules.sheafificationAdjunction.{r}
      (𝟙 (derivedChangeRingIndependentCoefficients J S).obj)).left_adjoint_additive
  dsimp only [ordinaryExtension]
  infer_instance

variable [HasSheafify J AddCommGrpCat.{r}]

private def modelOrdinaryIso {a : R ⟶ S}
    [HasDerivedCategory.{wR} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory.{wS} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J S))]
    (F : DerivedChangeOfRingsCochainModel a) : F.E ≅ ordinaryExtension a :=
  NatIso.ofComponents (fun M ↦ eqToIso (F.obj_eq M)) (by
    intro M N f
    simp only [eqToIso.hom, F.map_eq, Category.assoc, eqToHom_trans,
      eqToHom_refl, Category.comp_id]
    rfl)

end OrdinaryExtensionAuxiliary

section TensorExtensionNaturalityAuxiliary

variable {C : Type u} [Category.{v} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{r}]

private def tensorExtensionUnit {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    forget ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⋙
        leftTensorPresheaf
          ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).obj
            (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))).val ⟶
      (ordinaryExtension a ⋙
        restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)) ⋙
          forget ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) where
  app M := (restrictedTensorPresheafIso a M).hom ≫
    (PresheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map a).hom).map
      ((PresheafOfModules.sheafificationAdjunction.{r}
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).unit.app
          (changeOfRingsPresheaf a M))
  naturality {M N} f := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro s x
    change S.obj.obj U at s
    exact (congrArg (fun k ↦ (k.app U)
      (s ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x))
        ((PresheafOfModules.sheafificationAdjunction.{r}
          (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).unit.naturality
            ((ordinaryExtensionPresheaf a).map f)))

private instance tensorExtensionUnit_injective {R S : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S)
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    PresheafOfModules.IsLocallyInjective J ((tensorExtensionUnit a).app M) := by
  change Presheaf.IsLocallyInjective J
    ((PresheafOfModules.toPresheaf _).map (restrictedTensorPresheafIso a M).hom ≫
      toSheafify J (changeOfRingsPresheaf a M).presheaf)
  have : Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf _).map (restrictedTensorPresheafIso a M).hom) :=
    inferInstance
  have : Presheaf.IsLocallyInjective J
      (toSheafify J (changeOfRingsPresheaf a M).presheaf) := inferInstance
  infer_instance

private instance tensorExtensionUnit_surjective {R S : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S)
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    PresheafOfModules.IsLocallySurjective J ((tensorExtensionUnit a).app M) := by
  change Presheaf.IsLocallySurjective J
    ((PresheafOfModules.toPresheaf _).map (restrictedTensorPresheafIso a M).hom ≫
      toSheafify J (changeOfRingsPresheaf a M).presheaf)
  have : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf _).map (restrictedTensorPresheafIso a M).hom) :=
    inferInstance
  have : Presheaf.IsLocallySurjective J
      (toSheafify J (changeOfRingsPresheaf a M).presheaf) := inferInstance
  infer_instance

private theorem exists_extensionTensorIso {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    ∃ e : (leftTensorSheaf
      ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).obj
        (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)))).obj M ≅
      (ordinaryExtension a ⋙
        restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).obj M,
      (PresheafOfModules.sheafificationAdjunction.{r}
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app _ ≫
          e.hom.val = (tensorExtensionUnit a).app M := by
  exact sheafificationComparison
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
    _ _ ((tensorExtensionUnit a).app M)
    (hinj := tensorExtensionUnit_injective a M)
    (hsurj := tensorExtensionUnit_surjective a M)

private def extensionTensorIso {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (leftTensorSheaf
      ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).obj
        (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)))).obj M ≅
      (ordinaryExtension a ⋙
        restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).obj M :=
  (exists_extensionTensorIso a M).choose

private theorem extensionTensorIso_unit {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (PresheafOfModules.sheafificationAdjunction.{r}
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app _ ≫
        (extensionTensorIso a M).hom.val = (tensorExtensionUnit a).app M :=
  (exists_extensionTensorIso a M).choose_spec

private def tensorExtensionIso {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    leftTensorSheaf
        ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).obj
          (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))) ≅
      ordinaryExtension a ⋙
        restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a) :=
  NatIso.ofComponents (extensionTensorIso a) (by
    intro M N f
    let adj := PresheafOfModules.sheafificationAdjunction.{r}
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
    let N₀ := (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).obj
      (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    let T := leftTensorPresheaf (B := R) N₀.val
    apply moduleSheafification_hom_ext
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (T.obj M.val) _
    have hη : adj.unit.app (T.obj M.val) ≫ (leftTensorSheaf N₀ |>.map f).val =
        T.map f.val ≫ adj.unit.app (T.obj N.val) :=
      moduleSheafification_unit_naturality
        (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (T.map f.val)
    change adj.unit.app (T.obj M.val) ≫
        (leftTensorSheaf N₀ |>.map f).val ≫ (extensionTensorIso a N).hom.val =
      adj.unit.app (T.obj M.val) ≫ (extensionTensorIso a M).hom.val ≫
        ((ordinaryExtension a ⋙
          restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).map f).val
    have hM := extensionTensorIso_unit a M
    have hN := extensionTensorIso_unit a N
    change adj.unit.app (T.obj M.val) ≫ (extensionTensorIso a M).hom.val = _ at hM
    change adj.unit.app (T.obj N.val) ≫ (extensionTensorIso a N).hom.val = _ at hN
    rw [← Category.assoc, hη, Category.assoc, hN, ← Category.assoc, hM]
    exact (tensorExtensionUnit a).naturality f)

private theorem tensorExtensionIso_app_hom {R S : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S)
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (tensorExtensionIso a).hom.app M = (extensionTensorIso a M).hom := rfl

private theorem extensionTensorIso_tmul {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    ((extensionTensorIso a M).hom.val.app U)
      (siteSheafTensorTmul
        ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).obj
          (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))) M U s x) =
      (toSheafify J (changeOfRingsPresheaf a M).presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x) := by
  exact congrArg (fun k ↦ (k.app U)
    (s ⊗ₜ[R.obj.obj U] x)) (extensionTensorIso_unit a M)

variable [EssentiallySmall.{r} C]

variable [HasSheafify J AddCommGrpCat.{r}]

private def modelTensorIso {R S : Sheaf J CommRingCat.{r}} {a : R ⟶ S}
    [HasDerivedCategory.{wR} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory.{wS} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J S))]
    (F : DerivedChangeOfRingsCochainModel a) :
    leftTensorSheaf
        ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).obj
          (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))) ≅
      F.E ⋙ restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a) :=
  tensorExtensionIso a ≪≫ Functor.isoWhiskerRight (modelOrdinaryIso F).symm
    (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a))

private theorem modelTensorIso_hom {R S : Sheaf J CommRingCat.{r}} {a : R ⟶ S}
    [HasDerivedCategory.{wR} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory.{wS} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J S))]
    (F : DerivedChangeOfRingsCochainModel a)
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (modelTensorIso F).hom.app M = (extensionTensorIso a M).hom ≫
      (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).map
        (eqToHom (F.obj_eq M).symm) := by
  simp [modelTensorIso, tensorExtensionIso_app_hom, modelOrdinaryIso,
    Functor.isoWhiskerRight]

private theorem modelTensorIso_tmul {R S : Sheaf J CommRingCat.{r}} {a : R ⟶ S}
    [HasDerivedCategory.{wR} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory.{wS} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J S))]
    (F : DerivedChangeOfRingsCochainModel a)
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    ((modelTensorIso F).hom.app M).val.app U
      (siteSheafTensorTmul
        ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).obj
          (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))) M U s x) =
      (eqToHom (F.obj_eq M).symm).val.app U
        ((toSheafify J (changeOfRingsPresheaf a M).presheaf).app U
          (s ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x)) := by
  rw [modelTensorIso_hom]
  exact congrArg ((eqToHom (F.obj_eq M).symm).val.app U)
    (extensionTensorIso_tmul a M U s x)

end TensorExtensionNaturalityAuxiliary

section ExactRestrictionAuxiliary

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]

-- This is the general-ring version of systemScalarRestriction_exact. Both composites
-- with toSheaf retain the same underlying abelian sheaf and every morphism.
private theorem restriction_exact {R S : Sheaf J RingCat.{r}} (a : R ⟶ S) :
    PreservesFiniteLimits (restrictScalars.{r} a) ∧
      PreservesFiniteColimits (restrictScalars.{r} a) := by
  let F := restrictScalars.{r} a
  have : PreservesFiniteLimits (F ⋙ toSheaf R) := by
    change PreservesFiniteLimits (toSheaf S)
    infer_instance
  have : PreservesFiniteColimits (F ⋙ toSheaf R) := by
    change PreservesFiniteColimits (toSheaf S)
    infer_instance
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves F (toSheaf R),
    preservesFiniteColimits_of_reflects_of_preserves F (toSheaf R)⟩

omit [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}] in
private theorem restriction_faithful {R S : Sheaf J RingCat.{r}} (a : R ⟶ S) :
    (restrictScalars.{r} a).Faithful := by
  let F := restrictScalars.{r} a
  have : (F ⋙ toSheaf R).Faithful := by
    change (toSheaf S).Faithful
    infer_instance
  exact Functor.Faithful.of_comp F (toSheaf R)

private def liftRestrictedHom {R S : Sheaf J RingCat.{r}} (a : R ⟶ S)
    [Presheaf.IsLocallySurjective J a.hom] {M N : SheafOfModules.{r} S}
    (f : (restrictScalars a).obj M ⟶ (restrictScalars a).obj N) : M ⟶ N :=
  ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective a.hom N.isSheaf).symm f.val⟩

omit [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}] in
private theorem restrict_liftRestrictedHom {R S : Sheaf J RingCat.{r}} (a : R ⟶ S)
    [Presheaf.IsLocallySurjective J a.hom] {M N : SheafOfModules.{r} S}
    (f : (restrictScalars a).obj M ⟶ (restrictScalars a).obj N) :
    (restrictScalars a).map (liftRestrictedHom a f) = f := by
  rfl

omit [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}] in
private theorem restriction_full {R S : Sheaf J RingCat.{r}} (a : R ⟶ S)
    [Presheaf.IsLocallySurjective J a.hom] : (restrictScalars.{r} a).Full where
  map_surjective f := ⟨liftRestrictedHom a f, restrict_liftRestrictedHom a f⟩

private def restrictionComp {R S T : Sheaf J RingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (c : R ⟶ T) (h : a ≫ b = c) :
    restrictScalars.{r} b ⋙ restrictScalars a ≅ restrictScalars c := by
  have hU (U : Cᵒᵖ) : (b.hom.app U).hom.comp (a.hom.app U).hom =
      (c.hom.app U).hom :=
    congrArg RingCat.Hom.hom (congr_app (congrArg (fun k ↦ k.hom) h) U)
  refine NatIso.ofComponents (fun M ↦ (fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (a.hom.app U).hom (b.hom.app U).hom
        (c.hom.app U).hom (hU U).symm (M.val.obj U)).symm) ?_)) ?_
  · intro U V f
    ext x
    rfl
  · intro M N f
    ext U x
    rfl

end ExactRestrictionAuxiliary

section EndpointModelAuxiliary

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]

private def endpointModelIso {B S SN : Sheaf J CommRingCat.{r}}
    {π : B ⟶ S} (πN : B ⟶ SN) (rS : SN ⟶ S) (hπ : πN ≫ rS = π)
    [HasDerivedCategory.{wR} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B))]
    [HasDerivedCategory.{wS} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J S))]
    (F : DerivedChangeOfRingsCochainModel π) :
    leftTensorSheaf
        ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map π)).obj
          (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))) ≅
      (F.E ⋙ restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map rS)) ⋙
        restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map πN) := by
  let U := sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})
  have h : U.map πN ≫ U.map rS = U.map π := by
    rw [← U.map_comp, hπ]
  let c : restrictScalars (U.map rS) ⋙ restrictScalars (U.map πN) ≅
      restrictScalars (U.map π) :=
    restrictionComp (U.map πN) (U.map rS) (U.map π) h
  exact modelTensorIso F ≪≫ (Functor.isoWhiskerLeft F.E c).symm ≪≫
    (Functor.associator F.E (restrictScalars (U.map rS))
      (restrictScalars (U.map πN))).symm

private theorem endpointModelIso_tmul {B S SN : Sheaf J CommRingCat.{r}}
    {π : B ⟶ S} (πN : B ⟶ SN) (rS : SN ⟶ S) (hπ : πN ≫ rS = π)
    [HasDerivedCategory.{wR} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B))]
    [HasDerivedCategory.{wS} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J S))]
    (F : DerivedChangeOfRingsCochainModel π)
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    ((endpointModelIso πN rS hπ F).hom.app M).val.app U
      (siteSheafTensorTmul
        ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map π)).obj
          (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))) M U s x) =
      (eqToHom (F.obj_eq M).symm).val.app U
        ((toSheafify J (changeOfRingsPresheaf π M).presheaf).app U
          (s ⊗ₜ[B.obj.obj U, (π.hom.app U).hom] x)) := by
  change ((modelTensorIso F).hom.app M).val.app U _ = _
  exact modelTensorIso_tmul F M U s x

end EndpointModelAuxiliary

section CochainAuxiliary

variable {A : Type*} [Category A] [Abelian A]
  {D : Type*} [Category D] [Abelian D]
  (E₁ E₂ E₃ : A ⥤ D) [E₁.Additive] [E₂.Additive] [E₃.Additive]
  (a : E₁ ⟶ E₂) (b : E₂ ⟶ E₃) (wab : a ≫ b = 0)
  (P : CochainComplex A ℤ)

private def cochainSequence : ShortComplex (CochainComplex D ℤ) :=
  ShortComplex.mk ((a.mapHomologicalComplex (.up ℤ)).app P)
    ((b.mapHomologicalComplex (.up ℤ)).app P) (by
      ext i : 1
      exact NatTrans.congr_app wab (P.X i))

private theorem cochainSequence_shortExact
    (h : ∀ i : ℤ, (ShortComplex.mk (a.app (P.X i)) (b.app (P.X i))
      (NatTrans.congr_app wab (P.X i))).ShortExact) :
    (cochainSequence E₁ E₂ E₃ a b wab P).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  exact h i

end CochainAuxiliary

private theorem lift_shortExact
    {A D : Type*} [Category A] [Category D] [Abelian A] [Abelian D]
    (F : A ⥤ D) [F.Additive] [F.Full] [F.Faithful]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X₁ X₂ X₃ : A} (a : F.obj X₁ ⟶ F.obj X₂) (b : F.obj X₂ ⟶ F.obj X₃)
    (hab : a ≫ b = 0) (hS : (ShortComplex.mk a b hab).ShortExact) :
    ∃ (α : X₁ ⟶ X₂) (β : X₂ ⟶ X₃) (hαβ : α ≫ β = 0),
      (ShortComplex.mk α β hαβ).ShortExact ∧ F.map α = a ∧ F.map β = b := by
  let α := F.preimage a
  let β := F.preimage b
  have hαβ : α ≫ β = 0 := by
    apply F.map_injective
    simpa only [α, β, Functor.map_comp, Functor.map_preimage, Functor.map_zero] using hab
  let S := ShortComplex.mk α β hαβ
  have hSF : (S.map F).ShortExact := by
    change (ShortComplex.mk (F.map α) (F.map β) _).ShortExact
    simpa only [α, β, Functor.map_preimage] using hS
  have hSA : S.ShortExact := by
    exact { exact := (S.exact_map_iff_of_faithful F).1 hSF.exact
            mono_f := F.mono_of_mono_map hSF.mono_f
            epi_g := F.epi_of_epi_map hSF.epi_g }
  exact ⟨α, β, hαβ, hSA, F.map_preimage a, F.map_preimage b⟩

section FlatTensorAssembly

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {B SPrev SN SOne : Sheaf J CommRingCat.{r}}
  [HasDerivedCategory.{wB} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J B))]
  [HasDerivedCategory.{wPrev} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J SPrev))]
  [HasDerivedCategory.{wN} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J SN))]
  [HasDerivedCategory.{wOne} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J SOne))]

private theorem flatTensorData_of_sequence
    (t : (B.obj ⋙ CategoryTheory.forget CommRingCat.{r}).sections)
    (πPrev : B ⟶ SPrev) (πN : B ⟶ SN) (πOne : B ⟶ SOne)
    [Presheaf.IsLocallySurjective J
      (((sheafCompose J (forget₂ CommRingCat RingCat)).map πN).hom)]
    (FPrev : DerivedChangeOfRingsCochainModel.{u, v, r, wB, wPrev} πPrev)
    (FN : DerivedChangeOfRingsCochainModel.{u, v, r, wB, wN} πN)
    (FOne : DerivedChangeOfRingsCochainModel.{u, v, r, wB, wOne} πOne)
    (P : CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)) ℤ)
    (rPrev : SN ⟶ SPrev) (rOne : SN ⟶ SOne)
    (hrPrev : πN ≫ rPrev = πPrev) (hrOne : πN ≫ rOne = πOne)
    (S : ShortComplex (CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)) ℤ)) (hS : S.ShortExact)
    (ePrev : S.X₁ ≅ ((restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map πN)).mapHomologicalComplex
        (.up ℤ)).obj (successiveQuotientRestrictedModel rPrev FPrev P))
    (eN : S.X₂ ≅ ((restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map πN)).mapHomologicalComplex
        (.up ℤ)).obj (successiveQuotientTensorModel FN P))
    (eOne : S.X₃ ≅ ((restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map πN)).mapHomologicalComplex
        (.up ℤ)).obj (successiveQuotientRestrictedModel rOne FOne P))
    (zPrev : ∀ (i : ℤ) (U : Cᵒᵖ), B.obj.obj U → (P.X i).val.obj U → (S.X₁.X i).val.obj U)
    (zN : ∀ (i : ℤ) (U : Cᵒᵖ), B.obj.obj U → (P.X i).val.obj U → (S.X₂.X i).val.obj U)
    (zOne : ∀ (i : ℤ) (U : Cᵒᵖ), B.obj.obj U → (P.X i).val.obj U → (S.X₃.X i).val.obj U)
    (hα : ∀ (i : ℤ) (U : Cᵒᵖ) (b : B.obj.obj U) (x : (P.X i).val.obj U),
      (S.f.f i).val.app U (zPrev i U b x) = zN i U ((@id (B.obj.obj U) (t.val U)) * b) x)
    (hβ : ∀ (i : ℤ) (U : Cᵒᵖ) (b : B.obj.obj U) (x : (P.X i).val.obj U),
      (S.g.f i).val.app U (zN i U b x) = zOne i U b x)
    (hPrev : ∀ (i : ℤ) (U : Cᵒᵖ) (b : B.obj.obj U) (x : (P.X i).val.obj U),
      (ePrev.hom.f i).val.app U (zPrev i U b x) =
        successiveQuotientTensorSection FPrev (P.X i) U (πPrev.hom.app U b) x)
    (hN : ∀ (i : ℤ) (U : Cᵒᵖ) (b : B.obj.obj U) (x : (P.X i).val.obj U),
      (eN.hom.f i).val.app U (zN i U b x) =
        successiveQuotientTensorSection FN (P.X i) U (πN.hom.app U b) x)
    (hOne : ∀ (i : ℤ) (U : Cᵒᵖ) (b : B.obj.obj U) (x : (P.X i).val.obj U),
      (eOne.hom.f i).val.app U (zOne i U b x) =
        successiveQuotientTensorSection FOne (P.X i) U (πOne.hom.app U b) x) :
    Nonempty (SuccessiveQuotientFlatTensorData t πPrev πN πOne FPrev FN FOne P) := by
  let R := restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map πN)
  have : R.Full := restriction_full
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map πN)
  have : R.Faithful := restriction_faithful
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map πN)
  have : PreservesFiniteLimits R := (restriction_exact
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map πN)).1
  have : PreservesFiniteColimits R := (restriction_exact
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map πN)).2
  let V := R.mapHomologicalComplex (.up ℤ)
  let XPrev := successiveQuotientRestrictedModel rPrev FPrev P
  let XN := successiveQuotientTensorModel FN P
  let XOne := successiveQuotientRestrictedModel rOne FOne P
  let aB : V.obj XPrev ⟶ V.obj XN := ePrev.inv ≫ S.f ≫ eN.hom
  let bB : V.obj XN ⟶ V.obj XOne := eN.inv ≫ S.g ≫ eOne.hom
  have waB : aB ≫ bB = 0 := by
    calc
      aB ≫ bB = ePrev.inv ≫ (S.f ≫ S.g) ≫ eOne.hom := by
        simp [aB, bB, Category.assoc]
      _ = 0 := by rw [S.zero]; simp
  have hSB : (ShortComplex.mk aB bB waB).ShortExact := by
    let eS : S ≅ ShortComplex.mk aB bB waB :=
      ShortComplex.isoMk ePrev eN eOne
        (by simp [aB]) (by simp [bB])
    exact ShortComplex.shortExact_of_iso eS hS
  obtain ⟨α, β, hab, hSES, hαmap, hβmap⟩ :=
    lift_shortExact V (X₁ := XPrev) (X₂ := XN) (X₃ := XOne) aB bB waB hSB
  refine ⟨{
    rPrev := rPrev
    rOne := rOne
    rPrev_projection := hrPrev
    rOne_projection := hrOne
    α := α
    β := β
    zero := hab
    shortExact := hSES
    alpha_formula := ?_
    beta_formula := ?_ }⟩
  · intro i U b x
    have hc : (ePrev.inv.f i).val.app U ((ePrev.hom.f i).val.app U (zPrev i U b x)) =
        zPrev i U b x :=
      congrArg (fun k ↦ (k.f i).val.app U (zPrev i U b x)) ePrev.hom_inv_id
    have hm := congrArg (fun k ↦ (k.f i).val.app U
      ((ePrev.hom.f i).val.app U (zPrev i U b x))) hαmap
    change (α.f i).val.app U ((ePrev.hom.f i).val.app U (zPrev i U b x)) =
      (eN.hom.f i).val.app U ((S.f.f i).val.app U
        ((ePrev.inv.f i).val.app U ((ePrev.hom.f i).val.app U (zPrev i U b x)))) at hm
    rw [hc, hα, hPrev, hN] at hm
    exact hm
  · intro i U b x
    have hc : (eN.inv.f i).val.app U ((eN.hom.f i).val.app U (zN i U b x)) = zN i U b x :=
      congrArg (fun k ↦ (k.f i).val.app U (zN i U b x)) eN.hom_inv_id
    have hm := congrArg (fun k ↦ (k.f i).val.app U
      ((eN.hom.f i).val.app U (zN i U b x))) hβmap
    change (β.f i).val.app U ((eN.hom.f i).val.app U (zN i U b x)) =
      (eOne.hom.f i).val.app U ((S.g.f i).val.app U
        ((eN.inv.f i).val.app U ((eN.hom.f i).val.app U (zN i U b x)))) at hm
    rw [hc, hβ, hN, hOne] at hm
    exact hm

end FlatTensorAssembly


variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  [HasSheafify J CommRingCat.{r}]
  (B : Sheaf J CommRingCat.{r})
  (t : (B.obj ⋙ CategoryTheory.forget CommRingCat.{r}).sections)

omit [EssentiallySmall.{r} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  [HasSheafify J CommRingCat.{r}] in
private theorem powerIdeal_le (m n : ℕ) (h : m ≤ n) (U : Cᵒᵖ) :
    sectionPowerIdeal B t n U ≤ sectionPowerIdeal B t m U := by
  apply Ideal.span_le.2
  intro x hx
  obtain rfl := Set.mem_singleton_iff.1 hx
  apply Ideal.mem_span_singleton.2
  exact pow_dvd_pow _ h

private def quotientTransitionPresheaf (m n : ℕ) (h : m ≤ n) :
    sectionPowerQuotientPresheaf B t n ⟶ sectionPowerQuotientPresheaf B t m where
  app U := CommRingCat.ofHom (Ideal.Quotient.factor (powerIdeal_le B t m n h U))
  naturality {U V} f := by
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext x
    rfl

private def quotientTransition (m n : ℕ) (h : m ≤ n) :
    principalPowerRingQuotient B t n ⟶ principalPowerRingQuotient B t m := by
  unfold principalPowerRingQuotient
  exact (presheafToSheaf J CommRingCat.{r}).map (quotientTransitionPresheaf B t m n h)

omit [EssentiallySmall.{r} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}] in
private theorem quotientTransition_projection (m n : ℕ) (h : m ≤ n) :
    principalPowerRingProjection B t n ≫ quotientTransition B t m n h =
      principalPowerRingProjection B t m := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro b
  unfold principalPowerRingQuotient at *
  exact (congrArg (fun k ↦ (k.app U)
    (Ideal.Quotient.mk (sectionPowerIdeal B t n U) b))
      (toSheafify_naturality J (quotientTransitionPresheaf B t m n h))).symm

private abbrev coefficientRingPresheaf (n : ℕ) : Cᵒᵖ ⥤ RingCat.{r} :=
  sectionPowerQuotientPresheaf B t n ⋙ forget₂ CommRingCat RingCat

private instance quotientLocallyBijectiveCommRing :
    J.WEqualsLocallyBijective CommRingCat.{r} := by
  let : PreservesFilteredColimitsOfSize.{r, r}
      (CategoryTheory.forget CommRingCat.{r}) := preservesFilteredColimitsOfSize_shrink _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall J

private def rawCoefficientB (j : ℕ) :
    PresheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj :=
  (PresheafOfModules.restrictScalars
    (Functor.whiskerRight (sectionPowerQuotientProjection B t j)
      (forget₂ CommRingCat RingCat))).obj
    (PresheafOfModules.unit (coefficientRingPresheaf B t j))

private def rawAlphaB (n : ℕ) (hn : 1 ≤ n) :
    rawCoefficientB B t (n - 1) ⟶ rawCoefficientB B t n where
  app U := ModuleCat.ofHom
    (X := (rawCoefficientB B t (n - 1)).obj U)
    (Y := (rawCoefficientB B t n).obj U)
    { toFun := SuccessiveQuotientCoefficients.a (@id (B.obj.obj U) (t.val U)) n hn
      map_add' :=
        (SuccessiveQuotientCoefficients.a (@id (B.obj.obj U) (t.val U)) n hn).map_add
      map_smul' b x := by
        change B.obj.obj U at b
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        change Ideal.Quotient.mk (sectionPowerIdeal B t n U)
            ((@id (B.obj.obj U) (t.val U)) * (b * x)) =
          Ideal.Quotient.mk (sectionPowerIdeal B t n U)
            (b * ((@id (B.obj.obj U) (t.val U)) * x))
        exact congrArg (Ideal.Quotient.mk _) (mul_left_comm _ _ _) }
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk (sectionPowerIdeal B t n V)
        ((@id (B.obj.obj V) (t.val V)) * B.obj.map f x) =
      Ideal.Quotient.mk (sectionPowerIdeal B t n V)
        (B.obj.map f ((@id (B.obj.obj U) (t.val U)) * x))
    simp only [map_mul]
    rw [show B.obj.map f (@id (B.obj.obj U) (t.val U)) =
      @id (B.obj.obj V) (t.val V) from t.property f]

private def rawBetaB (n : ℕ) (hn : 1 ≤ n) :
    rawCoefficientB B t n ⟶ rawCoefficientB B t 1 where
  app U := ModuleCat.ofHom
    (X := (rawCoefficientB B t n).obj U)
    (Y := (rawCoefficientB B t 1).obj U)
    { toFun := SuccessiveQuotientCoefficients.b (@id (B.obj.obj U) (t.val U)) n hn
      map_add' :=
        (SuccessiveQuotientCoefficients.b (@id (B.obj.obj U) (t.val U)) n hn).map_add
      map_smul' b x := by
        change B.obj.obj U at b
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        rfl }
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

private def rawCoefficientBSequence (n : ℕ) (hn : 1 ≤ n) :
    ShortComplex (PresheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj) :=
  ShortComplex.mk (rawAlphaB B t n hn) (rawBetaB B t n hn) (by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    ext x
    exact LinearMap.congr_fun
      (SuccessiveQuotientCoefficients.zero_comp (@id (B.obj.obj U) (t.val U)) n hn) x)

omit [EssentiallySmall.{r} C]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  [HasSheafify J CommRingCat.{r}] in
private theorem rawCoefficientBSequence_shortExact (n : ℕ) (hn : 1 ≤ n)
    (ht : ∀ U : Cᵒᵖ, Function.Injective
      (fun b : B.obj.obj U ↦ (@id (B.obj.obj U) (t.val U)) * b)) :
    (rawCoefficientBSequence B t n hn).ShortExact := by
  let S := rawCoefficientBSequence B t n hn
  have hpoint (U : Cᵒᵖ) :
      (S.map (PresheafOfModules.evaluation
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj U)).ShortExact := by
    refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
    · apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
      exact SuccessiveQuotientCoefficients.exact_ab
        (@id (B.obj.obj U) (t.val U)) n hn
    · apply (ModuleCat.mono_iff_injective _).2
      exact SuccessiveQuotientCoefficients.a_injective
        (@id (B.obj.obj U) (t.val U)) n hn (ht U)
    · apply (ModuleCat.epi_iff_surjective _).2
      exact SuccessiveQuotientCoefficients.b_surjective
        (@id (B.obj.obj U) (t.val U)) n hn
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply ShortComplex.exact_of_f_is_kernel
    apply PresheafOfModules.evaluationJointlyReflectsLimits
    intro U
    exact (CategoryTheory.Limits.KernelFork.isLimitMapConeEquiv
      (CategoryTheory.Limits.KernelFork.ofι S.f S.zero)
      (PresheafOfModules.evaluation
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj U)).symm
        (hpoint U).fIsKernel
  · apply PresheafOfModules.mono_of_injective
    intro U
    exact SuccessiveQuotientCoefficients.a_injective
      (@id (B.obj.obj U) (t.val U)) n hn (ht U)
  · apply PresheafOfModules.epi_of_surjective
    intro U
    exact SuccessiveQuotientCoefficients.b_surjective
      (@id (B.obj.obj U) (t.val U)) n hn

private def quotientCoefficientB (j : ℕ) :
    SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B) :=
  (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map
    (principalPowerRingProjection B t j))).obj
    (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
      (principalPowerRingQuotient B t j)))

private def rawCoefficientBUnit (j : ℕ) :
    rawCoefficientB B t j ⟶ (quotientCoefficientB B t j).val where
  app U := by
    unfold quotientCoefficientB principalPowerRingQuotient
    exact ModuleCat.ofHom
      (X := (rawCoefficientB B t j).obj U)
      (Y := (ModuleCat.restrictScalars
        (((toSheafify J (sectionPowerQuotientPresheaf B t j)).app U).hom.comp
          (Ideal.Quotient.mk (sectionPowerIdeal B t j U)))).obj
            (ModuleCat.of ((sheafify J (sectionPowerQuotientPresheaf B t j)).obj U)
              ((sheafify J (sectionPowerQuotientPresheaf B t j)).obj U)))
      { toFun := fun x ↦ (toSheafify J (sectionPowerQuotientPresheaf B t j)).app U x
        map_add' := ((toSheafify J (sectionPowerQuotientPresheaf B t j)).app U).hom.map_add
        map_smul' b x := by
          change B.obj.obj U at b
          change B.obj.obj U ⧸ sectionPowerIdeal B t j U at x
          change (toSheafify J (sectionPowerQuotientPresheaf B t j)).app U
              (Ideal.Quotient.mk (sectionPowerIdeal B t j U) b * x) =
            (toSheafify J (sectionPowerQuotientPresheaf B t j)).app U
              (Ideal.Quotient.mk (sectionPowerIdeal B t j U) b) *
                (toSheafify J (sectionPowerQuotientPresheaf B t j)).app U x
          exact map_mul _ _ _ }
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    ext x
    unfold quotientCoefficientB principalPowerRingQuotient at *
    exact ConcreteCategory.congr_hom
      ((toSheafify J (sectionPowerQuotientPresheaf B t j)).naturality f) x

private instance rawCoefficientBUnit_injective (j : ℕ) :
    PresheafOfModules.IsLocallyInjective J (rawCoefficientBUnit B t j) := by
  constructor
  intro U x y h
  unfold rawCoefficientBUnit quotientCoefficientB principalPowerRingQuotient at h
  exact Presheaf.equalizerSieve_mem J
    (toSheafify J (sectionPowerQuotientPresheaf B t j)) x y h

private instance rawCoefficientBUnit_surjective (j : ℕ) :
    PresheafOfModules.IsLocallySurjective J (rawCoefficientBUnit B t j) := by
  constructor
  intro U x
  unfold quotientCoefficientB principalPowerRingQuotient at x
  unfold rawCoefficientBUnit quotientCoefficientB principalPowerRingQuotient
  exact Presheaf.imageSieve_mem J
    (toSheafify J (sectionPowerQuotientPresheaf B t j)) x


private theorem exists_coefficientSheafificationIso (j : ℕ) :
    ∃ e : (PresheafOfModules.sheafification.{r}
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj)).obj
        (rawCoefficientB B t j) ≅ quotientCoefficientB B t j,
      (PresheafOfModules.sheafificationAdjunction.{r}
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj)).unit.app
          (rawCoefficientB B t j) ≫ e.hom.val = rawCoefficientBUnit B t j := by
  exact sheafificationComparison (rawCoefficientB B t j) (quotientCoefficientB B t j)
    (rawCoefficientBUnit B t j)
    (hinj := rawCoefficientBUnit_injective B t j)
    (hsurj := rawCoefficientBUnit_surjective B t j)

private def coefficientSheafificationIso (j : ℕ) :
    (PresheafOfModules.sheafification.{r}
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj)).obj
        (rawCoefficientB B t j) ≅ quotientCoefficientB B t j :=
  (exists_coefficientSheafificationIso B t j).choose

private theorem coefficientSheafificationIso_unit (j : ℕ) :
    (PresheafOfModules.sheafificationAdjunction.{r}
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj)).unit.app
        (rawCoefficientB B t j) ≫ (coefficientSheafificationIso B t j).hom.val =
      rawCoefficientBUnit B t j :=
  (exists_coefficientSheafificationIso B t j).choose_spec

private def coefficientAlphaB (n : ℕ) (hn : 1 ≤ n) :
    quotientCoefficientB B t (n - 1) ⟶ quotientCoefficientB B t n :=
  (coefficientSheafificationIso B t (n - 1)).inv ≫
    (PresheafOfModules.sheafification.{r}
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj)).map
        (rawAlphaB B t n hn) ≫ (coefficientSheafificationIso B t n).hom

private def coefficientBetaB (n : ℕ) (hn : 1 ≤ n) :
    quotientCoefficientB B t n ⟶ quotientCoefficientB B t 1 :=
  (coefficientSheafificationIso B t n).inv ≫
    (PresheafOfModules.sheafification.{r}
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj)).map
        (rawBetaB B t n hn) ≫ (coefficientSheafificationIso B t 1).hom

private theorem coefficientAlphaB_comp_beta (n : ℕ) (hn : 1 ≤ n) :
    coefficientAlphaB B t n hn ≫ coefficientBetaB B t n hn = 0 := by
  let F := PresheafOfModules.sheafification.{r}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj)
  change (_ ≫ F.map _ ≫ _) ≫ (_ ≫ F.map _ ≫ _) = 0
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← F.map_comp_assoc]
  have hz : rawAlphaB B t n hn ≫ rawBetaB B t n hn = 0 :=
    (rawCoefficientBSequence B t n hn).zero
  rw [hz, F.map_zero]
  simp

private def coefficientBSequence (n : ℕ) (hn : 1 ≤ n) :
    ShortComplex (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) :=
  ShortComplex.mk (coefficientAlphaB B t n hn) (coefficientBetaB B t n hn)
    (coefficientAlphaB_comp_beta B t n hn)

private theorem coefficientBSequence_shortExact (n : ℕ) (hn : 1 ≤ n)
    (ht : ∀ U : Cᵒᵖ, Function.Injective
      (fun b : B.obj.obj U ↦ (@id (B.obj.obj U) (t.val U)) * b)) :
    (coefficientBSequence B t n hn).ShortExact := by
  let F := PresheafOfModules.sheafification.{r}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj)
  let e : (rawCoefficientBSequence B t n hn).map F ≅ coefficientBSequence B t n hn :=
    ShortComplex.isoMk (coefficientSheafificationIso B t (n - 1))
      (coefficientSheafificationIso B t n) (coefficientSheafificationIso B t 1)
      (by simp [F, rawCoefficientBSequence, coefficientBSequence, coefficientAlphaB])
      (by simp [F, rawCoefficientBSequence, coefficientBSequence, coefficientBetaB])
  exact ShortComplex.shortExact_of_iso e
    ((rawCoefficientBSequence_shortExact B t n hn ht).map_of_exact F)

private instance principalProjection_locallySurjective (j : ℕ) :
    Presheaf.IsLocallySurjective J
      (((sheafCompose J (forget₂ CommRingCat RingCat)).map
        (principalPowerRingProjection B t j)).hom) := by
  have : Presheaf.IsLocallySurjective J (sectionPowerQuotientProjection B t j) := by
    apply Presheaf.isLocallySurjective_of_surjective
    intro U
    exact Ideal.Quotient.mk_surjective
  unfold principalPowerRingProjection principalPowerRingQuotient
  apply (Presheaf.isLocallySurjective_iff_whisker_forget J _).2
  change Presheaf.IsLocallySurjective J (Functor.whiskerRight
    (sectionPowerQuotientProjection B t j ≫
      toSheafify J (sectionPowerQuotientPresheaf B t j)) (CategoryTheory.forget CommRingCat))
  infer_instance

private theorem coefficientAlphaB_unit (n : ℕ) (hn : 1 ≤ n) :
    rawCoefficientBUnit B t (n - 1) ≫ (coefficientAlphaB B t n hn).val =
      rawAlphaB B t n hn ≫ rawCoefficientBUnit B t n := by
  let F := PresheafOfModules.sheafification.{r}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj)
  let adj := PresheafOfModules.sheafificationAdjunction.{r}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj)
  calc
    _ = (adj.unit.app (rawCoefficientB B t (n - 1)) ≫
        (coefficientSheafificationIso B t (n - 1)).hom.val) ≫
          (coefficientAlphaB B t n hn).val := by
      rw [coefficientSheafificationIso_unit]
    _ = adj.unit.app (rawCoefficientB B t (n - 1)) ≫
        ((coefficientSheafificationIso B t (n - 1)).hom ≫
          coefficientAlphaB B t n hn).val := by
      rw [SheafOfModules.comp_val, Category.assoc]
    _ = adj.unit.app (rawCoefficientB B t (n - 1)) ≫
        (F.map (rawAlphaB B t n hn) ≫ (coefficientSheafificationIso B t n).hom).val := by
      simp only [coefficientAlphaB, Iso.hom_inv_id_assoc]
      rfl
    _ = (rawAlphaB B t n hn ≫ adj.unit.app (rawCoefficientB B t n)) ≫
        (coefficientSheafificationIso B t n).hom.val := by
      rw [SheafOfModules.comp_val, ← Category.assoc]
      exact congrArg (fun k ↦ k ≫ (coefficientSheafificationIso B t n).hom.val)
        (moduleSheafification_unit_naturality
          (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj B) (rawAlphaB B t n hn))
    _ = _ := by rw [Category.assoc, coefficientSheafificationIso_unit]

private theorem coefficientBetaB_unit (n : ℕ) (hn : 1 ≤ n) :
    rawCoefficientBUnit B t n ≫ (coefficientBetaB B t n hn).val =
      rawBetaB B t n hn ≫ rawCoefficientBUnit B t 1 := by
  let F := PresheafOfModules.sheafification.{r}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj)
  let adj := PresheafOfModules.sheafificationAdjunction.{r}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj)
  calc
    _ = (adj.unit.app (rawCoefficientB B t n) ≫
        (coefficientSheafificationIso B t n).hom.val) ≫
          (coefficientBetaB B t n hn).val := by
      rw [coefficientSheafificationIso_unit]
    _ = adj.unit.app (rawCoefficientB B t n) ≫
        ((coefficientSheafificationIso B t n).hom ≫
          coefficientBetaB B t n hn).val := by
      rw [SheafOfModules.comp_val, Category.assoc]
    _ = adj.unit.app (rawCoefficientB B t n) ≫
        (F.map (rawBetaB B t n hn) ≫ (coefficientSheafificationIso B t 1).hom).val := by
      simp only [coefficientBetaB, Iso.hom_inv_id_assoc]
      rfl
    _ = (rawBetaB B t n hn ≫ adj.unit.app (rawCoefficientB B t 1)) ≫
        (coefficientSheafificationIso B t 1).hom.val := by
      rw [SheafOfModules.comp_val, ← Category.assoc]
      exact congrArg (fun k ↦ k ≫ (coefficientSheafificationIso B t 1).hom.val)
        (moduleSheafification_unit_naturality
          (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj B) (rawBetaB B t n hn))
    _ = _ := by rw [Category.assoc, coefficientSheafificationIso_unit]

private theorem coefficientAlphaB_class (n : ℕ) (hn : 1 ≤ n)
    (U : Cᵒᵖ) (b : B.obj.obj U) :
    (coefficientAlphaB B t n hn).val.app U
        ((principalPowerRingProjection B t (n - 1)).hom.app U b) =
      (principalPowerRingProjection B t n).hom.app U
        ((@id (B.obj.obj U) (t.val U)) * b) :=
  congrArg (fun f ↦ (f.app U) (Ideal.Quotient.mk (sectionPowerIdeal B t (n - 1) U) b))
    (coefficientAlphaB_unit B t n hn)

private theorem coefficientBetaB_class (n : ℕ) (hn : 1 ≤ n)
    (U : Cᵒᵖ) (b : B.obj.obj U) :
    (coefficientBetaB B t n hn).val.app U
        ((principalPowerRingProjection B t n).hom.app U b) =
      (principalPowerRingProjection B t 1).hom.app U b :=
  congrArg (fun f ↦ (f.app U) (Ideal.Quotient.mk (sectionPowerIdeal B t n U) b))
    (coefficientBetaB_unit B t n hn)

private def tensorCoefficientBSequence (n : ℕ) (hn : 1 ≤ n)
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) :
    ShortComplex (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) :=
  (coefficientBSequence B t n hn).map (siteSheafTensorRight M)

private theorem tensorCoefficientBSequence_shortExact (n : ℕ) (hn : 1 ≤ n)
    (ht : ∀ U : Cᵒᵖ, Function.Injective
      (fun b : B.obj.obj U ↦ (@id (B.obj.obj U) (t.val U)) * b))
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))
    (hM : IsFlatOnSite (R := B) M) :
    (tensorCoefficientBSequence B t n hn M).ShortExact := by
  have : PreservesFiniteLimits (siteSheafTensorRight M) := hM.1
  have : PreservesFiniteColimits (siteSheafTensorRight M) := hM.2
  exact (coefficientBSequence_shortExact B t n hn ht).map_of_exact
    (siteSheafTensorRight M)

private abbrev quotientTensorB (j : ℕ) :=
  leftTensorSheaf (quotientCoefficientB B t j)

private theorem quotientTensorB_zero (n : ℕ) (hn : 1 ≤ n) :
    leftTensorSheafMap (coefficientAlphaB B t n hn) ≫
      leftTensorSheafMap (coefficientBetaB B t n hn) = 0 := by
  rw [← leftTensorSheafMap_comp, coefficientAlphaB_comp_beta, leftTensorSheafMap_zero]

private def tensorCoefficientBCochainSequence (n : ℕ) (hn : 1 ≤ n)
    (P : CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)) ℤ) :
    ShortComplex (CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)) ℤ) :=
  cochainSequence (quotientTensorB B t (n - 1)) (quotientTensorB B t n)
    (quotientTensorB B t 1) (leftTensorSheafMap (coefficientAlphaB B t n hn))
    (leftTensorSheafMap (coefficientBetaB B t n hn)) (quotientTensorB_zero B t n hn) P

private theorem tensorCoefficientBCochainSequence_shortExact (n : ℕ) (hn : 1 ≤ n)
    (ht : ∀ U : Cᵒᵖ, Function.Injective
      (fun b : B.obj.obj U ↦ (@id (B.obj.obj U) (t.val U)) * b))
    (P : CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)) ℤ)
    (hflat : ∀ i : ℤ, IsFlatOnSite (R := B) (P.X i)) :
    (tensorCoefficientBCochainSequence B t n hn P).ShortExact := by
  apply cochainSequence_shortExact
  intro i
  exact tensorCoefficientBSequence_shortExact B t n hn ht (P.X i) (hflat i)

private theorem tensorCoefficientBCochainSequence_alpha (n : ℕ) (hn : 1 ≤ n)
    (P : CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)) ℤ)
    (i : ℤ) (U : Cᵒᵖ) (b : B.obj.obj U) (x : (P.X i).val.obj U) :
    ((tensorCoefficientBCochainSequence B t n hn P).f.f i).val.app U
      (siteSheafTensorTmul (quotientCoefficientB B t (n - 1)) (P.X i) U
        ((principalPowerRingProjection B t (n - 1)).hom.app U b) x) =
      siteSheafTensorTmul (quotientCoefficientB B t n) (P.X i) U
        ((principalPowerRingProjection B t n).hom.app U
          ((@id (B.obj.obj U) (t.val U)) * b)) x := by
  change ((siteSheafTensorRight (P.X i)).map (coefficientAlphaB B t n hn)).val.app U
    (siteSheafTensorTmul _ _ _ _ _) = _
  rw [tensorMap_tmul, coefficientAlphaB_class]

private theorem tensorCoefficientBCochainSequence_beta (n : ℕ) (hn : 1 ≤ n)
    (P : CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)) ℤ)
    (i : ℤ) (U : Cᵒᵖ) (b : B.obj.obj U) (x : (P.X i).val.obj U) :
    ((tensorCoefficientBCochainSequence B t n hn P).g.f i).val.app U
      (siteSheafTensorTmul (quotientCoefficientB B t n) (P.X i) U
        ((principalPowerRingProjection B t n).hom.app U b) x) =
      siteSheafTensorTmul (quotientCoefficientB B t 1) (P.X i) U
        ((principalPowerRingProjection B t 1).hom.app U b) x := by
  change ((siteSheafTensorRight (P.X i)).map (coefficientBetaB B t n hn)).val.app U
    (siteSheafTensorTmul _ _ _ _ _) = _
  rw [tensorMap_tmul, coefficientBetaB_class]

/-- Tensoring the regular-element coefficient sequence with a complex with flat terms
is short exact over the middle quotient ring. This assertion is entirely about ordinary
cochain complexes; it neither constructs a derived triangle nor identifies a derived tensor.

Source: blueprint main-20261015, integral criterion reductions, second paragraph;
Stacks Project, Modules on Sites, Tags 03DA, 03EK, 03ER
(blueprint: lem-pe-successive-quotient-flat-tensor-sequence).

Proof: the sectionwise quotient maps induce ring-sheaf maps R_n to R_(n-1) and R_1,
commuting with their projections from B. Before sheafification, multiplication by t
and quotient give a short exact sequence of B-module presheaves: if tc=t^n d,
regularity cancels t and gives c=t^(n-1)d; a class killed modulo t is represented by
td; and the second arrow is surjective. Sheafification is exact. Its unit is locally
bijective, so the resulting endpoint coefficient modules are the actual quotient-ring
sheaves with their restricted actions. Restrict to B and tensor with each P^i. Flatness
means exactness of this sheaf tensor functor, so the tensor sequence is short exact.
The canonical tensor/scalar-extension comparison identifies its terms with the
specified E-models; on local pure tensors it is the identity. The resulting maps are
R_n-linear. This can be checked on local quotient representatives, or by the full
faithfulness of restriction along the locally surjective map B to R_n. That restriction
is exact and faithful, so it also reflects this short exactness. The coefficient maps
are natural in P^i, hence commute with every differential. Degreewise short exactness
then gives short exactness of the cochain sequence. The sheafification-unit formulas
are exactly [b] tensor x to [tb] tensor x and [b] tensor x to [b] tensor x. -/
theorem successive_quotient_flat_tensor_sequence (n : ℕ) (hn : 1 < n)
    (ht : ∀ U : Cᵒᵖ, Function.Injective
      (fun b : B.obj.obj U ↦ (@id (B.obj.obj U) (t.val U)) * b))
    [HasDerivedCategory.{wB} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B))]
    [HasDerivedCategory.{wPrev} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J (principalPowerRingQuotient B t (n - 1))))]
    [HasDerivedCategory.{wN} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J (principalPowerRingQuotient B t n)))]
    [HasDerivedCategory.{wOne} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J (principalPowerRingQuotient B t 1)))]
    (FPrev : DerivedChangeOfRingsCochainModel.{u, v, r, wB, wPrev}
      (principalPowerRingProjection B t (n - 1)))
    (FN : DerivedChangeOfRingsCochainModel.{u, v, r, wB, wN}
      (principalPowerRingProjection B t n))
    (FOne : DerivedChangeOfRingsCochainModel.{u, v, r, wB, wOne}
      (principalPowerRingProjection B t 1))
    (P : CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)) ℤ)
    (hflat : ∀ i : ℤ, IsFlatOnSite (R := B) (P.X i)) :
    Nonempty (SuccessiveQuotientFlatTensorData t
      (principalPowerRingProjection B t (n - 1)) (principalPowerRingProjection B t n)
      (principalPowerRingProjection B t 1) FPrev FN FOne P) := by
  classical
  let h : 1 ≤ n := Nat.le_of_lt hn
  let rPrev := quotientTransition B t (n - 1) n (Nat.sub_le n 1)
  let rOne := quotientTransition B t 1 n h
  have hrPrev : principalPowerRingProjection B t n ≫ rPrev =
      principalPowerRingProjection B t (n - 1) :=
    quotientTransition_projection B t (n - 1) n (Nat.sub_le n 1)
  have hrOne : principalPowerRingProjection B t n ≫ rOne =
      principalPowerRingProjection B t 1 := quotientTransition_projection B t 1 n h
  let R := restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map
    (principalPowerRingProjection B t n))
  have : Presheaf.IsLocallySurjective J
      (((sheafCompose J (forget₂ CommRingCat RingCat)).map
        (principalPowerRingProjection B t n)).hom) := principalProjection_locallySurjective B t n
  let V := R.mapHomologicalComplex (.up ℤ)
  let XPrev := successiveQuotientRestrictedModel rPrev FPrev P
  let XN := successiveQuotientTensorModel FN P
  let XOne := successiveQuotientRestrictedModel rOne FOne P
  let S := tensorCoefficientBCochainSequence B t n h P
  have hS : S.ShortExact := tensorCoefficientBCochainSequence_shortExact B t n h ht P hflat
  let ePrev : S.X₁ ≅ V.obj XPrev :=
    (NatIso.mapHomologicalComplex
      (endpointModelIso (principalPowerRingProjection B t n) rPrev hrPrev FPrev) (.up ℤ)).app P
  let eN : S.X₂ ≅ V.obj XN := (NatIso.mapHomologicalComplex (modelTensorIso FN) (.up ℤ)).app P
  let eOne : S.X₃ ≅ V.obj XOne :=
    (NatIso.mapHomologicalComplex
      (endpointModelIso (principalPowerRingProjection B t n) rOne hrOne FOne) (.up ℤ)).app P
  exact flatTensorData_of_sequence t
    (principalPowerRingProjection B t (n - 1)) (principalPowerRingProjection B t n)
    (principalPowerRingProjection B t 1) FPrev FN FOne P rPrev rOne hrPrev hrOne S hS
    ePrev eN eOne
    (fun i U b x ↦ siteSheafTensorTmul (quotientCoefficientB B t (n - 1)) (P.X i) U
      ((principalPowerRingProjection B t (n - 1)).hom.app U b) x)
    (fun i U b x ↦ siteSheafTensorTmul (quotientCoefficientB B t n) (P.X i) U
      ((principalPowerRingProjection B t n).hom.app U b) x)
    (fun i U b x ↦ siteSheafTensorTmul (quotientCoefficientB B t 1) (P.X i) U
      ((principalPowerRingProjection B t 1).hom.app U b) x)
    (tensorCoefficientBCochainSequence_alpha B t n h P)
    (tensorCoefficientBCochainSequence_beta B t n h P)
    (fun i U b x ↦ endpointModelIso_tmul (principalPowerRingProjection B t n) rPrev hrPrev
      FPrev (P.X i) U ((principalPowerRingProjection B t (n - 1)).hom.app U b) x)
    (fun i U b x ↦ modelTensorIso_tmul FN (P.X i) U
      ((principalPowerRingProjection B t n).hom.app U b) x)
    (fun i U b x ↦ endpointModelIso_tmul (principalPowerRingProjection B t n) rOne hrOne
      FOne (P.X i) U ((principalPowerRingProjection B t 1).hom.app U b) x)

end SheafOfModules
