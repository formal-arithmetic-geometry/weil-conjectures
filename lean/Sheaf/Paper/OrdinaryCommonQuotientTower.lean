/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T5
-/
module

public import Sheaf.Paper.CommonQuotientTowerPresentation
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import all Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Ordinary common-quotient scalar extensions

Source: Stacks Project, Modules on Sites, Tag 03EK (section-tensor-product).
The result concerns module sheaves before passing to complexes or derived categories.
Quotient units are proved epic, their local ideal-product kernels are computed, and their
transition compatibility follows from the pure-section formulas. The remaining theorem
constructs the normalized ordinary comparison and coefficient transitions.
The quotient units themselves are constructed by the sheafification adjunction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
universe u v r wR wB wS
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]

set_option quotPrecheck false in
set_option hygiene false in
local notation:max "Mod" A:arg => ringedSiteModules.{r}
  (derivedChangeRingIndependentCoefficients J A)
set_option quotPrecheck false in
set_option hygiene false in
local notation:max "Res" f:arg => restrictScalars
  ((sheafCompose J (forget₂ CommRingCat RingCat)).map f)

section QuotientKernel
variable {R S : Sheaf J CommRingCat.{r}} (q : R ⟶ S)

private def K (U : Cᵒᵖ) : Ideal (R.obj.obj U) := RingHom.ker (q.hom.app U).hom

omit [EssentiallySmall.{r} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}] in
private theorem K_map {U V : Cᵒᵖ} (f : U ⟶ V) (a : R.obj.obj U)
    (ha : a ∈ K q U) : R.obj.map f a ∈ K q V := by
  change (q.hom.app V).hom (R.obj.map f a) = 0
  have h := CategoryTheory.congr_fun (q.hom.naturality f) a
  change (q.hom.app V).hom (R.obj.map f a) = S.obj.map f ((q.hom.app U).hom a) at h
  rw [h]
  change (q.hom.app U).hom a = 0 at ha
  rw [ha, map_zero]

private def quotientMap {U V : Cᵒᵖ} (f : U ⟶ V) :
    ModuleCat.of (R.obj.obj U) (R.obj.obj U ⧸ K q U) ⟶
      (ModuleCat.restrictScalars (R.obj.map f).hom).obj
        (ModuleCat.of (R.obj.obj V) (R.obj.obj V ⧸ K q V)) := by
  let g : R.obj.obj U →ₛₗ[(R.obj.map f).hom] R.obj.obj V :=
    { toFun := R.obj.map f
      map_add' := map_add (R.obj.map f).hom
      map_smul' := fun a b ↦ map_mul (R.obj.map f).hom a b }
  let h := (K q U).mapQ (K q V) g (fun a ha ↦ K_map q f a ha)
  exact ModuleCat.ofHom
    (X := ModuleCat.of (R.obj.obj U) (R.obj.obj U ⧸ K q U))
    (Y := (ModuleCat.restrictScalars (R.obj.map f).hom).obj
      (ModuleCat.of (R.obj.obj V) (R.obj.obj V ⧸ K q V)))
    { toFun := h
      map_add' := h.map_add
      map_smul' := fun a b ↦ h.map_smulₛₗ a b }

private def quotientPresheaf :
    PresheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R).obj where
  obj U := ModuleCat.of (R.obj.obj U) (R.obj.obj U ⧸ K q U)
  map f := quotientMap q f
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      change Submodule.Quotient.mk (R.obj.map (𝟙 U) x) = Submodule.Quotient.mk x
      exact congrArg Submodule.Quotient.mk
        (CategoryTheory.congr_fun (R.obj.map_id U) x)
  map_comp {U V W} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      change Submodule.Quotient.mk (R.obj.map (f ≫ g) x) =
        Submodule.Quotient.mk (R.obj.map g (R.obj.map f x))
      rw [Functor.map_comp]
      rfl

private def quotientToScalar : quotientPresheaf q ⟶
    ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map q)).obj
      (unit (derivedChangeRingIndependentCoefficients J S))).val where
  app U := ModuleCat.ofHom
    (X := (quotientPresheaf q).obj U)
    (Y := (((restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map q)).obj
        (unit (derivedChangeRingIndependentCoefficients J S))).val.obj U))
    { toFun := RingHom.kerLift (q.hom.app U).hom
      map_add' := (RingHom.kerLift (q.hom.app U).hom).map_add
      map_smul' := by
        intro a x
        induction x using Submodule.Quotient.induction_on with
        | _ x =>
          change (q.hom.app U).hom (a * x) =
            (q.hom.app U).hom a * (q.hom.app U).hom x
          exact map_mul _ _ _ }
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      change (q.hom.app V).hom (R.obj.map f x) = S.obj.map f ((q.hom.app U).hom x)
      exact CategoryTheory.congr_fun (q.hom.naturality f) x

omit [EssentiallySmall.{r} C] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}] in
private theorem quotientToScalar_locallyInjective :
    PresheafOfModules.IsLocallyInjective J (quotientToScalar q) :=
  Presheaf.isLocallyInjective_of_injective J _ (fun U ↦ RingHom.kerLift_injective (q.hom.app U).hom)

omit [EssentiallySmall.{r} C] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}] in
private theorem quotientToScalar_locallySurjective
    (hq : Presheaf.IsLocallySurjective J q.hom) :
    PresheafOfModules.IsLocallySurjective J (quotientToScalar q) := by
  constructor
  intro U s
  apply J.superset_covering ?_ (Presheaf.imageSieve_mem J q.hom s)
  rintro V f ⟨r, hr⟩
  exact ⟨Submodule.Quotient.mk r, hr⟩

omit [EssentiallySmall.{r} C] in
private theorem tensor_quotientToScalar_locallyInjective
    (hq : Presheaf.IsLocallySurjective J q.hom)
    (M : SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R)) :
    PresheafOfModules.IsLocallyInjective J (siteTensorHom (quotientToScalar q) M.val) := by
  have hI : PresheafOfModules.IsLocallyInjective J (quotientToScalar q) :=
    quotientToScalar_locallyInjective q
  have hS : PresheafOfModules.IsLocallySurjective J (quotientToScalar q) :=
    quotientToScalar_locallySurjective q hq
  let A := derivedChangeRingIndependentCoefficients J R
  let f := siteTensorHom (quotientToScalar q) M.val
  have : IsIso ((PresheafOfModules.sheafification (R := A) (𝟙 A.obj)).map f) :=
    @PresheafOfModules.sheafification_tensorHom_isIso C _ J R.obj
      (quotientPresheaf q) _ M.val (quotientToScalar q) hI hS A.property _ _
  have : IsIso ((presheafToSheaf J AddCommGrpCat).map
      ((PresheafOfModules.toPresheaf A.obj).map f)) :=
    inferInstanceAs (IsIso ((toSheaf A).map
      ((PresheafOfModules.sheafification (R := A) (𝟙 A.obj)).map f)))
  exact ((J.W_iff _).mpr this).isLocallyInjective

private theorem kernel_forward
    (hq : Presheaf.IsLocallySurjective J q.hom)
    (M : SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R))
    (U : Cᵒᵖ) (x : M.val.obj U)
    (hx : (toSheafify J (changeOfRingsPresheaf q M).presheaf).app U
      ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(q.hom.app U).hom] x) = 0) :
    Sieve.generate (fun (V : C) (f : V ⟶ U.unop) ↦
      M.val.map f.op x ∈ Submodule.span (R.obj.obj (op V))
        {y | ∃ j ∈ K q (op V), ∃ p : M.val.obj (op V), y = j • p}) ∈ J U.unop := by
  let A := derivedChangeRingIndependentCoefficients J R
  let Q := quotientPresheaf q
  let B := ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map q)).obj
    (unit (derivedChangeRingIndependentCoefficients J S))).val
  let f := siteTensorHom (quotientToScalar q) M.val
  let e : siteTensorPresheaf B M.val ≅
      (PresheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map q).hom).obj
          (changeOfRingsPresheaf q M) :=
    (siteTensorRightIso R M.val).app B ≪≫ (presheafTensorIso q M).symm
  let ψ := (PresheafOfModules.toPresheaf A.obj).map f ≫
    (PresheafOfModules.toPresheaf A.obj).map e.hom ≫
      toSheafify J (changeOfRingsPresheaf q M).presheaf
  have hLI : Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf A.obj).map f) :=
    tensor_quotientToScalar_locallyInjective q hq M
  have : Presheaf.IsLocallyInjective J ψ := by
    dsimp only [ψ]
    have hE : Presheaf.IsLocallyInjective J
        ((PresheafOfModules.toPresheaf A.obj).map e.hom) := inferInstance
    have hθ : Presheaf.IsLocallyInjective J
        (toSheafify J (changeOfRingsPresheaf q M).presheaf) :=
      (J.W_toSheafify (changeOfRingsPresheaf q M).presheaf).isLocallyInjective
    exact @Presheaf.isLocallyInjective_comp _ _ _ _ _ _ _ _ J _ _ _ _ _ hLI
      (@Presheaf.isLocallyInjective_comp _ _ _ _ _ _ _ _ J _ _ _ _ _ hE hθ)
  let z : (siteTensorPresheaf Q M.val).obj U :=
    (1 : R.obj.obj U ⧸ K q U) ⊗ₜ[R.obj.obj U] x
  have hzero : ψ.app U z = ψ.app U 0 := by
    rw [map_zero]
    change (toSheafify J (changeOfRingsPresheaf q M).presheaf).app U
      ((RingHom.kerLift (q.hom.app U).hom 1)
        ⊗ₜ[R.obj.obj U, (q.hom.app U).hom] x) = 0
    rw [map_one]
    exact hx
  apply J.superset_covering ?_ (Presheaf.equalizerSieve_mem J ψ z 0 hzero)
  intro V g hg
  apply Sieve.le_generate
  change (siteTensorPresheaf Q M.val).map g.op z =
    (siteTensorPresheaf Q M.val).map g.op 0 at hg
  rw [map_zero] at hg
  change (quotientMap q g.op (1 : R.obj.obj U ⧸ K q U)) ⊗ₜ[R.obj.obj (op V)]
    M.val.map g.op x = 0 at hg
  have h1 : quotientMap q g.op (1 : R.obj.obj U ⧸ K q U) =
      (1 : R.obj.obj (op V) ⧸ K q (op V)) := by
    change Submodule.Quotient.mk (R.obj.map g.op 1) = Submodule.Quotient.mk 1
    rw [map_one]
  rw [h1] at hg
  have hquot := congrArg
    (TensorProduct.quotTensorEquivQuotSMul (M.val.obj (op V)) (K q (op V))) hg
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, map_zero] at hquot
  have hmem : M.val.map g.op x ∈ K q (op V) • (⊤ : Submodule _ (M.val.obj (op V))) :=
    (Submodule.Quotient.mk_eq_zero _).mp hquot
  have hle : K q (op V) • (⊤ : Submodule _ (M.val.obj (op V))) ≤
      Submodule.span (R.obj.obj (op V))
        {y | ∃ j ∈ K q (op V), ∃ p : M.val.obj (op V), y = j • p} := by
    rw [← Submodule.span_univ, ← (K q (op V)).span_eq, Submodule.span_smul_span]
    apply Submodule.span_le.mpr
    rintro y ⟨j, hj, p, _, rfl⟩
    exact Submodule.subset_span ⟨j, Ideal.subset_span hj, p, rfl⟩
  exact hle hmem

end QuotientKernel

/-- The sectionwise quotient unit, sending x to 1 tensor x.
Source: Stacks 03EK (blueprint: lem-weil-pbc-ordinary-common-quotient-tower). -/
noncomputable def commonQuotientPresheafUnit
    {R S : Sheaf J CommRingCat.{r}} (q : R ⟶ S) (M : Mod R) :
    M.val ⟶ (PresheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map q).hom).obj
        (changeOfRingsPresheaf q M) where
  app U := (ModuleCat.ExtendRestrictScalarsAdj.unit (q.hom.app U).hom).app (M.val.obj U)
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    ext x
    change (1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (q.hom.app V).hom] M.val.map f x =
      changeOfRingsMap q M f ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (q.hom.app U).hom] x)
    rw [show changeOfRingsMap q M f
        ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (q.hom.app U).hom] x) =
        S.obj.map f 1 ⊗ₜ[R.obj.obj V, (q.hom.app V).hom] M.val.map f x from
      Classical.choose_spec (exists_changeOfRingsMap q M f) 1 x, map_one]

omit [EssentiallySmall.{r} C] in
private theorem quotientPresheafUnit_locallySurjective
    {R S : Sheaf J CommRingCat.{r}} (q : R ⟶ S)
    (hq : Presheaf.IsLocallySurjective J q.hom) (M : Mod R) :
    PresheafOfModules.IsLocallySurjective J (commonQuotientPresheafUnit q M) := by
  let η := commonQuotientPresheafUnit q M
  constructor
  intro U t
  induction t using TensorProduct.induction_on with
  | zero =>
    apply J.superset_covering (S := ⊤) ?_ (J.top_mem U)
    intro V f _
    refine ⟨0, ?_⟩
    change (η.app _).hom 0 = (changeOfRingsPresheaf q M).map f.op 0
    rw [map_zero, map_zero]
  | tmul r m =>
    apply J.superset_covering ?_ (Presheaf.imageSieve_mem J q.hom r)
    rintro V f ⟨r', hr'⟩
    refine ⟨r' • (show M.val.obj (op V) from M.val.map f.op m), ?_⟩
    change (η.app _).hom (r' • (show M.val.obj (op V) from M.val.map f.op m)) =
      changeOfRingsMap q M f.op (r ⊗ₜ[R.obj.obj _, (q.hom.app _).hom] m)
    rw [(η.app _).hom.map_smul]
    rw [show changeOfRingsMap q M f.op
        (r ⊗ₜ[R.obj.obj _, (q.hom.app _).hom] m) =
        S.obj.map f.op r ⊗ₜ[R.obj.obj _, (q.hom.app _).hom] M.val.map f.op m from
      Classical.choose_spec (exists_changeOfRingsMap q M f.op) r m]
    change (q.hom.app (op V) r') •
      ((1 : S.obj.obj (op V)) ⊗ₜ[R.obj.obj (op V), (q.hom.app (op V)).hom]
        (show M.val.obj (op V) from M.val.map f.op m)) = _
    rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
    exact congrArg (fun s ↦ s ⊗ₜ[R.obj.obj (op V), (q.hom.app (op V)).hom]
      (show M.val.obj (op V) from M.val.map f.op m)) hr'
  | add x y hx hy =>
    apply J.superset_covering ?_ (J.intersection_covering hx hy)
    rintro V f ⟨⟨m, hm⟩, ⟨n, hn⟩⟩
    refine ⟨m + n, ?_⟩
    change (η.app _).hom (m + n) = (changeOfRingsPresheaf q M).map f.op (x + y)
    rw [map_add, map_add]
    exact congrArg₂ (· + ·) hm hn

omit [EssentiallySmall.{r} C] in
private theorem quotientUnit_epi
    {R S : Sheaf J CommRingCat.{r}} (q : R ⟶ S)
    (hq : Presheaf.IsLocallySurjective J q.hom) (M : Mod R)
    (u : M ⟶ (Res q).obj (changeOfRings q M))
    (hu : ∀ (U : Cᵒᵖ) (x : M.val.obj U), u.val.app U x =
      (toSheafify J (changeOfRingsPresheaf q M).presheaf).app U
        ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(q.hom.app U).hom] x)) : Epi u := by
  have := quotientPresheafUnit_locallySurjective q hq M
  have hfac : (PresheafOfModules.toPresheaf _).map u.val =
      (PresheafOfModules.toPresheaf _).map (commonQuotientPresheafUnit q M) ≫
        toSheafify J (changeOfRingsPresheaf q M).presheaf := by
    ext U x
    exact hu U x
  have hlocal : PresheafOfModules.IsLocallySurjective J u.val := by
    change Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf _).map u.val)
    rw [hfac]
    have : Presheaf.IsLocallySurjective J
        (toSheafify J (changeOfRingsPresheaf q M).presheaf) :=
      (J.W_toSheafify (changeOfRingsPresheaf q M).presheaf).isLocallySurjective
    exact Presheaf.isLocallySurjective_comp J _ _
  have : Sheaf.IsLocallySurjective ((toSheaf _).map u) := hlocal
  have : Epi ((toSheaf _).map u) := Sheaf.epi_of_isLocallySurjective _
  exact (toSheaf _).epi_of_epi_map inferInstance

/-- The actual sheaf quotient unit constructed from the sheafification adjunction.
Source: Stacks 03EK (blueprint: lem-weil-pbc-ordinary-common-quotient-tower). -/
noncomputable def commonQuotientUnit
    {R S : Sheaf J CommRingCat.{r}} (q : R ⟶ S) (M : Mod R) :
    M ⟶ (Res q).obj (changeOfRings q M) where
  val := commonQuotientPresheafUnit q M ≫
    (PresheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map q).hom).map
        (PresheafOfModules.sheafificationHomEquiv
          (𝟙 (derivedChangeRingIndependentCoefficients J S).obj)
          (𝟙 (changeOfRings q M)))

omit [EssentiallySmall.{r} C] in
/-- The actual quotient unit has the prescribed section formula.
Source: Stacks 03EK (blueprint: lem-weil-pbc-ordinary-common-quotient-tower). -/
theorem commonQuotientUnit_sections
    {R S : Sheaf J CommRingCat.{r}} (q : R ⟶ S) (M : Mod R)
    (U : Cᵒᵖ) (x : M.val.obj U) :
    (commonQuotientUnit q M).val.app U x =
      (toSheafify J (changeOfRingsPresheaf q M).presheaf).app U
        ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(q.hom.app U).hom] x) := by
  rfl

/-- The actual quotient units are natural in the module.
Source: Stacks 03EK (blueprint: lem-weil-pbc-ordinary-common-quotient-tower). -/
theorem commonQuotientUnit_naturality
    {R S : Sheaf J CommRingCat.{r}} (q : R ⟶ S)
    {M N : Mod R} (f : M ⟶ N) :
    f ≫ commonQuotientUnit q N = commonQuotientUnit q M ≫ (Res q).map (changeOfRingsHom q M f) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let g := changePresheafHom q f
  have h := congrArg (fun a ↦ a.app U
    ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(q.hom.app U).hom] x))
      (toSheafify_naturality J ((PresheafOfModules.toPresheaf _).map g))
  exact h

/-- The quotient unit transported to a prescribed ordinary scalar-extension model.
Source: Stacks 03EK (blueprint: lem-weil-pbc-ordinary-common-quotient-tower). -/
noncomputable def commonQuotientModelUnit
    {R S : Sheaf J CommRingCat.{r}} (q : R ⟶ S)
    [HasDerivedCategory.{wR} (Mod R)] [HasDerivedCategory.{wS} (Mod S)]
    (F : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} q) :
    𝟭 (Mod R) ⟶ F.E ⋙ Res q where
  app M := commonQuotientUnit q M ≫ (Res q).map (eqToHom (F.obj_eq M).symm)
  naturality {M N} f := by
    dsimp only [Functor.id_map, Functor.comp_map]
    rw [← Category.assoc, commonQuotientUnit_naturality q f, Category.assoc]
    rw [F.map_eq, Functor.map_comp, Functor.map_comp]
    simp only [Category.assoc, ← Functor.map_comp]
    apply congrArg (fun g ↦ commonQuotientUnit q M ≫ (Res q).map g)
    rw [← Category.assoc (eqToHom (F.obj_eq M).symm) (eqToHom (F.obj_eq M)),
      eqToHom_trans, eqToHom_refl, Category.id_comp]

variable {R B : Sheaf J CommRingCat.{r}} {φ : R ⟶ B}
  (D : CommonQuotientTowerPresentation φ)
  [HasDerivedCategory.{wR} (Mod R)] [HasDerivedCategory.{wB} (Mod B)]
  [∀ n : ℕ, HasDerivedCategory.{wS} (Mod(D.S.obj (op n)))]
  (a : ∀ n : ℕ, DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} (D.projection n))
  (b : ∀ n : ℕ,
    DerivedChangeOfRingsCochainModel.{u, v, r, wB, wS} (D.extensionProjection n))

/-- Ordinary common-quotient maps, characterized on the sheafification-unit images
of pure tensors. There are no complexes, K-flatness, or derived comparisons here.
Source: Stacks 03EK
(blueprint: lem-weil-pbc-ordinary-common-quotient-tower). -/
structure OrdinaryCommonQuotientTower where
  ordinary : ∀ n : ℕ, Res φ ⋙ (a n).E ≅ (b n).E
  ordinary_sections : ∀ (n : ℕ) (M : Mod B) (U : Cᵒᵖ)
    (s : (D.S.obj (op n)).obj.obj U) (x : M.val.obj U),
    ((ordinary n).hom.app M).val.app U
      ((eqToHom ((a n).obj_eq ((Res φ).obj M)).symm).val.app U
        ((toSheafify J (changeOfRingsPresheaf (D.projection n)
          ((Res φ).obj M)).presheaf).app U
            (s ⊗ₜ[R.obj.obj U, ((D.projection n).hom.app U).hom] x))) =
      (eqToHom ((b n).obj_eq M).symm).val.app U
        ((toSheafify J (changeOfRingsPresheaf (D.extensionProjection n) M).presheaf).app U
          (s ⊗ₜ[B.obj.obj U, ((D.extensionProjection n).hom.app U).hom] x))
  transition : ∀ n : ℕ,
    (a (n + 1)).E ⋙ Res (D.projection (n + 1)) ⟶ (a n).E ⋙ Res (D.projection n)
  transition_sections : ∀ (n : ℕ) (M : Mod R) (U : Cᵒᵖ)
    (s : (D.S.obj (op (n + 1))).obj.obj U) (x : M.val.obj U),
    ((transition n).app M).val.app U
      ((eqToHom ((a (n + 1)).obj_eq M).symm).val.app U
        ((toSheafify J (changeOfRingsPresheaf (D.projection (n + 1)) M).presheaf).app U
          (s ⊗ₜ[R.obj.obj U, ((D.projection (n + 1)).hom.app U).hom] x))) =
      (eqToHom ((a n).obj_eq M).symm).val.app U
        ((toSheafify J (changeOfRingsPresheaf (D.projection n) M).presheaf).app U
          (((D.S.map (homOfLE (Nat.le_succ n)).op).hom.app U s)
            ⊗ₜ[R.obj.obj U, ((D.projection n).hom.app U).hom] x))


omit [EssentiallySmall.{r} C] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}] [HasDerivedCategory.{wR} (Mod R)]
  [HasDerivedCategory.{wB} (Mod B)]
  [∀ n : ℕ, HasDerivedCategory.{wS} (Mod(D.S.obj (op n)))] in
private theorem locallyInIdealProduct_killed (n : ℕ) (M : Mod R)
    (N : Mod(D.S.obj (op n))) (u : M ⟶ (Res(D.projection n)).obj N)
    (U : Cᵒᵖ) (x : M.val.obj U) (hx : D.locallyInIdealProduct n M U x) :
    u.val.app U x = 0 := by
  have hk (V : Cᵒᵖ) :
      Submodule.span (R.obj.obj V)
        {y | ∃ j ∈ D.ideal n V, ∃ p : M.val.obj V, y = j • p} ≤
          LinearMap.ker (u.val.app V).hom := by
    apply Submodule.span_le.mpr
    rintro y ⟨j, hj, p, rfl⟩
    change (u.val.app V).hom (j • p) = 0
    rw [LinearMap.map_smul]
    change ((D.projection n).hom.app V).hom j •
      (show N.val.obj V from u.val.app V p) = (0 : N.val.obj V)
    have hj' : ((D.projection n).hom.app V).hom j = 0 := hj
    rw [hj', zero_smul]
  let N' := (Res (D.projection n)).obj N
  let S := Presheaf.equalizerSieve (F := N'.val.presheaf) (u.val.app U x) 0
  have hS : S ∈ J U.unop := by
    apply J.superset_covering ?_ hx
    apply (Sieve.generate_le_iff _ S).mpr
    intro V f hf
    change N'.val.map f.op (u.val.app U x) = N'.val.map f.op 0
    rw [map_zero, ← PresheafOfModules.naturality_apply u.val f.op x]
    exact hk (op V) hf
  apply N'.isSheaf.isSeparated _ _ hS
  intro V f hf
  exact hf

variable {D a b}

/-- The quotient units are constructed, rather than chosen as part of the comparison.
Source: Stacks 03EK (blueprint: lem-weil-pbc-ordinary-common-quotient-tower). -/
def OrdinaryCommonQuotientTower.unit (_O : OrdinaryCommonQuotientTower D a b) (n : ℕ) :
    𝟭 (Mod R) ⟶ (a n).E ⋙ Res (D.projection n) :=
  commonQuotientModelUnit (D.projection n) (a n)

/-- The constructed quotient units have the normalized pure-section formula.
Source: Stacks 03EK (blueprint: lem-weil-pbc-ordinary-common-quotient-tower). -/
theorem OrdinaryCommonQuotientTower.unit_sections
    (O : OrdinaryCommonQuotientTower D a b) (n : ℕ) (M : Mod R)
    (U : Cᵒᵖ) (x : M.val.obj U) :
    ((O.unit n).app M).val.app U x =
      (eqToHom ((a n).obj_eq M).symm).val.app U
        ((toSheafify J (changeOfRingsPresheaf (D.projection n) M).presheaf).app U
          ((1 : (D.S.obj (op n)).obj.obj U)
            ⊗ₜ[R.obj.obj U, ((D.projection n).hom.app U).hom] x)) := by
  rfl

/-- The normalized quotient unit has exactly the local ideal-product kernel.
Source: Stacks 03EK
(blueprint: lem-weil-pbc-ordinary-common-quotient-tower).
Proof: form the sectionwise quotient R/ker(q) and its locally bijective map to S.
Tensoring this map becomes an isomorphism after sheafification. Local injectivity
therefore detects vanishing of 1 tensor x already locally in the quotient tensor.
The quotient-tensor equivalence identifies this with local membership in I M.
Conversely every R-linear map into an S-module kills I M; naturality and sheaf
separatedness turn local membership into global vanishing. -/
theorem OrdinaryCommonQuotientTower.unit_kernel
    (O : OrdinaryCommonQuotientTower D a b) (n : ℕ) (M : Mod R)
    (U : Cᵒᵖ) (x : M.val.obj U) :
    ((O.unit n).app M).val.app U x = 0 ↔ D.locallyInIdealProduct n M U x := by
  constructor
  · intro hx
    let z := (toSheafify J (changeOfRingsPresheaf (D.projection n) M).presheaf).app U
      ((1 : (D.S.obj (op n)).obj.obj U)
        ⊗ₜ[R.obj.obj U, ((D.projection n).hom.app U).hom] x)
    have h := congrArg (fun y ↦ (eqToHom ((a n).obj_eq M)).val.app U y) hx
    rw [O.unit_sections, map_zero] at h
    have hc : (eqToHom ((a n).obj_eq M)).val.app U
        ((eqToHom ((a n).obj_eq M).symm).val.app U z) = z :=
      congrArg (fun f ↦ f.val.app U z)
        (eqToHom_trans ((a n).obj_eq M).symm ((a n).obj_eq M))
    exact kernel_forward (D.projection n) (D.q_surjective n) M U x (hc.symm.trans h)
  · exact locallyInIdealProduct_killed D n M ((a n).E.obj M) ((O.unit n).app M) U x

/-- The pure-section transition formula forces compatibility of quotient units.
Source: Stacks 03EK
(blueprint: lem-weil-pbc-ordinary-common-quotient-tower).
Proof: evaluate the transition on 1 tensor x. Ring transitions preserve 1,
so the result is exactly the unit at the next level. Equality on sections proves
componentwise equality and therefore equality of natural transformations. -/
theorem OrdinaryCommonQuotientTower.unit_transition
    (O : OrdinaryCommonQuotientTower D a b) (n : ℕ) :
    O.unit (n + 1) ≫ O.transition n = O.unit n := by
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext x
  change ((O.transition n).app M).val.app U
    (((O.unit (n + 1)).app M).val.app U x) = ((O.unit n).app M).val.app U x
  rw [O.unit_sections, O.transition_sections, O.unit_sections, map_one]

/-- The normalized quotient unit is epi using local scalar lifts and tensor generation.
Source: Stacks 03EK
(blueprint: lem-weil-pbc-ordinary-common-quotient-tower).
Proof: the presheaf unit is locally surjective by induction on tensors: lift a pure
scalar along the local quotient projection; sums lift on the intersection cover.
Sheafification units are locally surjective, so the composite is locally surjective
and therefore epi. Transport along the prescribed ordinary object equality. -/
theorem OrdinaryCommonQuotientTower.unit_epi
    (O : OrdinaryCommonQuotientTower D a b) (n : ℕ) (M : Mod R) :
    Epi ((O.unit n).app M) := by
  let e := (Res (D.projection n)).mapIso (eqToIso ((a n).obj_eq M))
  let u := (O.unit n).app M ≫ e.hom
  have : Epi u := quotientUnit_epi (D.projection n) (D.q_surjective n) M u (by
    intro U x
    have h := O.unit_sections n M U x
    change (e.hom.val.app U) (((O.unit n).app M).val.app U x) = _
    rw [h]
    change (eqToHom ((a n).obj_eq M)).val.app U
      ((eqToHom ((a n).obj_eq M).symm).val.app U _) = _
    exact congrArg (fun f ↦ f.val.app U
      ((toSheafify J (changeOfRingsPresheaf (D.projection n) M).presheaf).app U
        ((1 : (D.S.obj (op n)).obj.obj U)
          ⊗ₜ[R.obj.obj U, ((D.projection n).hom.app U).hom] x)))
      (eqToHom_trans ((a n).obj_eq M).symm ((a n).obj_eq M)))
  have h : Epi (u ≫ e.inv) := inferInstance
  simpa [u, Category.assoc] using h

/-- The section normalizations determine all ordinary comparison data uniquely.
Source: Stacks 03EK
(blueprint: lem-weil-pbc-ordinary-common-quotient-tower).
Proof: units agree on every section. For a transition or a comparison, restrict
scalars to R and precompose with the epic quotient unit. The formulas at 1 tensor x
make the resulting maps equal on every section. Cancel the unit; restriction leaves
the underlying functions unchanged, so the original maps agree. Proof fields are
irrelevant. This also verifies that choosing the normalized data is unambiguous. -/
theorem OrdinaryCommonQuotientTower.unique
    (O O' : OrdinaryCommonQuotientTower D a b) : O = O' := by
  have ht : O.transition = O'.transition := by
    funext n
    apply NatTrans.ext
    funext M
    have := O.unit_epi (n + 1) M
    apply (cancel_epi ((O.unit (n + 1)).app M)).mp
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ((O.transition n).app M).val.app U
      (((O.unit (n + 1)).app M).val.app U x) =
        ((O'.transition n).app M).val.app U (((O.unit (n + 1)).app M).val.app U x)
    simp only [O.unit_sections]
    exact (O.transition_sections n M U 1 x).trans (O'.transition_sections n M U 1 x).symm
  have ho : O.ordinary = O'.ordinary := by
    funext n
    apply Iso.ext
    apply NatTrans.ext
    funext M
    let Q := Res (D.projection n)
    let P := (Res φ).obj M
    have := O.unit_epi n P
    have hQ : Q.map ((O.ordinary n).hom.app M) =
        Q.map ((O'.ordinary n).hom.app M) := by
      apply (cancel_epi ((O.unit n).app P)).mp
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro U
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change ((O.ordinary n).hom.app M).val.app U
        (((O.unit n).app P).val.app U x) =
          ((O'.ordinary n).hom.app M).val.app U (((O.unit n).app P).val.app U x)
      simp only [O.unit_sections]
      exact (O.ordinary_sections n M U 1 x).trans (O'.ordinary_sections n M U 1 x).symm
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun f ↦ f.val.app U x) hQ
  cases O
  cases O'
  dsimp only at ht ho
  cases ht
  cases ho
  rfl

variable (D a b)

/-- The ordinary sheaf tensor with a quotient is the quotient by the ideal product,
naturally in the module and compatibly with quotient projections.

Source: Stacks Project, sites-modules.tex, Tag 03EK (section-tensor-product),
and Algebra, tensor products and quotient modules.
(blueprint: lem-weil-pbc-ordinary-common-quotient-tower).

Proof:
1. Let I be the kernel of a locally surjective ring-sheaf map q:R→S.
Sheafify the sectionwise quotient M/(I M). A section of S lifts to R on a cover.
The pairing (s,x)↦[rx], for any local lift r of s, is independent of the lift,
because changing r by an element of I changes rx by an element of I M.
It therefore glues to a balanced pairing into the quotient sheaf, and gives
S⊗_R M→M/(I M). The inverse sends [x] to the image of 1⊗x; it kills I M
by balancing. The two composites fix local quotient sections and pure tensors.
Consequently the canonical unit is epi and its kernel consists exactly of
sections locally in the span of products jx, with j in ker(q).
2. In a pushout R→B, R→S, B→S, S→S with the last map the identity,
let T be the quotient sheaf B/(I B). The map R→T kills I, so local lifts along q
define a unique ring map S→T. Together with B→T this gives a map from the pushout
S to T. Conversely B→S kills I B and factors through T→S. The composites are
identities by quotient and pushout uniqueness. Thus T is the same quotient ring S.
For a B-module M, the submodule
(I B)M equals I M: a generator (φ(j)b)x is φ(j)(bx), and the reverse
inclusion takes b=1. The two tensor quotients are thus canonically S-linearly
isomorphic, sending the image of s⊗x to that same pure section. The formulas
commute with every module morphism and give the natural ordinary comparison.
3. For an adjacent quotient map t:S_(n+1)→S_n, sheafify the balanced map
s⊗x↦t(s)⊗x. Naturality of q and the tensor restrictions makes this a
morphism of R-module sheaves, natural in M. It carries 1⊗x to 1⊗x,
so the explicitly constructed quotient units commute with the transitions.
The units, their naturality, epi and kernel properties are already proved above.
Only the ordinary comparison and the coefficient transitions remain to construct.
No sectionwise surjectivity is used. -/
theorem nonempty_ordinaryCommonQuotientTower :
    Nonempty (OrdinaryCommonQuotientTower D a b) := by sorry

end SheafOfModules
