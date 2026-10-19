/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import Sheaf.Paper.ExtendedLocalizationCech
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.RingTheory.Ideal.Maps
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-! # Flat comparison on torsion Koszul cohomology

Source: Stacks Project, Tags 099H, 0GLY and 05E9
(blueprint: lem-weil-pbc-flat-localization-koszul-cohomology-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SheafOfModules.LocalizationCech

private def scalarWord {D : Type*} [Category D] {r : ℕ}
    (s : Fin r → (𝟭 D ⟶ 𝟭 D)) : List (Fin r) → (𝟭 D ⟶ 𝟭 D)
  | [] => 𝟙 _
  | j :: l => s j ≫ scalarWord s l

private theorem exact_natTrans_nilpotent
    {D : Type*} [Category D] [Abelian D] (F : D ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (η : 𝟭 D ⟶ F) {r : ℕ} (s : Fin r → (𝟭 D ⟶ 𝟭 D))
    (base : ∀ M, (∀ j, (s j).app M = 0) → IsIso (η.app M))
    (k : ℕ) (M : D)
    (hk : ∀ l : List (Fin r), l.length = k → (scalarWord s l).app M = 0) :
    IsIso (η.app M) := by
  induction k generalizing M with
  | zero =>
    have hz : IsZero M := (IsZero.iff_id_eq_zero M).2 (hk [] rfl)
    exact hz.isIso (Functor.map_isZero F hz) _
  | succ k ih =>
    let t : (∐ fun _ : Fin r => M) ⟶ M := Sigma.desc (fun j => (s j).app M)
    have hQ : ∀ j, (s j).app (cokernel t) = 0 := by
      intro j
      apply (cancel_epi (cokernel.π t)).1
      rw [comp_zero]
      rw [show cokernel.π t ≫ (s j).app (cokernel t) =
          (s j).app M ≫ cokernel.π t from (s j).naturality (cokernel.π t)]
      change (s j).app M ≫ cokernel.π t = 0
      rw [← Sigma.ι_desc (fun j => (s j).app M) j]
      change (Sigma.ι (fun _ : Fin r => M) j ≫ t) ≫ cokernel.π t = 0
      simp
    have hN : ∀ l : List (Fin r), l.length = k →
        (scalarWord s l).app (Abelian.image t) = 0 := by
      intro l hl
      apply (cancel_mono (Abelian.image.ι t)).1
      rw [zero_comp]
      rw [show (scalarWord s l).app (Abelian.image t) ≫ Abelian.image.ι t =
          Abelian.image.ι t ≫ (scalarWord s l).app M from
        ((scalarWord s l).naturality (Abelian.image.ι t)).symm]
      apply (cancel_epi (Abelian.factorThruImage t)).1
      rw [comp_zero, ← Category.assoc, Abelian.image.fac]
      apply Sigma.hom_ext
      intro j
      change Sigma.ι (fun _ : Fin r => M) j ≫ t ≫ (scalarWord s l).app M =
        Sigma.ι (fun _ : Fin r => M) j ≫ 0
      rw [← Category.assoc, Sigma.ι_desc, comp_zero]
      exact hk (j :: l) (by simp [hl])
    have := ih (Abelian.image t) hN
    have := base (cokernel t) hQ
    let S := ShortComplex.kernelSequence (cokernel.π t)
    have hS : S.ShortExact :=
      { exact := ShortComplex.kernelSequence_exact _
        mono_f := inferInstance
        epi_g := by change Epi (cokernel.π t); infer_instance }
    have h₁ : IsIso (S.mapNatTrans η).τ₁ :=
      ih (Abelian.image t) hN
    have h₃ : IsIso (S.mapNatTrans η).τ₃ := base (cokernel t) hQ
    exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ (S.mapNatTrans η)
      (hS.map_of_exact (𝟭 D)) (hS.map_of_exact F)

private def centralScalar {D : Type*} [Category D] [MonoidalCategory D]
    (s : End (𝟙_ D)) : 𝟭 D ⟶ 𝟭 D :=
  (rightUnitorNatIso D).inv ≫ (tensoringRight D).map s ≫ (rightUnitorNatIso D).hom

private theorem tensor_unit_on_killed
    {D : Type*} [Category D] [Abelian D] [MonoidalCategory D]
    [MonoidalPreadditive D]
    [∀ M : D, PreservesFiniteColimits (tensorLeft M)]
    {P : D} (u : 𝟙_ D ⟶ P) {r : ℕ} (s : Fin r → End (𝟙_ D))
    (hQ : IsIso (((rightUnitorNatIso D).inv ≫ (tensoringRight D).map u).app
      (cokernel (Sigma.desc s))))
    (M : D) (hM : ∀ j, (centralScalar (s j)).app M = 0) :
    IsIso (((rightUnitorNatIso D).inv ≫ (tensoringRight D).map u).app M) := by
  let t := Sigma.desc s
  let Q := cokernel t
  let η : 𝟭 D ⟶ tensorRight P :=
    (rightUnitorNatIso D).inv ≫ (tensoringRight D).map u
  have ht : (tensorLeft M).map t = 0 := by
    apply (cancel_epi (sigmaComparison (tensorLeft M) (fun _ : Fin r => 𝟙_ D))).1
    apply Sigma.hom_ext
    intro j
    dsimp only [t]
    simp only [ι_comp_sigmaComparison_assoc, ← Functor.map_comp, Sigma.ι_desc,
      comp_zero]
    have h := hM j
    change (ρ_ M).inv ≫ M ◁ s j ≫ (ρ_ M).hom = 0 at h
    apply (cancel_epi (ρ_ M).inv).1
    apply (cancel_mono (ρ_ M).hom).1
    simpa using h
  have hp : IsIso (M ◁ cokernel.π t) :=
    CokernelCofork.IsColimit.isIso_π _
      (CokernelCofork.mapIsColimit _ (cokernelIsCokernel t) (tensorLeft M)) ht
  have hMQ : IsIso (η.app (M ⊗ Q)) := by
    have : IsIso (η.app Q) := hQ
    have he : η.app (M ⊗ Q) =
        M ◁ (η.app Q) ≫ (α_ M Q P).inv := by
      change (ρ_ (M ⊗ Q)).inv ≫ (M ⊗ Q) ◁ u = _
      change (ρ_ (M ⊗ Q)).inv ≫ (M ⊗ Q) ◁ u =
        M ◁ ((ρ_ Q).inv ≫ Q ◁ u) ≫ (α_ M Q P).inv
      rw [whiskerLeft_comp, Category.assoc, associator_inv_naturality_right,
        ← Category.assoc, whiskerLeft_rightUnitor_inv]
      simp
    rw [he]
    infer_instance
  let a : M ⟶ M ⊗ Q := (ρ_ M).inv ≫ M ◁ cokernel.π t
  have : IsIso a := inferInstance
  have h : a ≫ η.app (M ⊗ Q) = η.app M ≫ (tensorRight P).map a := η.naturality a
  have : IsIso (η.app M ≫ (tensorRight P).map a) := by rw [← h]; infer_instance
  exact IsIso.of_isIso_comp_right _ ((tensorRight P).map a)

private noncomputable def sectionScalar
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (s : (unit (rings R)).sections) :
    𝟭 (CategoryTheory.ringedSiteModules.{u} (rings R)) ⟶ 𝟭 _ where
  app M :=
    ⟨{ app := fun U => ModuleCat.ofHom
          (LinearMap.lsmul (R.obj.obj U) (M.val.obj U) (s.val U))
       naturality := by
         intro U V i
         apply ModuleCat.hom_ext
         apply LinearMap.ext
         intro x
         change (s.val V) • M.val.map i x = M.val.map i ((s.val U) • x)
         rw [M.val.map_smul]
         exact congrArg (fun a : R.obj.obj V => a • M.val.map i x) (s.property i).symm }⟩
  naturality {M N} a := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact ((a.val.app U).hom.map_smul (s.val U) x).symm

private theorem monoidal_counit_rightUnitor
    {D E : Type*} [Category D] [Category E] [MonoidalCategory D] [MonoidalCategory E]
    (F : D ⥤ E) [F.Monoidal] {X : D} {M : E} (e : F.obj X ≅ M)
    (e₀ : F.obj (𝟙_ D) ≅ 𝟙_ E) (h₀ : e₀.inv = Functor.LaxMonoidal.ε F) :
    (e.inv ⊗ₘ e₀.inv) ≫ Functor.LaxMonoidal.μ F X (𝟙_ D) ≫
      F.map (ρ_ X).hom ≫ e.hom = (ρ_ M).hom := by
  rw [tensorHom_def, Category.assoc, h₀,
    ← Functor.LaxMonoidal.right_unitality_assoc, rightUnitor_naturality_assoc]
  simp only [Iso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem tensor_rightUnitor_hom
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    (M : CategoryTheory.ringedSiteModules.{u} (rings R)) :
    let := monoidalCategory R
    let S := PresheafOfModules.sheafification (𝟙 (rings R).obj)
    let ε := (PresheafOfModules.sheafificationAdjunction (𝟙 (rings R).obj)).counit
    (tensorObjIsoSheafification M (unit (rings R))).hom ≫
      S.map (ρ_ M.val).hom ≫ ε.app M = (ρ_ M).hom := by
  let := monoidalCategory R
  let S := PresheafOfModules.sheafification (𝟙 (rings R).obj)
  let ε := (PresheafOfModules.sheafificationAdjunction (𝟙 (rings R).obj)).counit
  exact monoidal_counit_rightUnitor S ((asIso ε).app M)
    ((asIso ε).app (unit (rings R))) rfl

set_option backward.isDefEq.respectTransparency false in
private theorem sectionScalar_central
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (s : (unit (rings R)).sections)
    (M : CategoryTheory.ringedSiteModules.{u} (rings R)) :
    let := monoidalCategory R
    (centralScalar (scalar R s)).app M = (sectionScalar R s).app M := by
  let := monoidalCategory R
  let S := PresheafOfModules.sheafification (𝟙 (rings R).obj)
  let ε := (PresheafOfModules.sheafificationAdjunction (𝟙 (rings R).obj)).counit
  have hpre : M.val ◁ (scalar R s).val ≫ (ρ_ M.val).hom =
      (ρ_ M.val).hom ≫ ((sectionScalar R s).app M).val := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x a
    change R.obj.obj U at a
    change (a * (show R.obj.obj U from s.val U)) • x =
      (s.val U) • (a • x)
    rw [mul_smul, smul_comm]
  change (ρ_ M).inv ≫ M ◁ scalar R s ≫ (ρ_ M).hom = _
  apply (cancel_epi (ρ_ M).hom).1
  simp only [Iso.hom_inv_id_assoc]
  rw [← tensor_rightUnitor_hom R M]
  erw [whiskerLeft_tensorObjIsoSheafification_hom_assoc (R := R) M (scalar R s)]
  rw [← Functor.map_comp_assoc, hpre, Functor.map_comp]
  have hε := ε.naturality ((sectionScalar R s).app M)
  change S.map ((sectionScalar R s).app M).val ≫ ε.app M =
    ε.app M ≫ (sectionScalar R s).app M at hε
  simpa only [Category.assoc] using congrArg
    (fun a => (tensorObjIsoSheafification M (unit (rings R))).hom ≫
      S.map (ρ_ M.val).hom ≫ a) hε

private theorem centralScalar_left
    {D : Type*} [Category D] [MonoidalCategory D] [BraidedCategory D]
    (s : End (𝟙_ D)) (M : D) :
    s ▷ M ≫ (λ_ M).hom = (λ_ M).hom ≫ (centralScalar s).app M := by
  change s ▷ M ≫ (λ_ M).hom =
    (λ_ M).hom ≫ ((ρ_ M).inv ≫ M ◁ s ≫ (ρ_ M).hom)
  rw [← braiding_rightUnitor M]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact BraidedCategory.braiding_naturality_left_assoc s M (ρ_ M).hom

private theorem scalar_leftUnitor
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (s : (unit (rings R)).sections)
    (M : CategoryTheory.ringedSiteModules.{u} (rings R)) :
    letI := monoidalCategory R
    scalar R s ▷ M ≫ (λ_ M).hom = (λ_ M).hom ≫ (sectionScalar R s).app M := by
  let := monoidalCategory R
  let := symmetricCategory R
  exact (centralScalar_left (scalar R s) M).trans
    (congrArg ((λ_ M).hom ≫ ·) (sectionScalar_central R s M))

private theorem restriction_colimits
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    PreservesColimitsOfSize.{u, u} (restriction φ) := by
  have h (S : Sheaf J RingCat.{u}) :
      PreservesColimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} S) := by
    constructor
    intro K _
    exact ((moduleSheaves_colimits_forgetful S).2.2.2.2.2 K).2.1
  have := h (rings R)
  have := h (rings B)
  have : ReflectsColimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} (rings R)) :=
    reflectsColimits_of_reflectsIsomorphisms
  have : PreservesColimitsOfSize.{u, u}
      (restriction φ ⋙ SheafOfModules.toSheaf.{u} (rings R)) :=
    inferInstanceAs (PreservesColimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} (rings B)))
  exact preservesColimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf.{u} (rings R))

@[irreducible]
private noncomputable def freeTensorIso
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) (I : Type) :
    letI := monoidalCategory R
    (tensorRight ((restriction φ).obj (unit (rings B)))).obj
        (∐ fun _ : I => unit (rings R)) ≅
      (restriction φ).obj (∐ fun _ : I => unit (rings B)) := by
  let := monoidalCategory R
  have := restriction_colimits φ
  have : PreservesColimitsOfSize.{0, 0} (restriction φ) :=
    preservesSmallestColimits_of_preservesColimits _
  exact PreservesCoproduct.iso _ _ ≪≫ Sigma.mapIso (fun _ => λ_ _) ≪≫
    (PreservesCoproduct.iso (restriction φ) _).symm

@[reassoc]
private theorem freeTensorIso_ι
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) (I : Type) (i : I) :
    letI := monoidalCategory R
    (tensorRight ((restriction φ).obj (unit (rings B)))).map
        (Sigma.ι (fun _ : I => unit (rings R)) i) ≫ (freeTensorIso φ I).hom =
      (λ_ ((restriction φ).obj (unit (rings B)))).hom ≫
        (restriction φ).map (Sigma.ι (fun _ : I => unit (rings B)) i) := by
  let := monoidalCategory R
  have := restriction_colimits φ
  have : PreservesColimitsOfSize.{0, 0} (restriction φ) :=
    preservesSmallestColimits_of_preservesColimits _
  let F := tensorRight ((restriction φ).obj (unit (rings B)))
  let h := fun _ : I => unit (rings R)
  have hi : F.map (Sigma.ι h i) ≫ (PreservesCoproduct.iso F h).hom =
      Sigma.ι (fun _ : I => F.obj (unit (rings R))) i :=
    by
      apply (cancel_mono (PreservesCoproduct.iso F h).inv).1
      rw [Category.assoc, (PreservesCoproduct.iso F h).hom_inv_id, Category.comp_id]
      change F.map (Sigma.ι h i) = _ ≫ sigmaComparison F h
      exact (ι_comp_sigmaComparison F h i).symm
  unfold freeTensorIso
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  erw [reassoc_of% hi, Sigma.ι_mapIso_hom_assoc, PreservesCoproduct.inv_hom,
    ι_comp_sigmaComparison]

set_option backward.isDefEq.respectTransparency false in
private theorem scalar_tensor_unitor
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (s : (unit (rings R)).sections) :
    letI := monoidalCategory R
    (tensorRight ((restriction φ).obj (unit (rings B)))).map (scalar R s) ≫
        (λ_ ((restriction φ).obj (unit (rings B)))).hom =
      (λ_ ((restriction φ).obj (unit (rings B)))).hom ≫
        (restriction φ).map (scalar B (mapSection φ s)) := by
  let := monoidalCategory R
  change scalar R s ▷ ((restriction φ).obj (unit (rings B))) ≫ _ = _
  rw [scalar_leftUnitor]
  congr 1
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change B.obj.obj U at a
  change (φ.hom.app U) (s.val U) * a = a * (φ.hom.app U) (s.val U)
  exact mul_comm _ _

private theorem scalar_pow_tensor_unitor
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (s : (unit (rings R)).sections) (k : ℕ) :
    letI := monoidalCategory R
    (tensorRight ((restriction φ).obj (unit (rings B)))).map (scalar R s ^ k) ≫
        (λ_ ((restriction φ).obj (unit (rings B)))).hom =
      (λ_ ((restriction φ).obj (unit (rings B)))).hom ≫
        (restriction φ).map (scalar B (mapSection φ s) ^ k) := by
  let := monoidalCategory R
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [pow_succ, End.mul_def, Functor.map_comp]
    rw [Category.assoc, ih, ← Category.assoc, scalar_tensor_unitor, Category.assoc]

private theorem row_tensor_unitor
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) :
    letI := monoidalCategory R
    (tensorRight ((restriction φ).obj (unit (rings B)))).map (idealRow R r f) ≫
        (λ_ ((restriction φ).obj (unit (rings B)))).hom =
      (freeTensorIso φ (Fin r)).hom ≫
        (restriction φ).map (idealRow B r (mapSection φ ∘ f)) := by
  let := monoidalCategory R
  let F := tensorRight ((restriction φ).obj (unit (rings B)))
  apply (cancel_epi (sigmaComparison F (fun _ : Fin r => unit (rings R)))).1
  apply Sigma.hom_ext
  intro j
  simp only [ι_comp_sigmaComparison_assoc]
  rw [← F.map_comp_assoc, idealRow, Sigma.ι_desc]
  erw [freeTensorIso_ι_assoc φ (Fin r) j]
  rw [← (restriction φ).map_comp, idealRow, Sigma.ι_desc]
  exact scalar_tensor_unitor φ (f j)

private theorem differential_tensor_unitor
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) (n : ℕ) (q : ℤ) :
    letI := monoidalCategory R
    (tensorRight ((restriction φ).obj (unit (rings B)))).map (differential R r f n q) ≫
        (freeTensorIso φ (Indices r (q + 1))).hom =
      (freeTensorIso φ (Indices r q)).hom ≫
        (restriction φ).map (differential B r (mapSection φ ∘ f) n q) := by
  let := monoidalCategory R
  classical
  dsimp only [term, Indices] at *
  let F := tensorRight ((restriction φ).obj (unit (rings B)))
  apply (cancel_epi (sigmaComparison F (fun _ : Indices r q => unit (rings R)))).1
  apply Sigma.hom_ext
  intro i
  simp only [ι_comp_sigmaComparison_assoc]
  rw [← F.map_comp_assoc, differential, Sigma.ι_desc]
  erw [freeTensorIso_ι_assoc φ (Indices r q) i]
  rw [← (restriction φ).map_comp, differential, Sigma.ι_desc]
  simp only [Functor.map_sum, Preadditive.sum_comp,
    Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hj
  · simp only [Functor.map_zero, zero_comp, comp_zero]
  · simp only [Functor.map_zsmul, Functor.map_comp, Preadditive.zsmul_comp,
      Preadditive.comp_zsmul, Category.assoc, Function.comp_apply]
    erw [freeTensorIso_ι φ (Indices r (q + 1))
      ⟨insert j i.val, insert_degree i j hj⟩]
    rw [← Category.assoc, scalar_pow_tensor_unitor, Category.assoc]

private theorem tensor_unit_unitor
    {D : Type*} [Category D] [MonoidalCategory D] {P : D} (u : 𝟙_ D ⟶ P) :
    (((rightUnitorNatIso D).inv ≫ (tensoringRight D).map u).app (𝟙_ D)) ≫
      (λ_ P).hom = u := by
  dsimp only [NatTrans.comp_app]
  change ((ρ_ (𝟙_ D)).inv ≫ (𝟙_ D) ◁ u) ≫ (λ_ P).hom = _
  rw [Category.assoc]
  rw [leftUnitor_naturality, unitors_equal]
  simp

private theorem quotient_tensor_unit_isIso
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections)
    (hquot : IsIso (quotientComparison φ r f)) :
    letI := monoidalCategory R
    IsIso (((rightUnitorNatIso (CategoryTheory.ringedSiteModules.{u} (rings R))).inv ≫
      (tensoringRight _).map (unitMap φ)).app (cokernel (idealRow R r f))) := by
  let := monoidalCategory R
  have := restriction_colimits φ
  have : PreservesColimitsOfSize.{0, 0} (restriction φ) :=
    preservesSmallestColimits_of_preservesColimits _
  let P := (restriction φ).obj (unit (rings B))
  let F := tensorRight P
  let η : 𝟭 (CategoryTheory.ringedSiteModules.{u} (rings R)) ⟶ F :=
    (rightUnitorNatIso _).inv ≫ (tensoringRight _).map (unitMap φ)
  let a := idealRow R r f
  let b := idealRow B r (mapSection φ ∘ f)
  let cF := (CokernelCofork.ofπ (cokernel.π a) (cokernel.condition a)).map F
  let cG := (CokernelCofork.ofπ (cokernel.π b) (cokernel.condition b)).map (restriction φ)
  let hF : IsColimit cF := CokernelCofork.mapIsColimit _ (cokernelIsCokernel a) F
  let hG : IsColimit cG :=
    CokernelCofork.mapIsColimit _ (cokernelIsCokernel b) (restriction φ)
  let i : Arrow.mk (F.map a) ≅ Arrow.mk ((restriction φ).map b) :=
    Arrow.isoMk (freeTensorIso φ (Fin r)) (λ_ P) (row_tensor_unitor φ r f).symm
  let e : F.obj (cokernel a) ≅ (restriction φ).obj (cokernel b) :=
    CokernelCofork.mapIsoOfIsColimit hF hG i
  have he : F.map (cokernel.π a) ≫ e.hom =
      (λ_ P).hom ≫ (restriction φ).map (cokernel.π b) := by
    exact CokernelCofork.π_mapOfIsColimit hF cG i.hom
  have h : η.app (cokernel a) ≫ e.hom = quotientComparison φ r f := by
    apply (cancel_epi (cokernel.π a)).1
    have hn := η.naturality (cokernel.π a)
    dsimp only [Functor.id_map] at hn
    have hu : η.app (unit (rings R)) ≫ (λ_ P).hom = unitMap φ :=
      tensor_unit_unitor (unitMap φ)
    rw [← Category.assoc, hn, Category.assoc, he, ← Category.assoc, hu]
    exact (cokernel.π_desc _ _ _).symm
  have : IsIso (η.app (cokernel a) ≫ e.hom) := by rw [h]; exact hquot
  exact IsIso.of_isIso_comp_right _ e.hom

@[irreducible]
private noncomputable def koszulTensorIso
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) (n : ℕ) :
    letI := monoidalCategory R
    ((tensorRight ((restriction φ).obj (unit (rings B)))).mapHomologicalComplex
        (.up ℤ)).obj (koszul R r f n) ≅
      ((restriction φ).mapHomologicalComplex (.up ℤ)).obj
        (koszul B r (mapSection φ ∘ f) n) := by
  let := monoidalCategory R
  exact HomologicalComplex.Hom.isoOfComponents (fun q => freeTensorIso φ (Indices r q)) (by
    intro i j hij
    obtain rfl : i + 1 = j := hij
    simpa only [Functor.mapHomologicalComplex_obj_d, koszul, CochainComplex.of_d]
      using (differential_tensor_unitor φ r f n i).symm)

private theorem koszulTensorIso_hom_f
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) (n : ℕ) (q : ℤ) :
    letI := monoidalCategory R
    (koszulTensorIso φ r f n).hom.f q = (freeTensorIso φ (Indices r q)).hom := by
  let := monoidalCategory R
  unfold koszulTensorIso
  rfl

private theorem coproduct_natTrans_comparison
    {D E : Type*} [Category D] [Category E] {X : D} {Y : E}
    (F : D ⥤ D) (η : 𝟭 D ⟶ F) (G : E ⥤ D) (I : Type)
    [HasCoproduct (fun _ : I => X)] [HasCoproduct (fun _ : I => Y)]
    (v : X ⟶ G.obj Y) (l : F.obj X ⟶ G.obj Y)
    (e : F.obj (∐ fun _ : I => X) ⟶ G.obj (∐ fun _ : I => Y))
    (hv : η.app X ≫ l = v)
    (he : ∀ i, F.map (Sigma.ι (fun _ : I => X) i) ≫ e =
      l ≫ G.map (Sigma.ι (fun _ : I => Y) i)) :
    Sigma.desc (fun i => v ≫ G.map (Sigma.ι (fun _ : I => Y) i)) =
      η.app (∐ fun _ : I => X) ≫ e := by
  apply Sigma.hom_ext
  intro i
  have hn := η.naturality (Sigma.ι (fun _ : I => X) i)
  dsimp only [Functor.id_map] at hn
  rw [Sigma.ι_desc, ← hv, Category.assoc, ← he, ← Category.assoc, ← hn,
    Category.assoc]

private theorem koszulTensorIso_comparison
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) (n : ℕ) :
    letI := monoidalCategory R
    let A := CategoryTheory.ringedSiteModules.{u} (rings R)
    let P := (restriction φ).obj (unit (rings B))
    let η : 𝟭 A ⟶ tensorRight P :=
      (rightUnitorNatIso A).inv ≫ (tensoringRight A).map (unitMap φ)
    comparisonStage φ r f n =
      (Functor.mapHomologicalComplexIdIso A (.up ℤ)).inv.app (koszul R r f n) ≫
        (η.mapHomologicalComplex (.up ℤ)).app (koszul R r f n) ≫
          (koszulTensorIso φ r f n).hom := by
  let := monoidalCategory R
  let A := CategoryTheory.ringedSiteModules.{u} (rings R)
  let P := (restriction φ).obj (unit (rings B))
  let F := tensorRight P
  let η : 𝟭 A ⟶ F :=
    (rightUnitorNatIso A).inv ≫ (tensoringRight A).map (unitMap φ)
  apply HomologicalComplex.hom_ext
  intro q
  simp only [HomologicalComplex.comp_f,
    Functor.mapHomologicalComplexIdIso_inv_app_f, Category.id_comp,
    NatTrans.mapHomologicalComplex_app_f, koszulTensorIso_hom_f]
  change comparisonTerm φ r q = η.app (term R r q) ≫
    (freeTensorIso φ (Indices r q)).hom
  exact coproduct_natTrans_comparison F η (restriction φ) (Indices r q)
    (unitMap φ) (λ_ P).hom (freeTensorIso φ (Indices r q)).hom
    (tensor_unit_unitor (unitMap φ)) (freeTensorIso_ι φ (Indices r q))

private theorem sectionScalar_word_zero
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) (k : ℕ)
    (M : CategoryTheory.ringedSiteModules.{u} (rings R))
    (hkill : ∀ (X : Cᵒᵖ) (a : R.obj.obj X),
      a ∈ (Ideal.span (Set.range (fun j : Fin r =>
        (show R.obj.obj X from (f j).val X)))) ^ k →
      ∀ (x : M.val.obj X), a • x = 0) :
    ∀ l : List (Fin r), l.length = k →
      (scalarWord (fun j => sectionScalar R (f j)) l).app M = 0 := by
  let s := fun j : Fin r => sectionScalar R (f j)
  intro l hl
  have hw : ∀ (l : List (Fin r)) (X : Cᵒᵖ) (x : M.val.obj X),
      ((scalarWord s l).app M).val.app X x =
        (l.map (fun j => (show R.obj.obj X from (f j).val X))).prod • x := by
    intro l
    induction l with
    | nil => intro X x; simp [scalarWord]
    | cons j l ih =>
      intro X x
      change ((scalarWord s l).app M).val.app X
        ((show R.obj.obj X from (f j).val X) • x) = _
      rw [ih]
      simp only [List.map_cons, List.prod_cons, mul_smul]
      exact smul_comm _ _ _
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((scalarWord s l).app M).val.app X x = 0
  rw [hw]
  apply hkill X _ ?_ x
  have hm : ∀ l : List (Fin r),
      (l.map (fun j => (show R.obj.obj X from (f j).val X))).prod ∈
        (Ideal.span (Set.range (fun j : Fin r =>
          (show R.obj.obj X from (f j).val X)))) ^ l.length := by
    intro l
    induction l with
    | nil => simp
    | cons j l ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ']
      exact Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_range_self j)) ih
  simpa only [hl] using hm l


private theorem flat_torsion_tensor_unit_isIso
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) (k : ℕ)
    (M : CategoryTheory.ringedSiteModules.{u} (rings R))
    (hflat : IsFlat ((restriction φ).obj (unit (rings B))))
    (hquot : IsIso (quotientComparison φ r f))
    (hkill : ∀ (X : Cᵒᵖ) (a : R.obj.obj X),
      a ∈ (Ideal.span (Set.range (fun j : Fin r =>
        (show R.obj.obj X from (f j).val X)))) ^ k →
      ∀ (x : M.val.obj X), a • x = 0) :
    letI := monoidalCategory R
    IsIso (((rightUnitorNatIso (CategoryTheory.ringedSiteModules.{u} (rings R))).inv ≫
      (tensoringRight _).map (unitMap φ)).app M) := by
  let := monoidalCategory R
  let A := CategoryTheory.ringedSiteModules.{u} (rings R)
  let P := (restriction φ).obj (unit (rings B))
  let F := tensorRight P
  let η : 𝟭 A ⟶ F :=
    (rightUnitorNatIso A).inv ≫ (tensoringRight A).map (unitMap φ)
  have : PreservesFiniteLimits F := hflat.1
  have : PreservesFiniteColimits F := hflat.2
  let s := fun j : Fin r => sectionScalar R (f j)
  apply exact_natTrans_nilpotent F η s
    (fun N hN => tensor_unit_on_killed (unitMap φ) (fun j => scalar R (f j))
      (quotient_tensor_unit_isIso φ r f hquot) N (fun j =>
        (sectionScalar_central R (f j) N).trans (hN j))) k M
  exact sectionScalar_word_zero R r f k M hkill

/-- The tensor unit map is invertible on a Koszul cohomology sheaf annihilated
by a uniform positive ideal power, and finite free scalar extension realizes the target stage.
Source: Stacks Project, Tag 099H, using the sheaf tensor argument of Tag 0GLY
and the ideal-power induction of Tag 05E9
(blueprint: lem-weil-pbc-flat-localization-koszul-cohomology-comparison).

Proof: multiplication by each f_j is a natural endomorphism of the identity
functor on module sheaves. Every word of length N=r*(n+1)+1 in these
endomorphisms kills H, since its sectionwise scalar belongs to the N-th ideal power.
No evaluation functor is assumed to commute with cohomology or quotients.

First consider M killed by every f_j. Let Q be the cokernel of the ideal row.
Tensoring its presentation with M makes the row zero, so M tensor Q is canonically
isomorphic to M. Tensor the finite free ideal row with B. The unitors and coproduct
comparisons identify its cokernel map with quotientComparison, hence the canonical
tensor unit on Q is invertible. Associativity identifies the unit on M tensor Q
with M tensored with the unit on Q, followed by the inverse associator.
Consequently the unit on M is invertible by naturality.

Induct on the annihilating word length. The length-zero case is a zero object.
For the successor case take the image N of the row from the coproduct of r copies
of M to M whose components multiply by f_j. Every word of one smaller length
kills N: precompose with the epimorphism onto the image and check each summand,
then cancel the image inclusion. The cokernel is killed by every f_j, by naturality
and the cokernel relation. The sequence N -> M -> cokernel(row) is short exact.
Flat tensoring preserves it, and the short five lemma applies to the natural
unit transformation and the isomorphisms on the outer terms. Apply this to H.

Finally, tensoring the finite free source Koszul complex with B gives the target
Koszul complex after restriction of scalars: distribute tensor over the finite
coproducts, send e_S tensor b to b e_S, and check insertion coefficients.
The resulting isomorphism e carries the natural tensor unit transformation on the
complex to comparisonStage, with the canonical identity-functor comparison inserted
on its source. This is an identity of complex maps, checked on each coproduct basis
in every degree, rather than only an assertion about their homology maps.
The conclusions are the canonical tensor map on H being invertible and this compatible
finite free complex isomorphism; exact-functor homology is not part of this lemma. -/
theorem flat_koszul_tensor_comparison_data
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R B : Sheaf J CommRingCat.{u}) (φ : R ⟶ B) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) (n : ℕ) (q : ℤ)
    (hr : 0 < r) (hq : 0 ≤ q ∧ q ≤ (r : ℤ))
    (hflat : IsFlat ((restriction φ).obj (unit (rings B))))
    (hquot : IsIso (quotientComparison φ r f))
    (hkill : ∀ (X : Cᵒᵖ) (a : R.obj.obj X),
      a ∈ (Ideal.span (Set.range (fun j : Fin r ↦
        (show R.obj.obj X from (f j).val X)))) ^ (r * (n + 1) + 1) →
      ∀ (x : ((koszul R r f n).homology q).val.obj X), a • x = 0) :
    letI := monoidalCategory R
    let A := CategoryTheory.ringedSiteModules.{u} (rings R)
    let P := (restriction φ).obj (unit (rings B))
    let F := tensorRight P
    let η : 𝟭 A ⟶ F :=
      (rightUnitorNatIso A).inv ≫ (tensoringRight A).map (unitMap φ)
    IsIso (η.app ((koszul R r f n).homology q)) ∧
      ∃ e : (F.mapHomologicalComplex (.up ℤ)).obj (koszul R r f n) ≅
          ((restriction φ).mapHomologicalComplex (.up ℤ)).obj
            (koszul B r (mapSection φ ∘ f) n),
        comparisonStage φ r f n =
          (Functor.mapHomologicalComplexIdIso A (.up ℤ)).inv.app (koszul R r f n) ≫
          (η.mapHomologicalComplex (.up ℤ)).app (koszul R r f n) ≫ e.hom := by
  have _hr := hr
  have _hq := hq
  let := monoidalCategory R
  exact ⟨flat_torsion_tensor_unit_isIso φ r f (r * (n + 1) + 1)
    ((koszul R r f n).homology q) hflat hquot hkill,
    koszulTensorIso φ r f n, koszulTensorIso_comparison φ r f n⟩

end SheafOfModules.LocalizationCech
