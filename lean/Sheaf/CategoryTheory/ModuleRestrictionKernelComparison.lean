/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.CategoryTheory.LeftModuleDerivedEvaluationForget
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.InjectiveSheafMonoRestriction
import WeilConjectures.CategoryTheory.RightDerivedInjectiveSequence
import WeilConjectures.CategoryTheory.RightDerivedZeroTransformation
import WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
import WeilConjectures.CategoryTheory.Sites.CohomologyRightDerivedSections
import Sheaf.CategoryTheory.RightDerivedBaseChangeZeroUnit

/-! # Forgetting scalars and derived restriction kernels

Source: Stacks Project, sites-cohomology.tex, Tags 093X and 03FD; injectives.tex,
Tag 01DU; derived.tex, Tags 013K, 070J, 070I, 05TI and 05TH; homology.tex, Tags 0117
and 05QB (blueprint: lem-pur-module-restriction-kernel-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u w uB vB uD vD
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.ModuleRestrictionKernel

open ConstantLeftModuleInverseImage LeftModuleDerivedEvaluation

/-- The actual kernel of module restriction, with the induced action on morphisms.
Source: Stacks, 093X and the restriction-kernel refinement of 03FD
(blueprint: lem-pur-module-restriction-kernel-comparison). -/
def S
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Type u) [Ring A] [HasWeakSheafify J RingCat.{u}]
    {W T : C} (m : W ⟶ T) : ConstantLeftModuleInverseImage.Modules J A ⥤ ModuleCat.{u} A := by
  let r := LeftModuleDerivedEvaluation.restriction J A m
  exact {
    obj := fun M => kernel (r.app M)
    map := fun {M N} f => kernel.lift (r.app N)
      (kernel.ι (r.app M) ≫ (LeftModuleDerivedEvaluation.G J A T).map f) (by
        rw [Category.assoc, r.naturality f]
        rw [← Category.assoc, kernel.condition, zero_comp])
    map_id := by
      intro M
      apply (cancel_mono (kernel.ι _)).1
      rw [kernel.lift_ι]
      simp only [Functor.map_id, Category.comp_id, Category.id_comp]
    map_comp := by
      intro M N P f g
      apply (cancel_mono (kernel.ι _)).1
      rw [kernel.lift_ι]
      simp [Category.assoc]
  }

/-- The actual kernel of abelian restriction, with the induced action on morphisms.
Source: Stacks, 093X and the restriction-kernel refinement of 03FD
(blueprint: lem-pur-module-restriction-kernel-comparison). -/
def S₀
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    {W T : C} (m : W ⟶ T) : Sheaf J AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} := by
  let r := LeftModuleDerivedEvaluation.restriction₀ J m
  exact {
    obj := fun M => kernel (r.app M)
    map := fun {M N} f => kernel.lift (r.app N)
      (kernel.ι (r.app M) ≫ (LeftModuleDerivedEvaluation.G₀ J T).map f) (by
        rw [Category.assoc, r.naturality f]
        rw [← Category.assoc, kernel.condition, zero_comp])
    map_id := by
      intro M
      apply (cancel_mono (kernel.ι _)).1
      rw [kernel.lift_ι]
      simp
    map_comp := by
      intro M N P f g
      apply (cancel_mono (kernel.ι _)).1
      rw [kernel.lift_ι]
      simp [Category.assoc]
  }

private theorem kernelLeftExact
    {B : Type uB} {D : Type uD} [Category.{vB} B] [Category.{vD} D]
    [HasZeroMorphisms D] (F G K : B ⥤ D) (r : F ⟶ G) (ι : K ⟶ F)
    [∀ X, Mono (ι.app X)] (hι : ∀ X, ι.app X ≫ r.app X = 0)
    (hk : ∀ X, IsLimit (KernelFork.ofι (ι.app X) (hι X)))
    [PreservesFiniteLimits F] [PreservesFiniteLimits G] : PreservesFiniteLimits K := by
  constructor
  intro H _ _
  constructor
  intro d
  constructor
  intro c hc
  let hf := isLimitOfPreserves F hc
  let hg := isLimitOfPreserves G hc
  let a (s : Cone (d ⋙ K)) : Cone (d ⋙ F) :=
    (Cone.postcompose (Functor.whiskerLeft d ι)).obj s
  have hl (s : Cone (d ⋙ K)) : hf.lift (a s) ≫ r.app c.pt = 0 := by
    apply hg.hom_ext
    intro j
    change (hf.lift (a s) ≫ r.app c.pt) ≫ G.map (c.π.app j) = _
    rw [Category.assoc, ← r.naturality, ← Category.assoc]
    rw [show hf.lift (a s) ≫ F.map (c.π.app j) = (a s).π.app j from hf.fac (a s) j]
    change (s.π.app j ≫ ι.app (d.obj j)) ≫ r.app (d.obj j) = _
    rw [Category.assoc, hι, comp_zero, zero_comp]
  let l (s : Cone (d ⋙ K)) := KernelFork.IsLimit.lift' (hk c.pt) (hf.lift (a s)) (hl s)
  have hlι (s : Cone (d ⋙ K)) : (l s).1 ≫ ι.app c.pt = hf.lift (a s) := (l s).2
  refine ⟨{ lift := fun s ↦ (l s).1, fac := ?_, uniq := ?_ }⟩
  · intro s j
    apply (cancel_mono (ι.app (d.obj j))).1
    change ((l s).1 ≫ K.map (c.π.app j)) ≫ ι.app (d.obj j) = _
    rw [Category.assoc]
    rw [ι.naturality, ← Category.assoc, hlι s]
    exact hf.fac (a s) j
  · intro s b hb
    apply (cancel_mono (ι.app c.pt)).1
    rw [hlι s]
    apply hf.hom_ext
    intro j
    change (b ≫ ι.app c.pt) ≫ F.map (c.π.app j) = _
    rw [Category.assoc, ← ι.naturality, ← Category.assoc]
    rw [show b ≫ K.map (c.π.app j) = s.π.app j from hb j]
    exact (hf.fac (a s) j).symm

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (A : Type u) [CommRing A] [HasWeakSheafify J RingCat.{u}]
  {W T : C} (m : W ⟶ T)

/-- Additivity of module restriction kernels.
Source: Stacks, 03DA and 093X
(blueprint: lem-pur-module-restriction-kernel-comparison).
Proof: evaluation and restriction are additive; the induced kernel maps preserve
addition because their composites with the monic kernel inclusion do. -/
theorem sAdditiveProof : (S J A m).Additive := by
  constructor
  intro M N f g
  apply (cancel_mono (kernel.ι ((restriction J A m).app N))).1
  change kernel.lift _ _ _ ≫ _ = (kernel.lift _ _ _ + kernel.lift _ _ _) ≫ _
  simp only [kernel.lift_ι, Preadditive.add_comp, Functor.map_add, Preadditive.comp_add]

/-- Additivity of the actual module restriction-kernel functor.
Source: Stacks, 03DA/093X/01DU
(blueprint: lem-pur-module-restriction-kernel-comparison). -/
instance sAdditive : (S J A m).Additive :=
  sAdditiveProof J A m

omit [HasWeakSheafify J RingCat.{u}] in
/-- Additivity of abelian restriction kernels.
Source: Stacks, 01FT and 093X
(blueprint: lem-pur-module-restriction-kernel-comparison).
Proof: evaluation is additive. Composing the induced maps with the monic kernel
inclusion reduces addition to sectionwise addition. -/
theorem s₀AdditiveProof : (S₀ J m).Additive := by
  constructor
  intro M N f g
  apply (cancel_mono (kernel.ι ((restriction₀ J m).app N))).1
  change kernel.lift _ _ _ ≫ _ = (kernel.lift _ _ _ + kernel.lift _ _ _) ≫ _
  simp only [kernel.lift_ι, Preadditive.add_comp, Functor.map_add, Preadditive.comp_add]

/-- Additivity of the actual abelian restriction-kernel functor.
Source: Stacks, 03DA/093X/01DU
(blueprint: lem-pur-module-restriction-kernel-comparison). -/
instance s₀Additive : (S₀ J m).Additive :=
  s₀AdditiveProof J m

/-- Left exactness of module restriction kernels.
Source: Stacks, 03DA and 093X
(blueprint: lem-pur-module-restriction-kernel-comparison).
Proof: evaluation preserves finite limits. Kernels commute with finite limits,
so taking the kernel of the restriction natural transformation does also. -/
theorem sLeftExact : PreservesFiniteLimits (S J A m) := by
  let ι : S J A m ⟶ G J A T :=
    { app := fun M ↦ kernel.ι ((restriction J A m).app M)
      naturality := by
        intro M N f
        exact (kernel.lift_ι ((restriction J A m).app N)
          (kernel.ι ((restriction J A m).app M) ≫ (G J A T).map f) _) }
  let : ∀ M, Mono (ι.app M) := fun M ↦ by dsimp [ι]; infer_instance
  let : PreservesFiniteLimits (G J A T ⋙ v A) := inferInstanceAs
    (PreservesFiniteLimits (V J A ⋙ sheafToPresheaf J AddCommGrpCat.{u} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op T)))
  let : PreservesFiniteLimits (G J A W ⋙ v A) := inferInstanceAs
    (PreservesFiniteLimits (V J A ⋙ sheafToPresheaf J AddCommGrpCat.{u} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op W)))
  let : PreservesFiniteLimits (G J A T) :=
    preservesFiniteLimits_of_reflects_of_preserves (G J A T) (v A)
  let : PreservesFiniteLimits (G J A W) :=
    preservesFiniteLimits_of_reflects_of_preserves (G J A W) (v A)
  exact kernelLeftExact (G J A T) (G J A W) (S J A m) (restriction J A m) ι
    (fun M ↦ kernel.condition _) (fun M ↦ kernelIsKernel _)

omit [HasWeakSheafify J RingCat.{u}] in
/-- Left exactness of abelian restriction kernels.
Source: Stacks, 01FT and 093X
(blueprint: lem-pur-module-restriction-kernel-comparison).
Proof: finite limits of sheaves are sectionwise; taking a kernel commutes with
finite limits. Therefore the restriction-kernel functor preserves them. -/
theorem s₀LeftExact : PreservesFiniteLimits (S₀ J m) := by
  let ι : S₀ J m ⟶ G₀ J T :=
    { app := fun M ↦ kernel.ι ((restriction₀ J m).app M)
      naturality := by
        intro M N f
        exact (kernel.lift_ι ((restriction₀ J m).app N)
          (kernel.ι ((restriction₀ J m).app M) ≫ (G₀ J T).map f) _) }
  let : ∀ M, Mono (ι.app M) := fun M ↦ by dsimp [ι]; infer_instance
  let : PreservesFiniteLimits (G₀ J T) := inferInstanceAs
    (PreservesFiniteLimits (sheafToPresheaf J AddCommGrpCat.{u} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op T)))
  let : PreservesFiniteLimits (G₀ J W) := inferInstanceAs
    (PreservesFiniteLimits (sheafToPresheaf J AddCommGrpCat.{u} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op W)))
  exact kernelLeftExact (G₀ J T) (G₀ J W) (S₀ J m) (restriction₀ J m) ι
    (fun M ↦ kernel.condition _) (fun M ↦ kernelIsKernel _)

/-- The canonical scalar-forgetting kernel isomorphism on each object.
Source: Stacks, 03DA/03FD
(blueprint: lem-pur-module-restriction-kernel-comparison). -/
def kernelIdentityObj (M : Modules J A) :
    (v A).obj ((S J A m).obj M) ≅ (S₀ J m).obj ((V J A).obj M) :=
  PreservesKernel.iso (v A) ((restriction J A m).app M)

/-- Naturality of the kernel-preservation comparison.
Source: Stacks, 03DA/03FD
(blueprint: lem-pur-module-restriction-kernel-comparison).
Proof: compose both maps with the monic target kernel inclusion. Both composites
are the underlying section map followed by the source inclusion; kernel
uniqueness gives the equation. -/
theorem kernelIdentity_naturality {M N : Modules J A} (f : M ⟶ N) :
    (S J A m ⋙ v A).map f ≫ (kernelIdentityObj J A m N).hom =
      (kernelIdentityObj J A m M).hom ≫ (V J A ⋙ S₀ J m).map f := by
  apply (cancel_mono (kernel.ι ((v A).map ((restriction J A m).app N)))).1
  dsimp only [Functor.comp_map, kernelIdentityObj]
  simp only [PreservesKernel.iso_hom, Category.assoc, kernelComparison_comp_ι]
  change (v A).map (kernel.lift _ _ _) ≫ _ =
    kernelComparison _ (v A) ≫ kernel.lift _ _ _ ≫ _
  erw [kernel.lift_ι, ← Functor.map_comp, kernel.lift_ι]
  erw [← Category.assoc, kernelComparison_comp_ι]
  rfl

/-- The underived identity, expressed by canonical kernel preservation rather than
an equality between chosen categorical limit objects.
Source: Stacks, 03DA/03FD
(blueprint: lem-pur-module-restriction-kernel-comparison). -/
def kernelIdentity : S J A m ⋙ v A ≅ V J A ⋙ S₀ J m :=
  NatIso.ofComponents (kernelIdentityObj J A m) (kernelIdentity_naturality J A m)

/-- Enough injectives for constant module sheaves on the small site.
Source: Stacks, Injectives, 01DU
(blueprint: lem-pur-module-restriction-kernel-comparison).
Proof: module sheaves form a Grothendieck abelian category. The functorial
injective embedding theorem embeds every object monomorphically into an
injective object. The abelian structure is Mathlib's sectionwise-kernel,
sheafified-cokernel structure on `SheafOfModules`. -/
theorem moduleEnoughInjectivesProof : EnoughInjectives (Modules J A) := by
  let := SheafOfModules.isGrothendieckAbelian
    ((constantSheaf J RingCat.{u}).obj (RingCat.of A))
  infer_instance

/-- Enough injectives, installed from the separately named existence theorem.
Source: Stacks, 03DA/093X/01DU
(blueprint: lem-pur-module-restriction-kernel-comparison). -/
instance moduleEnoughInjectives : EnoughInjectives (Modules J A) :=
  moduleEnoughInjectivesProof J A

private theorem moduleRestrictionSurjective [Mono m] (I : Modules J A) [Injective I] :
    Function.Surjective ((restriction J A m).app I) := by
  let R := (constantSheaf J RingCat.{u}).obj (RingCat.of A)
  let adj := PresheafOfModules.sheafificationAdjunction.{u} (𝟙 R.obj)
  let M := (SheafOfModules.forget R ⋙
    PresheafOfModules.restrictScalars (𝟙 R.obj)).obj I
  have : Injective M := Injective.injective_of_adjoint adj I
  let a := (PresheafOfModules.free R.obj).map (yoneda.map m)
  have : Mono a := PresheafOfModules.mono_of_injective (fun {U} ↦ by
    change Function.Injective (Finsupp.mapDomain (fun f : U.unop ⟶ W ↦ f ≫ m))
    exact Finsupp.mapDomain_injective (fun f g h ↦ (cancel_mono m).mp h))
  intro s
  let b : (PresheafOfModules.free R.obj).obj (yoneda.obj W) ⟶ M :=
    PresheafOfModules.freeYonedaEquiv.symm s
  obtain ⟨g, hg⟩ := Injective.factors b a
  refine ⟨PresheafOfModules.freeYonedaEquiv g, ?_⟩
  have h := congrArg PresheafOfModules.freeYonedaEquiv hg
  rw [Equiv.apply_symm_apply] at h
  change M.map m.op (PresheafOfModules.freeYonedaEquiv g) = s
  rw [← h]
  change M.map m.op (g.app (op T) (ModuleCat.freeMk (𝟙 T))) =
    g.app (op W) (a.app (op W) (ModuleCat.freeMk (𝟙 W)))
  rw [← PresheafOfModules.naturality_apply g m.op]
  simp [a, PresheafOfModules.free, PresheafOfModules.freeObj,
    ModuleCat.free_map_apply, ModuleCat.freeDesc_apply]

private def inclusion : S₀ J m ⟶ G₀ J T where
  app M := kernel.ι ((restriction₀ J m).app M)
  naturality _ _ _ := kernel.lift_ι _ _ _

omit [HasWeakSheafify J RingCat.{u}] in
private theorem abelianRestrictionSurjective [Mono m]
    (I : Sheaf J AddCommGrpCat.{u}) [Injective I] :
    Function.Surjective ((restriction₀ J m).app I) :=
  injective_sheaf_mono_restriction J I m

private theorem forgottenEvaluationAcyclic (U : C) (I : Modules J A) [Injective I] :
    (G₀ J U).rightAcyclic ((V J A).obj I) := by
  let : HasExt.{u} (Sheaf J AddCommGrpCat.{u}) := hasExt_of_enoughInjectives _
  intro n
  let : Subsingleton (Sheaf.H' ((V J A).obj I) (n + 1) U) :=
    injective_module_abelian_acyclic U I (n + 1) (Nat.succ_pos n)
  obtain ⟨e⟩ := Sheaf.nonempty_cohomologyPresheafFunctor_eval_iso_rightDerived J U (n + 1)
  exact (AddCommGrpCat.isZero_of_subsingleton
    (Sheaf.H' ((V J A).obj I) (n + 1) U)).of_iso (e.app ((V J A).obj I)).symm

private theorem forgottenKernelAcyclic [Mono m] (I : Modules J A) [Injective I] :
    (S₀ J m).rightAcyclic ((V J A).obj I) := by
  let : PreservesFiniteLimits (G₀ J T) := inferInstanceAs
    (PreservesFiniteLimits (sheafToPresheaf J AddCommGrpCat.{u} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op T)))
  let : PreservesFiniteLimits (G₀ J W) := inferInstanceAs
    (PreservesFiniteLimits (sheafToPresheaf J AddCommGrpCat.{u} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op W)))
  obtain ⟨δ, hδ⟩ := rightDerived_injective_sequence (S₀ J m) (G₀ J T) (G₀ J W)
    (inclusion J m) (restriction₀ J m)
    (fun M _ ↦ (AddCommGrpCat.mono_iff_injective _).1
      (show Mono (kernel.ι ((restriction₀ J m).app M)) from inferInstance))
    (fun M _ ↦ (ShortComplex.ab_exact_iff_function_exact _).1
      (ShortComplex.exact_kernel ((restriction₀ J m).app M)))
    (fun M hM ↦ abelianRestrictionSurjective J m M)
  have hepi : Epi (((restriction₀ J m).rightDerived 0).app ((V J A).obj I)) := by
    have hs : Epi ((restriction₀ J m).app ((V J A).obj I)) :=
      (AddCommGrpCat.epi_iff_surjective _).2 (moduleRestrictionSurjective J A m I)
    have he := rightDerived_zero_transformation (restriction₀ J m) ((V J A).obj I)
    have : Epi ((G₀ J T).toRightDerivedZero.app ((V J A).obj I) ≫
        ((restriction₀ J m).rightDerived 0).app ((V J A).obj I)) := by
      rw [he]
      infer_instance
    exact epi_of_epi ((G₀ J T).toRightDerivedZero.app ((V J A).obj I)) _
  intro n
  suffices h : ∀ x : ((S₀ J m).rightDerived (n + 1)).obj ((V J A).obj I), x = 0 by
    let : Subsingleton (((S₀ J m).rightDerived (n + 1)).obj ((V J A).obj I)) :=
      ⟨fun x y ↦ (h x).trans (h y).symm⟩
    exact AddCommGrpCat.isZero_of_subsingleton _
  intro x
  have hx : ((inclusion J m).rightDerived (n + 1)).app ((V J A).obj I) x = 0 :=
    (AddCommGrpCat.subsingleton_of_isZero (forgottenEvaluationAcyclic J A T I n)).elim _ _
  obtain ⟨y, hy⟩ := (hδ ((V J A).obj I) n).2.2 x |>.mp hx
  rw [← hy]
  cases n with
  | zero =>
    obtain ⟨z, rfl⟩ := (AddCommGrpCat.epi_iff_surjective _).1 hepi y
    exact (hδ ((V J A).obj I) 0).2.1.apply_apply_eq_zero z
  | succ n =>
    have hy0 : y = 0 :=
      (AddCommGrpCat.subsingleton_of_isZero (forgottenEvaluationAcyclic J A W I n)).elim _ _
    rw [hy0, map_zero]

variable [HasDerivedCategory.{w} (Modules J A)]
  [HasDerivedCategory.{w} (Sheaf J AddCommGrpCat.{u})]
  [HasDerivedCategory.{w} (ModuleCat.{u} A)] [HasDerivedCategory.{w} AddCommGrpCat.{u}]

/-- The canonical derived comparison induced by the identity on restriction kernels.
Source: Stacks, 03FD/05TI/05TH, restriction-kernel refinement
(blueprint: lem-pur-module-restriction-kernel-comparison). -/
def comparison :
    (S J A m).rightDerivedFunctorPlus ⋙ (v A).mapDerivedCategoryPlus ⟶
      (V J A).mapDerivedCategoryPlus ⋙ (S₀ J m).rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusBaseChange (kernelIdentity J A m).hom

/-- A restriction-kernel row, with its specified kernel inclusion.
Source: Stacks, 093X (blueprint: lem-pur-module-restriction-kernel-comparison). -/
def row (M : Sheaf J AddCommGrpCat.{u}) : ShortComplex AddCommGrpCat.{u} :=
  ShortComplex.mk (kernel.ι ((restriction₀ J m).app M))
    ((restriction₀ J m).app M) (kernel.condition _)

/-- The unit computation on a bounded-below complex, with no chosen resolution.
Source: Stacks, 05TI/05TH
(blueprint: lem-pur-module-restriction-kernel-comparison). -/
abbrev compute {B : Type uB} {D : Type uD} [Category.{vB} B] [Category.{vD} D]
    [Abelian B] [Abelian D]
    [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} D] [EnoughInjectives B]
    (F : B ⥤ D) [F.Additive] (L : CochainComplex.Plus B) :
    DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj L) ⟶
      F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj L) :=
  F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient B).obj L)

/-- The underived kernel identity applied to every term of a bounded-below complex.
Source: Stacks, 03DA/03FD
(blueprint: lem-pur-module-restriction-kernel-comparison). -/
def kernelComplexIdentity (L : CochainComplex.Plus (Modules J A)) :
    (v A).mapCochainComplexPlus.obj ((S J A m).mapCochainComplexPlus.obj L) ≅
      (S₀ J m).mapCochainComplexPlus.obj ((V J A).mapCochainComplexPlus.obj L) :=
  (CochainComplex.Plus.ι AddCommGrpCat.{u}).preimageIso
    ((NatIso.mapHomologicalComplex (kernelIdentity J A m) (.up ℤ)).app L.obj)

/-- The computation map for the scalar-forgotten module kernel complex.
Source: Stacks, 05TI/05TH, using the exact scalar-forgetting localization factor
(blueprint: lem-pur-module-restriction-kernel-comparison). -/
def forgetCompute (F : Modules J A ⥤ ModuleCat.{u} A) [F.Additive]
    (L : CochainComplex.Plus (Modules J A)) :
    DerivedCategory.Plus.Q.obj
        ((v A).mapCochainComplexPlus.obj (F.mapCochainComplexPlus.obj L)) ⟶
      (v A).mapDerivedCategoryPlus.obj
        (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj L)) :=
  (v A).mapDerivedCategoryPlusFactorsh.inv.app
      (F.mapHomotopyCategoryPlus.obj
        ((HomotopyCategory.Plus.quotient (Modules J A)).obj L)) ≫
    (v A).mapDerivedCategoryPlus.map (compute F L)

/-- The chain map on actual scalar-forgotten module kernel complexes induced by `q`.
Source: Stacks, 093X/03FD and homology 0117
(blueprint: lem-pur-module-restriction-kernel-comparison). -/
def kernelMap (L : CochainComplex.Plus (Modules J A))
    (N : CochainComplex.Plus (Sheaf J AddCommGrpCat.{u}))
    (q : (V J A).mapCochainComplexPlus.obj L ⟶ N) :
    (v A).mapCochainComplexPlus.obj ((S J A m).mapCochainComplexPlus.obj L) ⟶
      (S₀ J m).mapCochainComplexPlus.obj N :=
  (kernelComplexIdentity J A m L).hom ≫ (S₀ J m).mapCochainComplexPlus.map q

/-- The identity on underlying evaluated complexes.
Source: Stacks, 03FD (blueprint: lem-pur-module-restriction-kernel-comparison). -/
def evaluationComplexIdentity (U : C) (L : CochainComplex.Plus (Modules J A)) :
    (v A).mapCochainComplexPlus.obj ((G J A U).mapCochainComplexPlus.obj L) ≅
      (G₀ J U).mapCochainComplexPlus.obj ((V J A).mapCochainComplexPlus.obj L) :=
  (CochainComplex.Plus.ι AddCommGrpCat.{u}).preimageIso
    ((NatIso.mapHomologicalComplex (evaluationIdentity J A U) (.up ℤ)).app L.obj)

/-- The evaluation of the specified comparison map, retaining scalar forgetting.
Source: Stacks, 03FD (blueprint: lem-pur-module-restriction-kernel-comparison). -/
def evaluationMap (U : C) (L : CochainComplex.Plus (Modules J A))
    (N : CochainComplex.Plus (Sheaf J AddCommGrpCat.{u}))
    (q : (V J A).mapCochainComplexPlus.obj L ⟶ N) :
    (v A).mapCochainComplexPlus.obj ((G J A U).mapCochainComplexPlus.obj L) ⟶
      (G₀ J U).mapCochainComplexPlus.obj N :=
  (evaluationComplexIdentity J A U L).hom ≫ (G₀ J U).mapCochainComplexPlus.map q

private def complexIdentity
    (F : Modules J A ⥤ ModuleCat.{u} A) [F.Additive]
    (H : Sheaf J AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u}) [H.Additive]
    (e : F ⋙ v A ≅ V J A ⋙ H) (L : CochainComplex.Plus (Modules J A)) :
    (v A).mapCochainComplexPlus.obj (F.mapCochainComplexPlus.obj L) ≅
      H.mapCochainComplexPlus.obj ((V J A).mapCochainComplexPlus.obj L) :=
  (CochainComplex.Plus.ι AddCommGrpCat.{u}).preimageIso
    ((NatIso.mapHomologicalComplex e (.up ℤ)).app L.obj)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem comparisonCompute
    (F : Modules J A ⥤ ModuleCat.{u} A) [F.Additive]
    (H : Sheaf J AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u}) [H.Additive]
    (e : F ⋙ v A ≅ V J A ⋙ H)
    (K : DerivedCategory.Plus (Modules J A))
    (L : CochainComplex.Plus (Modules J A))
    (N : CochainComplex.Plus (Sheaf J AddCommGrpCat.{u}))
    (eL : DerivedCategory.Plus.Q.obj L ≅ K)
    (eN : DerivedCategory.Plus.Q.obj N ≅ (V J A).mapDerivedCategoryPlus.obj K)
    (q : (V J A).mapCochainComplexPlus.obj L ⟶ N)
    (he : (V J A).mapDerivedCategoryPlus.map eL.hom ≫ eN.inv =
      (V J A).mapDerivedCategoryPlusFactorsh.hom.app
        ((HomotopyCategory.Plus.quotient (Modules J A)).obj L) ≫
      DerivedCategory.Plus.Q.map q) :
    forgetCompute J A F L ≫
        (v A).mapDerivedCategoryPlus.map (F.rightDerivedFunctorPlus.map eL.hom) ≫
        (Functor.rightDerivedFunctorPlusBaseChange e.hom).app K =
      DerivedCategory.Plus.Q.map
          ((complexIdentity J A F H e L).hom ≫ H.mapCochainComplexPlus.map q) ≫
        compute H N ≫ H.rightDerivedFunctorPlus.map eN.hom := by
  let M := (HomotopyCategory.Plus.quotient (Modules J A)).obj L
  change _ = _
  have hf := congr_app (Functor.rightDerivedFunctorPlusBaseChange_fac e.hom) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.comp_id] at hf
  have hc : (NatTrans.mapHomotopyCategoryPlus e.hom).app M =
      (HomotopyCategory.Plus.quotient AddCommGrpCat.{u}).map
        (complexIdentity J A F H e L).hom := by
    apply (HomotopyCategory.Plus.ι AddCommGrpCat.{u}).map_injective
    rw [NatTrans.ι_map_mapHomotopyCategoryPlus_app]
    change (HomotopyCategory.quotient _ _).map _ =
      (HomotopyCategory.quotient _ _).map
        ((CochainComplex.Plus.ι _).map (complexIdentity J A F H e L).hom)
    rw [complexIdentity, Functor.preimageIso_hom, Functor.map_preimage]
    rfl
  have hf' : forgetCompute J A F L ≫
      (Functor.rightDerivedFunctorPlusBaseChange e.hom).app (DerivedCategory.Plus.Q.obj L) =
      DerivedCategory.Plus.Q.map (complexIdentity J A F H e L).hom ≫
        compute H ((V J A).mapCochainComplexPlus.obj L) ≫
        H.rightDerivedFunctorPlus.map ((V J A).mapDerivedCategoryPlusFactorsh.inv.app M) := by
    dsimp only [forgetCompute, compute]
    rw [Category.assoc]
    change (v A).mapDerivedCategoryPlusFactorsh.inv.app
      (F.mapHomotopyCategoryPlus.obj M) ≫
      ((v A).mapDerivedCategoryPlus.map (F.rightDerivedFunctorPlusUnit.app M) ≫
      (Functor.rightDerivedFunctorPlusBaseChange e.hom).app
        (DerivedCategory.Plus.Qh.obj M)) = _
    rw [hf]
    simp only [Functor.rightDerivedFunctorPlusBaseChangeAux, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id,
      Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app,
      Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app, Functor.map_id]
    erw [Iso.inv_hom_id_app_assoc]
    erw [Category.id_comp, Category.id_comp]
    rw [hc]
    rfl
  have he' : (V J A).mapDerivedCategoryPlusFactorsh.inv.app M ≫
      (V J A).mapDerivedCategoryPlus.map eL.hom =
      DerivedCategory.Plus.Q.map q ≫ eN.hom := by
    have h := congrArg (fun f ↦
      (V J A).mapDerivedCategoryPlusFactorsh.inv.app M ≫ f ≫ eN.hom) he
    simpa only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id,
      Category.comp_id, M] using h
  have hn := (Functor.rightDerivedFunctorPlusBaseChange e.hom).naturality eL.hom
  simp only [Functor.comp_map] at hn
  rw [hn, ← Category.assoc, hf']
  simp only [Category.assoc]
  rw [← H.rightDerivedFunctorPlus.map_comp, he', H.rightDerivedFunctorPlus.map_comp]
  have hq := H.rightDerivedFunctorPlusUnit.naturality
    ((HomotopyCategory.Plus.quotient (Sheaf J AddCommGrpCat.{u})).map q)
  simp only [Functor.comp_map] at hq
  rw [Functor.map_comp, Category.assoc]
  change _ = DerivedCategory.Plus.Q.map (complexIdentity J A F H e L).hom ≫
    DerivedCategory.Plus.Q.map (H.mapCochainComplexPlus.map q) ≫ _
  change DerivedCategory.Plus.Q.map (H.mapCochainComplexPlus.map q) ≫ compute H N =
    compute H ((V J A).mapCochainComplexPlus.obj L) ≫
      H.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map q) at hq
  rw [← Category.assoc (compute H _) _, ← hq]
  simp only [Category.assoc]

omit [HasWeakSheafify J RingCat.{u}]
  [HasDerivedCategory.{w} (Sheaf J AddCommGrpCat.{u})]
  [HasDerivedCategory.{w} AddCommGrpCat.{u}] in
private theorem mapAcyclicQuasiIso
    (H : Sheaf J AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u}) [H.Additive]
    [PreservesFiniteLimits H]
    (L N : CochainComplex.Plus (Sheaf J AddCommGrpCat.{u}))
    (q : L ⟶ N) [QuasiIso q.hom]
    (hL : ∀ i, H.rightAcyclic (L.obj.X i))
    (hN : ∀ i, H.rightAcyclic (N.obj.X i)) :
    QuasiIso (H.mapCochainComplexPlus.map q).hom := by
  obtain ⟨a, ha⟩ := L.property
  obtain ⟨b, hb⟩ := N.property
  let := ha
  let := hb
  have : L.obj.IsStrictlyGE (min a b) :=
    L.obj.isStrictlyGE_of_ge (min a b) a (min_le_left _ _)
  have : N.obj.IsStrictlyGE (min a b) :=
    N.obj.isStrictlyGE_of_ge (min a b) b (min_le_right _ _)
  exact H.quasiIso_map_of_rightAcyclic q.hom (min a b) hL hN

/-- Forgetting constant module scalars compares the derived restriction kernels,
including all representative normalizations.

Source: Stacks, sites-cohomology.tex, 093X and 03FD, and injectives.tex, 01DU;
agent-formulated restriction-kernel refinement of the ordinary evaluation comparison
(blueprint: lem-pur-module-restriction-kernel-comparison).

Proof:
1. Module sheaves are abelian and Grothendieck, hence have enough injectives.
Evaluation and the two kernel functors are additive and left exact. Forgetting
scalars is exact and preserves the kernels, giving `kernelIdentity`.
2. Apply 093X to an injective module sheaf and to an injective abelian sheaf viewed
as a sheaf of integer modules. Their restriction maps are surjective, so their
restriction-kernel rows are short exact. This does not make the underlying
abelian sheaf of an injective module sheaf injective.
3. The ordinary evaluation comparison 03FD shows that the underlying abelian
sheaf of a module-injective is acyclic for evaluation at T and W.
4. Resolve that abelian sheaf by injectives. The degreewise short exact kernel
sequence gives a long exact cohomology sequence. Evaluation acyclicity kills
all positive degrees except possibly degree one; surjectivity in step 2 kills
that degree as well. Thus it is acyclic for the abelian kernel functor.
5. Bounded-below injective representatives L and N compute the two derived
kernel functors via their right-derived units (05TI/05TH). Maps into the
abelian K-injective representative N realize the chosen derived identification
by a quasi-isomorphism q (070I).
6. Naturality of q gives a morphism of the short exact restriction-kernel rows.
The two evaluated maps are quasi-isomorphisms by 03FD.
7. Apply the natural long exact sequence to the row morphism. In the five-term
window around each kernel cohomology group the other four maps are isomorphisms.
The five lemma makes the kernel map a quasi-isomorphism in every integer degree.
8. Naturality of the right-derived unit identifies this kernel map with the
canonical `comparison`. Maps between injective representatives are unique up
to homotopy; additive functors preserve homotopies. This proves independence
of all representatives and naturality in K. The same unit argument identifies
the two evaluations with the recorded ordinary comparisons. Degree zero is
the identity on actual kernels, expressed by kernel preservation when categorical
limits have been chosen. No flatness over the integers is used. -/
theorem moduleRestrictionKernelComparison [Mono m] :
    (∀ (I : Modules J A), Injective I →
      Function.Surjective ((restriction J A m).app I)) ∧
    (∀ (I : Modules J A), Injective I → ∀ q : ℕ, 0 < q →
      IsZero (((S₀ J m).rightDerived q).obj ((V J A).obj I))) ∧
    IsIso (comparison J A m) ∧
    (Functor.whiskerRight (S J A m).toRightDerivedZero (v A) ≫
        Functor.rightDerivedBaseChange (kernelIdentity J A m).hom 0 =
      (kernelIdentity J A m).hom ≫
        Functor.whiskerLeft (V J A) (S₀ J m).toRightDerivedZero) ∧
    (∀ (K : DerivedCategory.Plus (Modules J A))
      (L : CochainComplex.Plus (Modules J A))
      (N : CochainComplex.Plus (Sheaf J AddCommGrpCat.{u}))
      (_hL : ∀ i : ℤ, Injective (L.obj.X i))
      (_hN : ∀ i : ℤ, Injective (N.obj.X i))
      (eL : DerivedCategory.Plus.Q.obj L ≅ K)
      (eN : DerivedCategory.Plus.Q.obj N ≅ (V J A).mapDerivedCategoryPlus.obj K)
      (q : (V J A).mapCochainComplexPlus.obj L ⟶ N)
      (_hq : QuasiIso q.hom)
      (_he : (V J A).mapDerivedCategoryPlus.map eL.hom ≫ eN.inv =
        (V J A).mapDerivedCategoryPlusFactorsh.hom.app
            ((HomotopyCategory.Plus.quotient (Modules J A)).obj L) ≫
          DerivedCategory.Plus.Q.map q),
      (∀ i : ℤ,
        (row J m ((V J A).obj (L.obj.X i))).ShortExact ∧
        (row J m (N.obj.X i)).ShortExact ∧
        (S₀ J m).map (q.hom.f i) ≫ (row J m (N.obj.X i)).f =
          (row J m ((V J A).obj (L.obj.X i))).f ≫ (G₀ J T).map (q.hom.f i) ∧
        (G₀ J T).map (q.hom.f i) ≫ (row J m (N.obj.X i)).g =
          (row J m ((V J A).obj (L.obj.X i))).g ≫ (G₀ J W).map (q.hom.f i)) ∧
      QuasiIso (kernelMap J A m L N q).hom ∧
      QuasiIso (evaluationMap J A T L N q).hom ∧
      QuasiIso (evaluationMap J A W L N q).hom ∧
      (forgetCompute J A (S J A m) L ≫
          (v A).mapDerivedCategoryPlus.map ((S J A m).rightDerivedFunctorPlus.map eL.hom) ≫
          (comparison J A m).app K =
        DerivedCategory.Plus.Q.map (kernelMap J A m L N q) ≫ compute (S₀ J m) N ≫
          (S₀ J m).rightDerivedFunctorPlus.map eN.hom) ∧
      (∀ U : C, U = T ∨ U = W →
        forgetCompute J A (G J A U) L ≫
            (v A).mapDerivedCategoryPlus.map ((G J A U).rightDerivedFunctorPlus.map eL.hom) ≫
            (LeftModuleDerivedEvaluation.comparison J A U).app K =
          DerivedCategory.Plus.Q.map (evaluationMap J A U L N q) ≫ compute (G₀ J U) N ≫
            (G₀ J U).rightDerivedFunctorPlus.map eN.hom)) := by
  let := sLeftExact J A m
  let := s₀LeftExact J m
  have hi : IsIso (comparison J A m) :=
    Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic
      (kernelIdentity J A m) (fun I _ ↦ forgottenKernelAcyclic J A m I)
  refine ⟨fun I hI ↦ moduleRestrictionSurjective J A m I, ?_, hi, ?_, ?_⟩
  · intro I hI q hq
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
    exact forgottenKernelAcyclic J A m I n
  · apply NatTrans.ext
    funext I
    change (v A).map ((S J A m).toRightDerivedZero.app I) ≫
      (Functor.rightDerivedBaseChange (kernelIdentity J A m).hom 0).app I = _
    exact Functor.rightDerivedBaseChange_zero_unit (kernelIdentity J A m).hom I
  · intro K L N hL hN eL eN q hq he
    let : ∀ i : ℤ, Injective (L.obj.X i) := hL
    let : ∀ i : ℤ, Injective (N.obj.X i) := hN
    let := hq
    have hrows : ∀ i : ℤ,
        (row J m ((V J A).obj (L.obj.X i))).ShortExact ∧
        (row J m (N.obj.X i)).ShortExact ∧
        (S₀ J m).map (q.hom.f i) ≫ (row J m (N.obj.X i)).f =
          (row J m ((V J A).obj (L.obj.X i))).f ≫ (G₀ J T).map (q.hom.f i) ∧
        (G₀ J T).map (q.hom.f i) ≫ (row J m (N.obj.X i)).g =
          (row J m ((V J A).obj (L.obj.X i))).g ≫ (G₀ J W).map (q.hom.f i) := by
      intro i
      have hs₁ : Epi ((restriction₀ J m).app ((V J A).obj (L.obj.X i))) :=
        (AddCommGrpCat.epi_iff_surjective _).2 (moduleRestrictionSurjective J A m _)
      have hs₂ : Epi ((restriction₀ J m).app (N.obj.X i)) :=
        (AddCommGrpCat.epi_iff_surjective _).2 (abelianRestrictionSurjective J m _)
      have hm₁ : Mono (row J m ((V J A).obj (L.obj.X i))).f := by
        change Mono (kernel.ι _)
        infer_instance
      have hm₂ : Mono (row J m (N.obj.X i)).f := by
        change Mono (kernel.ι _)
        infer_instance
      refine ⟨ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel _) hm₁ hs₁,
        ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel _) hm₂ hs₂, ?_, ?_⟩
      · exact kernel.lift_ι _ _ _
      · exact (restriction₀ J m).naturality _
    have hkq : QuasiIso ((S₀ J m).mapCochainComplexPlus.map q).hom :=
      mapAcyclicQuasiIso J (S₀ J m) _ N q
        (fun i ↦ forgottenKernelAcyclic J A m (L.obj.X i))
        (fun i ↦ Functor.rightAcyclic_of_injective _)
    have heq (U : C) : QuasiIso (evaluationMap J A U L N q).hom := by
      let : PreservesFiniteLimits (G₀ J U) := inferInstanceAs
        (PreservesFiniteLimits (sheafToPresheaf J AddCommGrpCat.{u} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)))
      have : QuasiIso ((G₀ J U).mapCochainComplexPlus.map q).hom :=
        mapAcyclicQuasiIso J (G₀ J U) _ N q
          (fun i ↦ forgottenEvaluationAcyclic J A U (L.obj.X i))
          (fun i ↦ Functor.rightAcyclic_of_injective _)
      change QuasiIso ((evaluationComplexIdentity J A U L).hom.hom ≫
        ((G₀ J U).mapCochainComplexPlus.map q).hom)
      have : IsIso (evaluationComplexIdentity J A U L).hom.hom :=
        inferInstanceAs (IsIso ((CochainComplex.Plus.ι _).map
          (evaluationComplexIdentity J A U L).hom))
      infer_instance
    refine ⟨hrows, ?_, heq T, heq W, ?_, ?_⟩
    · change QuasiIso ((kernelComplexIdentity J A m L).hom.hom ≫
        ((S₀ J m).mapCochainComplexPlus.map q).hom)
      have : IsIso (kernelComplexIdentity J A m L).hom.hom :=
        inferInstanceAs (IsIso ((CochainComplex.Plus.ι _).map
          (kernelComplexIdentity J A m L).hom))
      infer_instance
    · exact comparisonCompute J A (S J A m) (S₀ J m) (kernelIdentity J A m)
        K L N eL eN q he
    · intro U _
      exact comparisonCompute J A (G J A U) (G₀ J U) (evaluationIdentity J A U)
        K L N eL eN q he


end CategoryTheory.ModuleRestrictionKernel
