/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution

import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Injective resolutions in finite products of abelian categories

Source: Stacks Project, Derived Categories, Section 13.20 (Tag 0156), and the
componentwise product-category argument recorded in the DAG
(blueprint: lem-weil-pbc-finite-product-injective-resolutions).
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

-- The structures below use pointwise operations on morphisms.
private instance piPreadditive {I : Type w} (C : I → Type u)
    [∀ i, Category.{v} (C i)] [∀ i, Preadditive (C i)] : Preadditive (∀ i, C i) where
  homGroup X Y := inferInstanceAs (AddCommGroup (∀ i, X i ⟶ Y i))
  add_comp X Y Z f f' g := by
    funext i
    exact Preadditive.add_comp (X i) (Y i) (Z i) (f i) (f' i) (g i)
  comp_add X Y Z f g g' := by
    funext i
    exact Preadditive.comp_add (X i) (Y i) (Z i) (f i) (g i) (g' i)

@[simp] private theorem piZeroApply {I : Type w} {C : I → Type u}
    [∀ i, Category.{v} (C i)] [∀ i, Preadditive (C i)]
    {X Y : ∀ i, C i} (i : I) : (0 : X ⟶ Y) i = 0 := rfl

private theorem piMonoComponent {I : Type w} {C : I → Type u}
    [∀ i, Category.{v} (C i)] [∀ i, Preadditive (C i)]
    {X Y : ∀ i, C i} (f : X ⟶ Y) [Mono f] (i : I) : Mono (f i) := by
  classical
  apply Preadditive.mono_of_cancel_zero
  intro Z g hg
  let g' : Function.update X i Z ⟶ X := fun j ↦
    if h : j = i then by subst j; simpa using g else 0
  have hgf : g' ≫ f = 0 := by
    funext j
    by_cases h : j = i
    · subst j
      simpa [g', Category.assoc] using
        congrArg (fun t ↦ eqToHom (Function.update_self i Z X) ≫ t) hg
    · simp [g', h, Pi.comp_apply]
  have hz : g' = 0 := zero_of_comp_mono f hgf
  simpa [g', Category.assoc] using
    congrArg (fun t ↦ eqToHom (Function.update_self i Z X).symm ≫ t) (congrFun hz i)

private theorem piEpiComponent {I : Type w} {C : I → Type u}
    [∀ i, Category.{v} (C i)] [∀ i, Preadditive (C i)]
    {X Y : ∀ i, C i} (f : X ⟶ Y) [Epi f] (i : I) : Epi (f i) := by
  classical
  apply Preadditive.epi_of_cancel_zero
  intro Z g hg
  let g' : Y ⟶ Function.update Y i Z := fun j ↦
    if h : j = i then by subst j; simpa using g else 0
  have hfg : f ≫ g' = 0 := by
    funext j
    by_cases h : j = i
    · subst j
      simpa [g', Category.assoc] using
        congrArg (fun t ↦ t ≫ eqToHom (Function.update_self i Z Y).symm) hg
    · simp [g', h, Pi.comp_apply]
  have hz : g' = 0 := zero_of_epi_comp f hfg
  simpa [g', Category.assoc] using
    congrArg (fun t ↦ t ≫ eqToHom (Function.update_self i Z Y)) (congrFun hz i)

private theorem piMono {I : Type w} {C : I → Type u}
    [∀ i, Category.{v} (C i)] {X Y : ∀ i, C i} (f : X ⟶ Y)
    [∀ i, Mono (f i)] : Mono f where
  right_cancellation g h e := by
    funext i
    exact (cancel_mono (f i)).1 (congrFun e i)

-- Assemble universal cones without restricting the index or hom universes.
private noncomputable def piLimit {I : Type w} {C : I → Type u}
    [∀ i, Category.{v} (C i)] {J : Type*} [Category* J]
    (F : J ⥤ ∀ i, C i) [∀ i, HasLimit (F ⋙ Pi.eval C i)] : LimitCone F where
  cone :=
    { pt := fun i ↦ limit (F ⋙ Pi.eval C i)
      π := { app := fun j i ↦ limit.π (F ⋙ Pi.eval C i) j
             naturality := by intros; funext i; exact (limit.cone _).π.naturality _ } }
  isLimit :=
    { lift := fun s i ↦ limit.lift (F ⋙ Pi.eval C i)
        { pt := s.pt i
          π := { app := fun j ↦ s.π.app j i
                 naturality := by intros; exact congrFun (s.π.naturality _) i } }
      fac := by intros; funext i; apply limit.lift_π
      uniq := by
        intro s m hm
        funext i
        apply limit.hom_ext
        intro j
        trans s.π.app j i
        · exact congrFun (hm j) i
        · symm; apply limit.lift_π }

private noncomputable def piColimit {I : Type w} {C : I → Type u}
    [∀ i, Category.{v} (C i)] {J : Type*} [Category* J]
    (F : J ⥤ ∀ i, C i) [∀ i, HasColimit (F ⋙ Pi.eval C i)] : ColimitCocone F where
  cocone :=
    { pt := fun i ↦ colimit (F ⋙ Pi.eval C i)
      ι := { app := fun j i ↦ colimit.ι (F ⋙ Pi.eval C i) j
             naturality := by
               intros; funext i
               exact (colimit.cocone (F ⋙ Pi.eval C i)).ι.naturality _ } }
  isColimit :=
    { desc := fun s i ↦ colimit.desc (F ⋙ Pi.eval C i)
        { pt := s.pt i
          ι := { app := fun j ↦ s.ι.app j i
                 naturality := by intros; exact congrFun (s.ι.naturality _) i } }
      fac := by intros; funext i; apply colimit.ι_desc
      uniq := by
        intro s m hm
        funext i
        apply colimit.hom_ext
        intro j
        trans s.ι.app j i
        · exact congrFun (hm j) i
        · symm; apply colimit.ι_desc }

private instance piHasLimitsOfShape {I : Type w} {C : I → Type u}
    [∀ i, Category.{v} (C i)] {J : Type*} [Category* J]
    [∀ i, HasLimitsOfShape J (C i)] : HasLimitsOfShape J (∀ i, C i) where
  has_limit F := HasLimit.mk (piLimit F)

private instance piHasColimitsOfShape {I : Type w} {C : I → Type u}
    [∀ i, Category.{v} (C i)] {J : Type*} [Category* J]
    [∀ i, HasColimitsOfShape J (C i)] : HasColimitsOfShape J (∀ i, C i) where
  has_colimit F := HasColimit.mk (piColimit F)

private noncomputable def piKernel {I : Type w} {C : I → Type u}
    [∀ i, Category.{v} (C i)] [∀ i, Preadditive (C i)]
    {X Y Z : ∀ i, C i} (f : X ⟶ Y) (g : Y ⟶ Z) (h : f ≫ g = 0)
    (hf : ∀ i, IsLimit (KernelFork.ofι (f i) (congrFun h i))) :
    IsLimit (KernelFork.ofι f h) := by
  apply KernelFork.IsLimit.ofι f h
    (fun k hk i ↦ (hf i).lift (KernelFork.ofι (k i) (congrFun hk i)))
  · intro W k hk
    funext i
    exact (hf i).fac _ WalkingParallelPair.zero
  · intro W k hk m hm
    funext i
    apply Fork.IsLimit.hom_ext (hf i)
    exact (congrFun hm i).trans ((hf i).fac (KernelFork.ofι (k i) (congrFun hk i))
      WalkingParallelPair.zero).symm

private noncomputable def piCokernel {I : Type w} {C : I → Type u}
    [∀ i, Category.{v} (C i)] [∀ i, Preadditive (C i)]
    {X Y Z : ∀ i, C i} (f : X ⟶ Y) (g : Y ⟶ Z) (h : f ≫ g = 0)
    (hg : ∀ i, IsColimit (CokernelCofork.ofπ (g i) (congrFun h i))) :
    IsColimit (CokernelCofork.ofπ g h) := by
  apply CokernelCofork.IsColimit.ofπ g h
    (fun k hk i ↦ (hg i).desc (CokernelCofork.ofπ (k i) (congrFun hk i)))
  · intro W k hk
    funext i
    exact (hg i).fac _ WalkingParallelPair.one
  · intro W k hk m hm
    funext i
    apply Cofork.IsColimit.hom_ext (hg i)
    exact (congrFun hm i).trans ((hg i).fac (CokernelCofork.ofπ (k i) (congrFun hk i))
      WalkingParallelPair.one).symm

@[instance_reducible] private noncomputable def piAbelian {I : Type w} (C : I → Type u)
    [∀ i, Category.{v} (C i)] [∀ i, Abelian (C i)] : Abelian (∀ i, C i) where
  has_finite_products := ⟨fun _ ↦ inferInstance⟩
  has_kernels := inferInstance
  has_cokernels := inferInstance
  normalMonoOfMono f _ := by
    have : ∀ i, Mono (f i) := fun i ↦ piMonoComponent f i
    let N := fun i ↦ normalMonoOfMono (f i)
    exact ⟨{
      Z := fun i ↦ (N i).Z
      g := fun i ↦ (N i).g
      w := funext fun i ↦ (N i).w
      isLimit := piKernel f _ _ (fun i ↦ (N i).isLimit) }⟩
  normalEpiOfEpi f _ := by
    have : ∀ i, Epi (f i) := fun i ↦ piEpiComponent f i
    let N := fun i ↦ normalEpiOfEpi (f i)
    exact ⟨{
      W := fun i ↦ (N i).W
      g := fun i ↦ (N i).g
      w := funext fun i ↦ (N i).w
      isColimit := piCokernel _ f _ (fun i ↦ (N i).isColimit) }⟩

private theorem piInjective {I : Type w} {C : I → Type u}
    [∀ i, Category.{v} (C i)] [∀ i, Preadditive (C i)]
    (J : ∀ i, C i) : Injective J ↔ ∀ i, Injective (J i) := by
  classical
  constructor
  · intro hJ i
    constructor
    intro X Y g f hf
    let X' := Function.update J i X
    let Y' := Function.update J i Y
    let f' : X' ⟶ Y' := fun j ↦ if h : j = i then by
      subst j
      exact eqToHom (Function.update_self i X J) ≫ f ≫
        eqToHom (Function.update_self i Y J).symm
      else eqToHom (Function.update_of_ne h X J) ≫
        eqToHom (Function.update_of_ne h Y J).symm
    let g' : X' ⟶ J := fun j ↦ if h : j = i then by
      subst j; exact eqToHom (Function.update_self i X J) ≫ g else 0
    have : ∀ j, Mono (f' j) := by
      intro j
      by_cases h : j = i
      · subst j; simp only [f', dif_pos rfl]; infer_instance
      · simp only [f', dif_neg h]; infer_instance
    have : Mono f' := piMono f'
    obtain ⟨k, hk⟩ := Injective.factors g' f'
    refine ⟨eqToHom (Function.update_self i Y J).symm ≫ k i, ?_⟩
    simpa [f', g', Category.assoc] using
      congrArg (fun t ↦ eqToHom (Function.update_self i X J).symm ≫ t)
        (congrFun hk i)
  · intro hJ
    have : ∀ i, Injective (J i) := hJ
    constructor
    intro X Y g f hf
    have : ∀ i, Mono (f i) := fun i ↦ piMonoComponent f i
    exact ⟨fun i ↦ Injective.factorThru (g i) (f i),
      funext fun i ↦ Injective.comp_factorThru (g i) (f i)⟩

attribute [local instance] piAbelian

-- Exactness can be tested using the componentwise kernel and cokernel.
private theorem piExact {I : Type w} {C : I → Type u}
    [∀ i, Category.{v} (C i)] [∀ i, Abelian (C i)]
    (S : ShortComplex (∀ i, C i))
    (h : ∀ i, (ShortComplex.mk (S.f i) (S.g i) (congrFun S.zero i)).Exact) :
    S.Exact := by
  let k : (fun i ↦ kernel (S.g i)) ⟶ S.X₂ := fun i ↦ kernel.ι (S.g i)
  let q : S.X₂ ⟶ (fun i ↦ cokernel (S.f i)) := fun i ↦ cokernel.π (S.f i)
  have hk : k ≫ S.g = 0 := funext fun i ↦ kernel.condition (S.g i)
  have hq : S.f ≫ q = 0 := funext fun i ↦ cokernel.condition (S.f i)
  apply (S.exact_iff_of_forks
    (piKernel k S.g hk (fun i ↦ kernelIsKernel (S.g i)))
    (piCokernel S.f q hq (fun i ↦ cokernelIsCokernel (S.f i)))).2
  funext i
  exact ((ShortComplex.mk (S.f i) (S.g i) (congrFun S.zero i)).exact_iff_of_forks
    (kernelIsKernel (S.g i)) (cokernelIsCokernel (S.f i))).1 (h i)

private noncomputable def piResolution {I : Type w} {C : I → Type u}
    [∀ i, Category.{v} (C i)] [∀ i, Abelian (C i)]
    (A : ∀ i, C i) (R : ∀ i, InjectiveResolution (A i)) : InjectiveResolution A := by
  let K : CochainComplex (∀ i, C i) ℕ :=
    { X := fun n i ↦ (R i).cocomplex.X n
      d := fun n m i ↦ (R i).cocomplex.d n m
      shape := by intros; funext i; exact (R i).cocomplex.shape _ _ ‹_›
      d_comp_d' := by intros; funext i; exact (R i).cocomplex.d_comp_d _ _ _ }
  let f : A ⟶ K.X 0 := fun i ↦ (R i).ι.f 0
  have hf : f ≫ K.d 0 1 = 0 :=
    funext fun i ↦ (R i).ι_f_zero_comp_complex_d
  refine {
    cocomplex := K
    injective := fun n ↦ (piInjective (K.X n)).2 (fun i ↦ inferInstance)
    ι := (CochainComplex.fromSingle₀Equiv K A).symm ⟨f, hf⟩
    quasiIso := ⟨fun n ↦ ?_⟩ }
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff]
    rw [ShortComplex.quasiIso_iff_of_zeros _
      (by simp [HomologicalComplex.shortComplexFunctor'])
      (by simp [HomologicalComplex.shortComplexFunctor'])
      (by exact K.shape 0 0 (by simp))]
    apply (ShortComplex.exact_and_mono_f_iff_f_is_kernel _).2
    refine ⟨?_⟩
    simpa using piKernel f (K.d 0 1) hf (fun i ↦ (R i).isLimitKernelFork)
  | succ n =>
    rw [quasiIsoAt_iff_exactAt]
    · rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
      apply piExact
      intro i
      exact (R i).exact_succ n
    · apply CochainComplex.exactAt_succ_single_obj

/-- A finite product of abelian categories with enough injectives is abelian and has enough
injectives. Its injective objects and injective resolutions are componentwise.
Source: Stacks Project, Derived Categories, Section 13.20 (Tag 0156), for the injective-resolution
setup; the product-category argument is supplied by the DAG
(blueprint: lem-weil-pbc-finite-product-injective-resolutions).

Proof, following the four steps of the node:
1. Zero objects, biproducts, kernels and cokernels are computed componentwise. A morphism is
mono or epi exactly when every component is. Normal monos and normal epis therefore hold
componentwise, giving the abelian structure (def-sp-abelian).
2. If every component of J is injective, extend a map along a mono in each component and
assemble the extensions. Conversely, put a mono and a map into J i in component i, with
zero objects in every other component; an extension into J gives the required extension
into J i (def-sp-injective-resolutions).
3. Choose monomorphisms into injectives componentwise (degree zero of the component
resolutions). Their assembled map is mono and their assembled target is injective by step 2,
giving enough injectives; with step 4 every object of the product has an injective resolution
(`HasInjectiveResolutions`, the form of lem-weil-pbc-derived-finite-product).
4. Assemble any given complexes and augmentations componentwise. Every term is injective
by step 2. Kernels and images are componentwise, so exactness in positive degrees and the
identification of degree-zero cohomology with A follow from the given resolutions. Thus
this very complex and augmentation form an injective resolution, not just some unrelated
resolution (def-sp-injective-resolutions).

The equations on X, d and the degree-zero augmentation specify the componentwise data
exactly. Heterogeneous equality allows the differential and augmentation to be compared
before rewriting the equalities of their endpoint objects. In higher degrees the source
of the augmentation is zero, so those components are forced. -/
theorem finiteProduct_injectiveResolutions
    (I : Type w) [Finite I] (C : I → Type u) [∀ i, Category.{v} (C i)]
    [∀ i, Abelian (C i)] [∀ i, HasInjectiveResolutions (C i)] :
    ∃ abelian : Abelian (∀ i, C i),
      letI := abelian
      HasInjectiveResolutions (∀ i, C i) ∧
        (∀ J : ∀ i, C i, Injective J ↔ ∀ i, Injective (J i)) ∧
        (∀ (A : ∀ i, C i) (R : ∀ i, InjectiveResolution (A i)),
          ∃ K : InjectiveResolution A,
            (∀ n : ℕ, K.cocomplex.X n = fun i ↦ (R i).cocomplex.X n) ∧
            (∀ n m : ℕ, HEq (K.cocomplex.d n m)
              (fun i ↦ (R i).cocomplex.d n m)) ∧
            HEq (K.ι.f 0) (fun i ↦ (R i).ι.f 0)) := by
  refine ⟨piAbelian C, ?_⟩
  refine ⟨⟨fun A ↦ ⟨⟨piResolution A (fun i ↦ (HasInjectiveResolution.out (Z := A i)).some)⟩⟩⟩,
    piInjective, ?_⟩
  intro A R
  refine ⟨piResolution A R, fun _ ↦ rfl, fun _ _ ↦ HEq.rfl, ?_⟩
  apply heq_of_eq
  exact CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

end CategoryTheory
