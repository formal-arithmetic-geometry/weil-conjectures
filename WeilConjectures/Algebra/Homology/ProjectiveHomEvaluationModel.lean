/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Category.Grp.EpiMono
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableCriterion
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Projective

/-! # Projective Hom complexes and the derived evaluation

Source: Stacks Project, More on Algebra, Tags 0A66, 0A5W, 0A5Y, 0GWQ and 0FNG
(blueprint: lem-pod-projective-hom-evaluation-model).

The Hom complex here has differential d_N f - (-1)^q f d_P, using the recorded
module-valued Hom complex. The tensor and internal Hom on the derived category are
its existing derived closed monoidal structure. The canonical lax tensorator of Q
compares derived tensor with the ordinary direct-sum total tensor of complexes.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace CochainComplex

private noncomputable def modelMap {R : Type u} [CommRing R]
    {P P' N N' : CochainComplex (ModuleCat.{u} R) ℤ} (a : P' ⟶ P) (b : N ⟶ N') :
    moduleHomComplex P N ⟶ moduleHomComplex P' N' where
  f n := ModuleCat.ofHom
    { toFun := fun f ↦ ((HomComplex.Cochain.ofHom a).comp f (zero_add n)).comp
        (HomComplex.Cochain.ofHom b) (add_zero n)
      map_add' := fun f g ↦ by simp
      map_smul' := fun r f ↦ by simp }
  comm' n m _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact (HomComplex.δ_comp_ofHom _ b m).trans
      (congrArg (fun z ↦ z.comp (HomComplex.Cochain.ofHom b) (add_zero m))
        (HomComplex.δ_ofHom_comp a f m))

private lemma modelMap_v {R : Type u} [CommRing R]
    {P P' N N' : CochainComplex (ModuleCat.{u} R) ℤ} (a : P' ⟶ P) (b : N ⟶ N')
    (n p q : ℤ) (h : p + n = q) (f : (moduleHomComplex P N).X n) :
    ((modelMap a b).f n f).v p q h = a.f p ≫ f.v p q h ≫ b.f q := by
  change (((HomComplex.Cochain.ofHom a).comp f (zero_add n)).comp
    (HomComplex.Cochain.ofHom b) (add_zero n)).v p q h = _
  rw [HomComplex.Cochain.comp_zero_cochain_v, HomComplex.Cochain.zero_cochain_comp_v]
  rfl

private noncomputable def modelEv {R : Type u} [CommRing R]
    (P N : CochainComplex (ModuleCat.{u} R) ℤ) : P ⊗ moduleHomComplex P N ⟶ N :=
  (internalHomEquiv P N _).symm (modelIso P N).hom

private lemma modelEv_apply {R : Type u} [CommRing R]
    (P N : CochainComplex (ModuleCat.{u} R) ℤ) (p q : ℤ)
    (x : P.X p) (f : (moduleHomComplex P N).X q) :
    (modelEv P N).f (p + q)
        (HomologicalComplex.ιTensorObj P (moduleHomComplex P N) p q (p + q) rfl
          (x ⊗ₜ[R] f)) = (p * q).negOnePow • (f.v p (p + q) rfl) x := by
  have e := ιTensorObj_internalHomEquiv_symm_f
    (moduleHomComplex P N) (modelIso P N).hom p q (p + q) rfl
  change (HomologicalComplex.ιTensorObj P (moduleHomComplex P N) p q (p + q) rfl ≫
    (modelEv P N).f (p + q)) (x ⊗ₜ[R] f) = _
  dsimp only [modelEv]
  rw [e]
  change (((modelIso P N).hom.f q ≫ internalHomπ P N q p (p + q) rfl) f).hom x = _
  rw [show (modelIso P N).hom.f q = modelToInternalX P N q from rfl,
    modelToInternalX_π]
  rfl

private lemma modelEv_naturality {R : Type u} [CommRing R]
    {P P' N N' : CochainComplex (ModuleCat.{u} R) ℤ} (a : P' ⟶ P) (b : N ⟶ N') :
    P' ◁ modelMap a b ≫ modelEv P' N' =
      a ▷ moduleHomComplex P N ≫ modelEv P N ≫ b := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  subst n
  simp only [HomologicalComplex.comp_f, ← Category.assoc]
  rw [ιTensorObj_whiskerLeft_f]
  rw [CochainComplex.Monoidal.ι_whiskerRight]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext x f
  change (modelEv P' N').f (p + q)
      (HomologicalComplex.ιTensorObj P' (moduleHomComplex P' N') p q (p + q) rfl
        (x ⊗ₜ[R] ((modelMap a b).f q f))) =
    b.f (p + q) ((modelEv P N).f (p + q)
      (HomologicalComplex.ιTensorObj P (moduleHomComplex P N) p q (p + q) rfl
        (a.f p x ⊗ₜ[R] f)))
  rw [modelEv_apply, modelEv_apply, modelMap_v]
  simp

private lemma modelMap_id_apply {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    {N N' : CochainComplex (ModuleCat.{u} R) ℤ} (b : N ⟶ N') (n : ℤ)
    (f : (moduleHomComplex P N).X n) :
    (modelMap (𝟙 P) b).f n f = f.comp (HomComplex.Cochain.ofHom b) (add_zero n) := by
  change ((HomComplex.Cochain.ofHom (𝟙 P)).comp f (zero_add n)).comp
    (HomComplex.Cochain.ofHom b) (add_zero n) = _
  rw [HomComplex.Cochain.id_comp]

private lemma modelMap_quasiIso {R : Type u} [CommRing R]
    [HasDerivedCategory.{u} (ModuleCat.{u} R)]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKProjective]
    {N N' : CochainComplex (ModuleCat.{u} R) ℤ} (b : N ⟶ N') [QuasiIso b] :
    QuasiIso (modelMap (𝟙 P) b) := by
  let U := forget₂ (ModuleCat.{u} R) AddCommGrpCat
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ U]
  let f := (U.mapHomologicalComplex (.up ℤ)).map (modelMap (𝟙 P) b)
  refine ⟨fun n ↦ ?_⟩
  rw [quasiIsoAt_iff]
  let D := HomComplex.leftHomologyData P N n
  let D' := HomComplex.leftHomologyData P N' n
  let γ : ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor _ _ n).map f) D D' := default
  rw [γ.quasiIso_iff, ConcreteCategory.isIso_iff_bijective]
  have hk (z : HomComplex.Cocycle P N n) :
      γ.φK z = z.postcomp b := by
    apply HomComplex.Cocycle.ext
    have h := ConcreteCategory.congr_hom γ.commi z
    change (γ.φK z).val = (modelMap (𝟙 P) b).f n z.val at h
    exact h.trans (modelMap_id_apply P b n z.val)
  have hh (z : HomComplex.Cocycle P N n) :
      γ.φH (HomComplex.CohomologyClass.mk z) =
        HomComplex.CohomologyClass.mk (z.postcomp b) := by
    have h := ConcreteCategory.congr_hom γ.commπ z
    change γ.φH (HomComplex.CohomologyClass.mk z) =
      HomComplex.CohomologyClass.mk (γ.φK z) at h
    exact h.trans (congrArg HomComplex.CohomologyClass.mk (hk z))
  let H := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)
  let e := HomComplex.CohomologyClass.homAddEquiv (K := P) (L := N) (n := n)
  let e' := HomComplex.CohomologyClass.homAddEquiv (K := P) (L := N') (n := n)
  have he (z : HomComplex.CohomologyClass P N n) :
      e' (γ.φH z) = e z ≫
        H.map ((CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) n).map b) := by
    obtain ⟨z, rfl⟩ := z.mk_surjective
    rw [hh]
    change H.map (HomComplex.Cocycle.equivHomShift.symm (z.postcomp b)) = _
    rw [HomComplex.Cocycle.equivHomShift_symm_postcomp, Functor.map_comp]
    rfl
  have hbij : Function.Bijective (fun g : H.obj P ⟶ H.obj (N⟦n⟧) ↦
      g ≫ H.map ((CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) n).map b)) := by
    have : IsIso (DerivedCategory.Qh.map (H.map
        ((CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) n).map b))) := by
      apply (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso _) _).2
      infer_instance
    have h₁ := IsKProjective.Qh_map_bijective P (H.obj (N⟦n⟧))
    have h₂ := IsKProjective.Qh_map_bijective P (H.obj (N'⟦n⟧))
    have h₃ : Function.Bijective
        (fun g : DerivedCategory.Qh.obj (H.obj P) ⟶
            DerivedCategory.Qh.obj (H.obj (N⟦n⟧)) ↦
          g ≫ DerivedCategory.Qh.map (H.map
            ((CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) n).map b))) := by
      refine (Function.bijective_iff_has_inverse).2
        ⟨fun g ↦ g ≫ inv (DerivedCategory.Qh.map (H.map
          ((CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) n).map b))),
          ?_, ?_⟩
      · intro g; simp
      · intro g; simp
    apply (Function.Bijective.of_comp_iff' h₂ _).mp
    have eq : (DerivedCategory.Qh.map ∘ fun g : H.obj P ⟶ H.obj (N⟦n⟧) ↦
        g ≫ H.map ((CategoryTheory.shiftFunctor _ n).map b)) =
        (fun g ↦ g ≫ DerivedCategory.Qh.map
          (H.map ((CategoryTheory.shiftFunctor _ n).map b))) ∘ DerivedCategory.Qh.map := by
      funext g
      exact DerivedCategory.Qh.map_comp _ _
    rw [eq]
    exact h₃.comp h₁
  apply (Function.Bijective.of_comp_iff' e'.bijective _).mp
  change Function.Bijective (fun z : HomComplex.CohomologyClass P N n ↦ e' (γ.φH z))
  have eq : (fun z : HomComplex.CohomologyClass P N n ↦ e' (γ.φH z)) =
      (fun g ↦ g ≫ H.map ((CategoryTheory.shiftFunctor _ n).map b)) ∘ e := funext he
  rw [eq]
  exact hbij.comp e.bijective

private lemma modelKFlat {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hb : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i))
    (hp : ∀ i : ℤ, Module.Projective R (P.X i)) :
    (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat
      ((HomotopyCategory.quotient _ _).obj P) := by
  obtain ⟨n, hn⟩ := hb
  have : P.IsStrictlyLE n := (P.isStrictlyLE_iff n).2 hn
  apply (HomotopyCategory.kFlat_quotient_obj_iff P).2
  apply kFlat_of_isStrictlyLE_of_flat P n
  intro i
  have := hp i
  exact (ModuleCat.flat_iff_flat (P.X i)).2 inferInstance

private lemma modelTensorIso {R : Type u} [CommRing R]
    [HasDerivedCategory.{u} (ModuleCat.{u} R)]
    (P D : CochainComplex (ModuleCat.{u} R) ℤ)
    (hb : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i))
    (hp : ∀ i : ℤ, Module.Projective R (P.X i)) :
    IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P D) := by
  have := DerivedCategory.isIso_μ_Qh_of_kFlat
    ((HomotopyCategory.quotient _ _).obj P) ((HomotopyCategory.quotient _ _).obj D)
    (modelKFlat P hb hp)
  change IsIso ((_ ⊗ₘ _) ≫ (Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫
    DerivedCategory.Qh.map _) ≫ _)
  infer_instance

private noncomputable def modelComparison {R : Type u} [CommRing R]
    [HasDerivedCategory.{u} (ModuleCat.{u} R)]
    (P N : CochainComplex (ModuleCat.{u} R) ℤ) :
    DerivedCategory.Q.obj (moduleHomComplex P N) ⟶
      (ihom (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj N) :=
  MonoidalClosed.curry (Functor.LaxMonoidal.μ DerivedCategory.Q P (moduleHomComplex P N) ≫
    DerivedCategory.Q.map (modelEv P N))

private lemma modelComparison_naturality {R : Type u} [CommRing R]
    [HasDerivedCategory.{u} (ModuleCat.{u} R)]
    {P P' N N' : CochainComplex (ModuleCat.{u} R) ℤ} (a : P' ⟶ P) (b : N ⟶ N') :
    DerivedCategory.Q.map (modelMap a b) ≫ modelComparison P' N' =
      modelComparison P N ≫
        (MonoidalClosed.pre (DerivedCategory.Q.map a)).app (DerivedCategory.Q.obj N) ≫
        (ihom (DerivedCategory.Q.obj P')).map (DerivedCategory.Q.map b) := by
  dsimp only [modelComparison]
  rw [← Category.assoc, MonoidalClosed.curry_pre_app,
    ← MonoidalClosed.curry_natural_right, ← MonoidalClosed.curry_natural_left]
  congr 1
  rw [Functor.LaxMonoidal.μ_natural_right_assoc, ← Functor.map_comp,
    modelEv_naturality, Functor.map_comp, Functor.map_comp,
    Functor.LaxMonoidal.μ_natural_left_assoc]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private lemma modelComparison_isIso_injective {R : Type u} [CommRing R]
    [HasDerivedCategory.{u} (ModuleCat.{u} R)]
    (P N : CochainComplex (ModuleCat.{u} R) ℤ) [N.IsKInjective]
    (hb : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i))
    (hp : ∀ i : ℤ, Module.Projective R (P.X i)) :
    IsIso (modelComparison P N) := by
  let H := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)
  let e := DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)
  have hN : (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)).isLocal (H.obj N) := by
    rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic,
      CategoryTheory.ObjectProperty.isLocal_trW]
    exact IsKInjective.rightOrthogonal N
  let ev : P ⊗ internalHomObj P N ⟶ N := (tensorHomAdjunction P).counit.app N
  let c := MonoidalClosed.curry
    (Functor.LaxMonoidal.μ DerivedCategory.Qh (H.obj P) (H.obj (internalHomObj P N)) ≫
      DerivedCategory.Qh.map (H.map ev))
  have hc : IsIso c := by
    have h := DerivedCategory.isIso_curry_μ_Qh_counit_comp
      (modelKFlat P hb hp) hN (𝟙 (DerivedCategory.Qh.obj (H.obj N)))
    dsimp only [H] at h
    rw [HomotopyCategory.tensorHomAdjunction_counit_app] at h
    simp only [HomotopyCategory.internalHom_obj, HomotopyCategory.quotient_obj_as] at h
    erw [Category.comp_id] at h
    exact h
  let t := DerivedCategory.Q.map (modelIso P N).hom ≫
    (e.app (internalHomObj P N)).inv ≫ c ≫
    (MonoidalClosed.pre (e.app P).inv).app (DerivedCategory.Qh.obj (H.obj N)) ≫
    (ihom (DerivedCategory.Q.obj P)).map (e.app N).hom
  have ht : modelComparison P N = t := by
    apply MonoidalClosed.uncurry_injective
    dsimp only [modelComparison, t]
    rw [MonoidalClosed.uncurry_curry]
    simp only [← Category.assoc]
    rw [MonoidalClosed.uncurry_natural_right]
    rw [MonoidalClosed.uncurry_pre_app]
    rw [MonoidalClosed.uncurry_natural_left]
    dsimp only [c]
    rw [MonoidalClosed.uncurry_curry]
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    have hev : modelEv P N = P ◁ (modelIso P N).hom ≫ ev := by
      apply (internalHomEquiv P N _).injective
      rw [internalHomEquiv_whiskerLeft_comp]
      dsimp only [modelEv, ev]
      rw [tensorHomAdjunction_counit_app, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply, Category.comp_id]
    rw [hev, Functor.map_comp, ← Functor.LaxMonoidal.μ_natural_right_assoc]
    rw [← whisker_exchange_assoc]
    apply congrArg (fun k ↦ DerivedCategory.Q.obj P ◁
      DerivedCategory.Q.map (modelIso P N).hom ≫ k)
    have hμ : Functor.LaxMonoidal.μ DerivedCategory.Q P (internalHomObj P N) =
        ((e.app P).inv ⊗ₘ (e.app (internalHomObj P N)).inv) ≫
          Functor.LaxMonoidal.μ (H ⋙ DerivedCategory.Qh) P (internalHomObj P N) ≫
            (e.app (P ⊗ internalHomObj P N)).hom := rfl
    rw [hμ]
    have hμ' : Functor.LaxMonoidal.μ (H ⋙ DerivedCategory.Qh) P (internalHomObj P N) =
        Functor.LaxMonoidal.μ DerivedCategory.Qh (H.obj P)
          (H.obj (internalHomObj P N)) := by
      change _ ≫ DerivedCategory.Qh.map (𝟙 _) = _
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
    rw [hμ']
    simp only [Category.assoc]
    erw [← e.hom.naturality]
    rw [tensorHom_def]
    simp only [Category.assoc]
    rfl
  rw [ht]
  infer_instance

private lemma modelComparison_isIso {R : Type u} [CommRing R]
    [HasDerivedCategory.{u} (ModuleCat.{u} R)]
    (P N : CochainComplex (ModuleCat.{u} R) ℤ)
    (hb : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i))
    (hp : ∀ i : ℤ, Module.Projective R (P.X i)) :
    IsIso (modelComparison P N) := by
  obtain ⟨n, hn⟩ := hb
  have : P.IsStrictlyLE n := (P.isStrictlyLE_iff n).2 hn
  have (i : ℤ) : Projective (P.X i) := by
    have := hp i
    exact ModuleCat.projective_of_categoryTheory_projective (R := R) (P.X i)
  have : P.IsKProjective := isKProjective_of_projective P n
  let I := (kInjectiveResolutionFunctor.{u} (ModuleCat.{u} R)).obj N
  let b := (toKInjectiveResolution.{u} (ModuleCat.{u} R)).app N
  have : QuasiIso b := (monoQuasiIso_toKInjectiveResolution_app.{u} _ N).2
  have : I.IsKInjective := isKInjective_kInjectiveResolutionFunctor_obj (ModuleCat.{u} R) N
  have : QuasiIso (modelMap (𝟙 P) b) := modelMap_quasiIso P b
  have := modelComparison_isIso_injective P I ⟨n, hn⟩ hp
  have eq := modelComparison_naturality (𝟙 P) b
  rw [CategoryTheory.Functor.map_id, MonoidalClosed.pre_id, NatTrans.id_app,
    Category.id_comp] at eq
  change DerivedCategory.Q.map (modelMap (𝟙 P) b) ≫ modelComparison P I =
    modelComparison P N ≫
      (ihom (DerivedCategory.Q.obj P)).map (DerivedCategory.Q.map b) at eq
  have : IsIso (modelComparison P N ≫
      (ihom (DerivedCategory.Q.obj P)).map (DerivedCategory.Q.map b)) := by
    rw [← eq]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((ihom (DerivedCategory.Q.obj P)).map (DerivedCategory.Q.map b))

/-- The projective Hom model, natural in both complexes, with its signed evaluation.
Source: Stacks Project, Tags 0A66 (projective Hom model), 0A5W (derived internal Hom),
0A5Y and 0GWQ (tensor-Hom adjunction), and 0FNG (Koszul signs).
(blueprint: lem-pod-projective-hom-evaluation-model)

The witnesses H and ev are uniquely specified chain maps: H is pre- and post-composition
on every homogeneous coordinate, and ev is signed evaluation on every total-tensor
summand. The comparison e is specified by its counit square, equivalently as the
adjoint transpose of Q(ev) after the canonical tensorator. Thus neither the comparison
nor the tensor model is an arbitrary isomorphism. Boundedness and projectivity enter
only the derived comparison; no finite generation or bound on N is assumed.

Proof:
1. Projective modules are flat. Translate the upper support bound into IsStrictlyLE
and apply the generic bounded-above flat-complex theorem to make P K-flat. The
canonical tensorator of Q is therefore invertible with P as its first factor.
2. The coordinate twist (-1)^(p*q) identifies moduleHomComplex with the library's
categorical internalHomObj. The cochain differential formula proves that this is
an isomorphism of complexes. Transposing it constructs the signed evaluation.
3. In every degree, HomComplex.leftHomologyData and CohomologyClass.homAddEquiv
identify Hom cohomology with homotopy-category maps into a shifted target.
Bounded-above projectivity makes P K-projective, so Qh_map_bijective shows that
postcomposition by a quasi-isomorphism is bijective. Thus Hom(P,-) preserves
quasi-isomorphisms, including the map to a K-injective resolution of N.
4. Define the derived comparison by currying Q of evaluation after the tensorator.
For a K-injective target, the generic derived counit criterion makes this map
invertible. Transport from Qh to Q using quotientCompQhIso and its defining
monoidal structure. Naturality with respect to a K-injective resolution gives
invertibility for arbitrary N. Uncurrying gives the required counit square.
5. Pre- and postcomposition commute with signed evaluation on every total-tensor
summand. Localize and curry this equality to get mixed naturality of the comparison.
The same formulas apply to zero complexes, shifted free modules, arbitrary projective
modules, and unbounded N; no finite-generation hypothesis is used. -/
theorem projective_hom_evaluation_model (R : Type u) [CommRing R]
    [HasDerivedCategory.{u} (ModuleCat.{u} R)] :
    ∃ H : ∀ {P P' N N' : CochainComplex (ModuleCat.{u} R) ℤ},
        (P' ⟶ P) → (N ⟶ N') → (moduleHomComplex P N ⟶ moduleHomComplex P' N'),
      ∃ ev : ∀ (P N : CochainComplex (ModuleCat.{u} R) ℤ),
          P ⊗ moduleHomComplex P N ⟶ N,
        (∀ (P P' N N' : CochainComplex (ModuleCat.{u} R) ℤ)
          (a : P' ⟶ P) (b : N ⟶ N') (q p s : ℤ) (h : p + q = s)
          (f : (moduleHomComplex P N).X q),
          ((H a b).f q f).v p s h = a.f p ≫ f.v p s h ≫ b.f s) ∧
        (∀ (P N : CochainComplex (ModuleCat.{u} R) ℤ) (p q : ℤ)
          (x : P.X p) (f : (moduleHomComplex P N).X q),
          (ev P N).f (p + q)
              ((HomologicalComplex.ιTensorObj P (moduleHomComplex P N) p q (p + q) rfl)
                (x ⊗ₜ[R] f)) =
            (p * q).negOnePow • (f.v p (p + q) rfl) x) ∧
        ∃ e : ∀ (P : CochainComplex (ModuleCat.{u} R) ℤ)
            (_hb : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i))
            (_hp : ∀ i : ℤ, Module.Projective R (P.X i))
            (N : CochainComplex (ModuleCat.{u} R) ℤ),
            DerivedCategory.Q.obj (moduleHomComplex P N) ≅
              (ihom (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj N),
          (∀ (P : CochainComplex (ModuleCat.{u} R) ℤ)
            (hb : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i))
            (hp : ∀ i : ℤ, Module.Projective R (P.X i))
            (N : CochainComplex (ModuleCat.{u} R) ℤ),
            IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P (moduleHomComplex P N)) ∧
            Functor.LaxMonoidal.μ DerivedCategory.Q P (moduleHomComplex P N) ≫
                DerivedCategory.Q.map (ev P N) =
              DerivedCategory.Q.obj P ◁ (e P hb hp N).hom ≫
                (ihom.ev (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj N)) ∧
          (∀ (P P' N N' : CochainComplex (ModuleCat.{u} R) ℤ)
            (hb : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i))
            (hp : ∀ i : ℤ, Module.Projective R (P.X i))
            (hb' : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P'.X i))
            (hp' : ∀ i : ℤ, Module.Projective R (P'.X i))
            (a : P' ⟶ P) (b : N ⟶ N'),
            DerivedCategory.Q.map (H a b) ≫ (e P' hb' hp' N').hom =
              (e P hb hp N).hom ≫
                (MonoidalClosed.pre (DerivedCategory.Q.map a)).app (DerivedCategory.Q.obj N) ≫
                (ihom (DerivedCategory.Q.obj P')).map (DerivedCategory.Q.map b)) := by
  classical
  refine ⟨fun {_ _ _ _} a b ↦ modelMap a b, modelEv, ?_, ?_, ?_⟩
  · intro P P' N N' a b q p s h f
    exact modelMap_v a b q p s h f
  · exact modelEv_apply
  · let e (P : CochainComplex (ModuleCat.{u} R) ℤ)
        (hb : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i))
        (hp : ∀ i : ℤ, Module.Projective R (P.X i))
        (N : CochainComplex (ModuleCat.{u} R) ℤ) :
        DerivedCategory.Q.obj (moduleHomComplex P N) ≅
          (ihom (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj N) := by
      have := modelComparison_isIso P N hb hp
      exact asIso (modelComparison P N)
    refine ⟨e, ?_, ?_⟩
    · intro P hb hp N
      refine ⟨modelTensorIso P _ hb hp, ?_⟩
      exact (MonoidalClosed.uncurry_curry _).symm
    · intro P P' N N' hb hp hb' hp' a b
      exact modelComparison_naturality a b

end CochainComplex
