/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.DerivedInternalHomFilteredColimitData
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.FromJoel.Algebra.Homology.Bifunctor
import WeilConjectures.CategoryTheory.DerivedCategory.Products

/-! # Finite-free calculation for the strict internal-Hom roof

The tensor-unit calculation is checked on local sections. Finite-product cones
then extend it to arbitrary finite rank after taking homology. This avoids any
additivity assumption on the chosen functorial K-injective replacement.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SfbHomFilteredColimit
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]

attribute [local instance] Abelian.hasFiniteBiproducts

open MonoidalCategory
open SheafOfModules (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses)

private theorem tensorPreadditive (R : Sheaf J CommRingCat.{max u v r}) :
    let := SheafOfModules.isMonoidal_W_independentCoefficients R
    let := SheafOfModules.monoidalCategory R
    MonoidalPreadditive (Modules.{u, v, r} J R) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  have (X : Modules.{u, v, r} J R) : (tensorLeft X).Additive :=
    SheafOfModules.tensorLeft_additive_independent R X
  have (X : Modules.{u, v, r} J R) : (tensorRight X).Additive :=
    Functor.additive_of_iso (F := tensorLeft X)
      (NatIso.ofComponents (fun Y ↦ β_ X Y)
        (fun f ↦ BraidedCategory.braiding_naturality_right X f))
  exact
    { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
      zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
      whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
      add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add (f := f) (g := g) }

private noncomputable def tensorFinitePowerIso
    (R : Sheaf J CommRingCat.{max u v r}) (T : Modules.{u, v, r} J R)
    (d : ℕ) (e : T ≅ ∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((sheafCompose J
      (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R)) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients R
    letI := SheafOfModules.monoidalCategory R
    tensorLeft T ≅ Functor.const (Discrete (Fin d)) ⋙
      (lim : (Discrete (Fin d) ⥤ Modules.{u, v, r} J R) ⥤ _) := by
  letI := SheafOfModules.isMonoidal_W_independentCoefficients R
  letI := SheafOfModules.monoidalCategory R
  letI := tensorPreadditive.{u, v, r} J R
  let A := Modules.{u, v, r} J R
  let E : tensorLeft T ≅ ∏ᶜ fun _ : Fin d ↦ (𝟭 A) :=
    (curriedTensor A).mapIso (e ≪≫ (biproduct.isoProduct _).symm) ≪≫
      (curriedTensor A).mapBiproduct _ ≪≫
      biproduct.mapIso (fun _ ↦ MonoidalCategory.leftUnitorNatIso A) ≪≫
      biproduct.isoProduct _
  exact E ≪≫ limitIsoFlipCompLim (Discrete.functor (fun _ : Fin d ↦ 𝟭 A))


private theorem tensorFinitePowerExact
    (R : Sheaf J CommRingCat.{max u v r}) (T : Modules.{u, v, r} J R)
    (d : ℕ) (e : T ≅ ∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((sheafCompose J
      (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R)) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients R
    letI := SheafOfModules.monoidalCategory R
    PreservesFiniteLimits (tensorLeft T) ∧ PreservesFiniteColimits (tensorLeft T) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let A := Modules.{u, v, r} J R
  let H := Functor.const (Discrete (Fin d)) ⋙
    (lim : (Discrete (Fin d) ⥤ A) ⥤ A)
  have : PreservesFiniteLimits H := inferInstance
  have : PreservesFiniteColimits
      (lim : (Discrete (Fin d) ⥤ A) ⥤ A) :=
    preservesFiniteColimits_of_natIso HasBiproductsOfShape.colimIsoLim
  have : PreservesFiniteColimits H := inferInstance
  exact ⟨preservesFiniteLimits_of_natIso (tensorFinitePowerIso.{u, v, r} J R T d e).symm,
    preservesFiniteColimits_of_natIso (tensorFinitePowerIso.{u, v, r} J R T d e).symm⟩

omit [HasSheafify J AddCommGrpCat.{max u v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}] in
private theorem rawHomAdditive (R : Sheaf J CommRingCat.{max u v r})
    (P : CochainComplex (Modules.{u, v, r} J R) ℤ) :
    ((homComplexFunctor (R := R)).obj (op P)).Additive := by
  constructor
  intro X Y f g
  ext n : 1
  apply homComplex_hom_ext
  intro p q hpq
  simp only [HomologicalComplex.add_f_apply, Preadditive.add_comp]
  rw [homComplexFunctor_obj_map_f_π.{u, v, max u v r, max u v r} (f + g),
    homComplexFunctor_obj_map_f_π.{u, v, max u v r, max u v r} f,
    homComplexFunctor_obj_map_f_π.{u, v, max u v r, max u v r} g,
    HomologicalComplex.add_f_apply]
  rw [← Preadditive.comp_add]
  congr 1

private theorem tensorFixedAdditive (R : Sheaf J CommRingCat.{max u v r})
    (B : CochainComplex (Modules.{u, v, r} J R) ℤ) :
    (tensorFixed.{u, v, r} J R B).Additive := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := tensorPreadditive.{u, v, r} J R
  let F := Functor.map₂HomologicalComplex (curriedTensor (Modules.{u, v, r} J R))
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
  let S := HomologicalComplex.single (Modules.{u, v, r} J R) (ComplexShape.up ℤ) 0
  constructor
  intro X Y f g
  change (F.map (S.map (f + g))).app B ≫ (F.obj (S.obj Y)).map (𝟙 B) =
    (F.map (S.map f)).app B ≫ (F.obj (S.obj Y)).map (𝟙 B) +
      (F.map (S.map g)).app B ≫ (F.obj (S.obj Y)).map (𝟙 B)
  simp only [Functor.map_add, NatTrans.app_add, Preadditive.add_comp]

private theorem tensorQuasiIso
    (R : Sheaf J CommRingCat.{max u v r}) (T : Modules.{u, v, r} J R)
    (d : ℕ) (e : T ≅ ∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((sheafCompose J
      (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R))
    {K L : CochainComplex (Modules.{u, v, r} J R) ℤ}
    (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((tensor.{u, v, r} J R).map (X := (T, K)) (Y := (T, L)) (𝟙 T, f)) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := tensorPreadditive.{u, v, r} J R
  let A := Modules.{u, v, r} J R
  have := (tensorFinitePowerExact.{u, v, r} J R T d e).1
  have := (tensorFinitePowerExact.{u, v, r} J R T d e).2
  let a := CochainComplex.map₂HomologicalComplexObjSingleIso (curriedTensor A) T
  have : QuasiIso (((tensorLeft T).mapHomologicalComplex (.up ℤ)).map f) :=
    inferInstance
  have h := a.hom.naturality f
  change HomologicalComplex.mapBifunctorMap
      (𝟙 ((HomologicalComplex.single A (.up ℤ) 0).obj T)) f (curriedTensor A) (.up ℤ) ≫
    (a.app L).hom = (a.app K).hom ≫ _ at h
  have : QuasiIso (HomologicalComplex.mapBifunctorMap
      (𝟙 ((HomologicalComplex.single A (.up ℤ) 0).obj T)) f
      (curriedTensor A) (.up ℤ)) := by
    apply (quasiIso_iff_comp_right _ (a.app L).hom).mp
    rw [h]
    infer_instance
  change QuasiIso ((Functor.uncurry.obj (Functor.map₂HomologicalComplex
    (curriedTensor A) (.up ℤ) (.up ℤ) (.up ℤ))).map
      (X := ((HomologicalComplex.single A (.up ℤ) 0).obj T, K))
      (Y := ((HomologicalComplex.single A (.up ℤ) 0).obj T, L))
      ((HomologicalComplex.single A (.up ℤ) 0).map (𝟙 T), f))
  rw [Functor.uncurry_obj_map,
    (HomologicalComplex.single A (.up ℤ) 0).map_id T,
    (Functor.map₂HomologicalComplex (curriedTensor A) (.up ℤ) (.up ℤ) (.up ℤ)).map_id,
    NatTrans.id_app, Category.id_comp]
  exact this

private theorem resolutionProperties (R : Sheaf J CommRingCat.{max u v r})
    (K : CochainComplex (Modules.{u, v, r} J R) ℤ) :
    QuasiIso ((resolutionUnit.{u, v, r} J R).app K) ∧
      ((coefficientHomResolution.{r, u, v} J R).obj K).IsKInjective := by
  let := (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u, v, r}
    J R).1
  exact ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max u v r} _ K).2,
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max u v r} _ K⟩

private theorem homFixedQuasiIso (R : Sheaf J CommRingCat.{max u v r})
    (P : CochainComplex (Modules.{u, v, r} J R) ℤ)
    {K L : CochainComplex (Modules.{u, v, r} J R) ℤ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((homFixed.{u, v, r} J R P).map f) := by
  have := (resolutionProperties.{u, v, r} J R K).1
  have := (resolutionProperties.{u, v, r} J R L).1
  have := (resolutionProperties.{u, v, r} J R K).2
  have := (resolutionProperties.{u, v, r} J R L).2
  have : QuasiIso ((coefficientHomResolution.{r, u, v} J R).map f) := by
    apply (quasiIso_iff_comp_left ((resolutionUnit.{u, v, r} J R).app K) _).mp
    rw [← (resolutionUnit.{u, v, r} J R).naturality f]
    change QuasiIso (f ≫ (resolutionUnit.{u, v, r} J R).app L)
    infer_instance
  have h := quasiIso_homComplex_mapOfUniverses.{u, v, r}
    ((coefficientHomResolution.{r, u, v} J R).map f) (𝟙 P)
  rw [op_id, (homComplexFunctor (R := R)).map_id, NatTrans.id_app,
    Category.id_comp] at h
  exact h

private theorem denominatorFiniteFree (R : Sheaf J CommRingCat.{max u v r})
    (T : Modules.{u, v, r} J R) (d : ℕ)
    (e : T ≅ ∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((sheafCompose J
      (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R))
    (P L : CochainComplex (Modules.{u, v, r} J R) ℤ) :
    QuasiIso (roofDenominator.{u, v, r} J R P L T) := by
  have := (resolutionProperties.{u, v, r} J R L).1
  have := tensorQuasiIso.{u, v, r} J R T d e ((resolutionUnit.{u, v, r} J R).app L)
  exact homFixedQuasiIso.{u, v, r} J R P _

omit [HasSheafify J AddCommGrpCat.{max u v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}] in
private lemma homObj_ext_at_identity (R : Sheaf J CommRingCat.{max u v r})
    {A M N : Modules.{u, v, r} J R} (f g : A ⟶ SheafOfModules.homObj (R := R) M N)
    (h : ∀ (U : Cᵒᵖ) (a : A.val.obj U) (x : M.val.obj U),
      ((f.val.app U a).app (op (Over.mk (𝟙 U.unop)))).hom x =
        ((g.val.app U a).app (op (Over.mk (𝟙 U.unop)))).hom x) : f = g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hf := PresheafOfModules.naturality_apply f.val W.unop.hom.op a
  have hg := PresheafOfModules.naturality_apply g.val W.unop.hom.op a
  have hf' := congrArg (fun k ↦ (k.app (op (Over.mk (𝟙 W.unop.left)))).hom x) hf
  have hg' := congrArg (fun k ↦ (k.app (op (Over.mk (𝟙 W.unop.left)))).hom x) hg
  have hc := PresheafOfModules.restrictOver_hom_app_congr
    (f.val.app U a) (Category.id_comp W.unop.hom) x
  have hc' := PresheafOfModules.restrictOver_hom_app_congr
    (g.val.app U a) (Category.id_comp W.unop.hom) x
  exact hc.symm.trans (hf'.symm.trans ((h _ _ _).trans (hg'.trans hc')))

omit [HasSheafify J AddCommGrpCat.{max u v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}] in
private lemma homValue_ext (R : Sheaf J CommRingCat.{max u v r})
    (P Q K : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (f g : K ⟶ homComplex (R := R) P Q)
    (h : ∀ (n p q : ℤ) (hpq : p + n = q) (U : Cᵒᵖ)
      (k : (K.X n).val.obj U) (x : (P.X p).val.obj U),
      homValue.{u, v, r} J R P Q n p q hpq U ((f.f n).val.app U k) x =
        homValue.{u, v, r} J R P Q n p q hpq U ((g.f n).val.app U k) x) : f = g := by
  ext n : 1
  apply homComplex_hom_ext
  intro p q hpq
  apply homObj_ext_at_identity.{u, v, r} J R
  intro U k x
  exact h n p q hpq U k x

omit [HasSheafify J AddCommGrpCat.{max u v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}] in
private lemma homValue_map (R : Sheaf J CommRingCat.{max u v r})
    (P Q Q' : CochainComplex (Modules.{u, v, r} J R) ℤ) (g : Q ⟶ Q')
    (n p q : ℤ) (hpq : p + n = q) (U : Cᵒᵖ)
    (f : ((homComplex (R := R) P Q).X n).val.obj U) (x : (P.X p).val.obj U) :
    homValue.{u, v, r} J R P Q' n p q hpq U
      (((((homComplexFunctor (R := R)).obj (op P)).map g).f n).val.app U f) x =
        (g.f q).val.app U (homValue.{u, v, r} J R P Q n p q hpq U f x) := by
  have h := homComplexFunctor_obj_map_f_π.{u, v, max u v r, max u v r} (L := P) g n p q hpq
  have h' := congrArg (fun k ↦ ((k.val.app U f).app
    (op (Over.mk (𝟙 U.unop)))).hom x) h
  exact h'

private lemma tensorPresentationNaturality
    {D E : Type*} [Category D] [Category E] [MonoidalCategory D] [MonoidalCategory E]
    (a : D ⥤ E) [a.Monoidal] (i : E ⥤ D) (ε : i ⋙ a ≅ 𝟭 E)
    (M N N' : E) (f : N ⟶ N') :
    M ◁ f ≫ ((ε.app M ⊗ᵢ ε.app N').symm ≪≫
        Functor.Monoidal.μIso a (i.obj M) (i.obj N')).hom =
      ((ε.app M ⊗ᵢ ε.app N).symm ≪≫
        Functor.Monoidal.μIso a (i.obj M) (i.obj N)).hom ≫
          a.map (i.obj M ◁ i.map f) := by
  let j (M : E) : M ⟶ a.obj (i.obj M) := ε.inv.app M
  have hn : f ≫ j N' = j N ≫ a.map (i.map f) := ε.inv.naturality f
  have ht : (𝟙 M ⊗ₘ f) ≫ (j M ⊗ₘ j N') =
      (j M ⊗ₘ j N) ≫ (𝟙 (a.obj (i.obj M)) ⊗ₘ a.map (i.map f)) := by
    simpa only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id] using
      congrArg (fun k ↦ j M ⊗ₘ k) hn
  simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_inv, Iso.app_inv,
    Functor.Monoidal.μIso_hom]
  change M ◁ f ≫ (j M ⊗ₘ j N') ≫ Functor.LaxMonoidal.μ a (i.obj M) (i.obj N') =
    ((j M ⊗ₘ j N) ≫ Functor.LaxMonoidal.μ a (i.obj M) (i.obj N)) ≫
      a.map (i.obj M ◁ i.map f)
  have hμ := Functor.LaxMonoidal.μ_natural a (𝟙 (i.obj M)) (i.map f)
  rw [a.map_id] at hμ
  rw [← id_tensorHom M f, ← id_tensorHom (i.obj M) (i.map f),
    Category.assoc, ← Category.assoc (𝟙 M ⊗ₘ f), ht, Category.assoc, hμ]

section RegularTensor
variable (R : Sheaf J CommRingCat.{max u v r})
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.monoidalCategory
set_option quotPrecheck false
set_option hygiene false in
local notation "A" => Modules.{u, v, r} J R
set_option hygiene false in
local notation "O" => (sheafCompose J
  (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R

private noncomputable def regularTensorIso (M : A) :
    (SheafOfModules.unit O) ⊗ M ≅ M :=
  SheafOfModules.tensorObjIsoSheafification _ M ≪≫
    (PresheafOfModules.sheafification (𝟙 (O).obj)).mapIso (λ_ M.val) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 (O).obj)).counit).app M

private lemma tensorComparison_naturality {N N' : A} (M : A) (f : N ⟶ N') :
    M ◁ f ≫ (SheafOfModules.tensorObjIsoSheafification M N').hom =
      (SheafOfModules.tensorObjIsoSheafification M N).hom ≫
        (PresheafOfModules.sheafification (𝟙 (O).obj)).map (M.val ◁ f.val) := by
  let a := PresheafOfModules.sheafification (𝟙 (O).obj)
  let i := SheafOfModules.forget O
  let ε : i ⋙ a ≅ 𝟭 A :=
    asIso (PresheafOfModules.sheafificationAdjunction (𝟙 (O).obj)).counit
  exact tensorPresentationNaturality a i ε M N N' f

private noncomputable def regularTensorNatIso : tensorLeft (SheafOfModules.unit O) ≅ 𝟭 A :=
  NatIso.ofComponents (regularTensorIso.{u, v, r} J R) (by
    intro M N f
    dsimp only [regularTensorIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
      asIso_hom, Functor.id_map]
    change (SheafOfModules.unit O) ◁ f ≫ _ = _
    rw [← Category.assoc, ← Category.assoc,
      tensorComparison_naturality.{u, v, r} J R]
    simp only [Category.assoc, ← Functor.map_comp_assoc]
    change _ ≫ (PresheafOfModules.sheafification (𝟙 (O).obj)).map
      ((𝟙_ (PresheafOfModules (O).obj)) ◁ f.val ≫ (λ_ N.val).hom) ≫ _ = _
    rw [leftUnitor_naturality]
    simp only [Functor.map_comp, Category.assoc]
    congr 1
    congr 1
    exact (PresheafOfModules.sheafificationAdjunction (𝟙 (O).obj)).counit.naturality f)

private lemma regularTensorIso_inv_apply (M : A) (V : Cᵒᵖ) (x : M.val.obj V) :
    (regularTensorIso.{u, v, r} J R M).inv.val.app V x =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (O).obj)).unit.app
        ((SheafOfModules.unit O).val ⊗ M.val) ≫
          (SheafOfModules.tensorObjIsoSheafification (SheafOfModules.unit O) M).inv.val).app V
            ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (O).obj)
  have : IsIso adj.counit := by dsimp [adj]; infer_instance
  let e := (asIso adj.counit).app M
  let f := (SheafOfModules.forget O).mapIso e
  have hc : e.inv.val = adj.unit.app M.val := by
    apply (cancel_mono f.hom).1
    change e.inv.val ≫ e.hom.val = adj.unit.app M.val ≫ e.hom.val
    have h := adj.right_triangle_components M
    have hi := congrArg SheafOfModules.Hom.val e.inv_hom_id
    exact hi.trans h.symm
  have hn := adj.unit.naturality (λ_ M.val).inv
  have h := congrArg (fun f ↦ f.app V x) hn
  simp only [regularTensorIso, Iso.trans_inv, Functor.mapIso_inv, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply]
  rw [hc]
  simp only [Functor.id_map, Functor.comp_map,
    PresheafOfModules.comp_app, ModuleCat.comp_apply] at h
  erw [← h]
  rfl

private noncomputable def tensorUnitIso
    (B : CochainComplex A ℤ) :
    (tensor.{u, v, r} J R).obj (SheafOfModules.unit O, B) ≅ B := by
  let := tensorPreadditive.{u, v, r} J R
  exact CochainComplex.mapBifunctorSingle₁Iso (curriedTensor A) (SheafOfModules.unit O) B ≪≫
    (NatIso.mapHomologicalComplex (regularTensorNatIso.{u, v, r} J R) (.up ℤ)).app B ≪≫
    (Functor.mapHomologicalComplexIdIso A (.up ℤ)).app B

private lemma tensorUnitIso_inv_apply (B : CochainComplex A ℤ)
    (n : ℤ) (U : Cᵒᵖ) (x : (B.X n).val.obj U) :
    ((tensorUnitIso.{u, v, r} J R B).inv.f n).val.app U x =
      tensorGenerator.{u, v, r} J R (SheafOfModules.unit O) B n U (1 : R.obj.obj U) x := by
  let := tensorPreadditive.{u, v, r} J R
  change (((CochainComplex.mapBifunctorSingle₁Iso (curriedTensor A)
    (SheafOfModules.unit O) B).inv.f n).val.app U)
      ((regularTensorIso.{u, v, r} J R (B.X n)).inv.val.app U x) = _
  rw [regularTensorIso_inv_apply.{u, v, r} J R]
  rw [CochainComplex.mapBifunctorSingle₁Iso_inv_f]
  have he : (HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (SheafOfModules.unit O)).inv = 𝟙 (SheafOfModules.unit O) := by rfl
  rw [he, (curriedTensor A).map_id, NatTrans.id_app, Category.id_comp]
  rfl

private noncomputable def finitePowerFanLimit (T : A) (d : ℕ)
    (e : T ≅ ∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit O) :
    IsLimit (Fan.mk T (fun i : Fin d ↦ e.hom ≫
      Pi.π (fun _ : Fin d ↦ SheafOfModules.unit O) i)) :=
  Fan.IsLimit.ofIsos (productIsProduct _) (fun _ ↦ Iso.refl _) e (fun _ ↦ by simp)

private lemma tensorKInjective (T : A) (d : ℕ)
    (e : T ≅ ∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit O)
    (B : CochainComplex A ℤ) [B.IsKInjective] :
    ((tensorFixed.{u, v, r} J R B).obj T).IsKInjective := by
  have := tensorFixedAdditive.{u, v, r} J R B
  have hunit : ((tensorFixed.{u, v, r} J R B).obj (SheafOfModules.unit O)).IsKInjective :=
    CochainComplex.isKInjective_of_iso (tensorUnitIso.{u, v, r} J R B).symm
  have (_ : Fin d) :
      ((tensorFixed.{u, v, r} J R B).obj (SheafOfModules.unit O)).IsKInjective := hunit
  exact CochainComplex.isKInjective_of_isLimitFan
    (isLimitFanMkObjOfIsLimit (tensorFixed.{u, v, r} J R B) _ _
      (finitePowerFanLimit.{u, v, r} J R T d e))

private lemma rawToResolvedQuasiIso (P K : CochainComplex A ℤ) [K.IsKInjective] :
    QuasiIso (((homComplexFunctor (R := R)).obj (op P)).map
      ((resolutionUnit.{u, v, r} J R).app K)) := by
  have := (resolutionProperties.{u, v, r} J R K).1
  have := (resolutionProperties.{u, v, r} J R K).2
  have h := quasiIso_homComplex_mapOfUniverses.{u, v, r}
    (I' := K) ((resolutionUnit.{u, v, r} J R).app K) (𝟙 P)
  rwa [op_id, (homComplexFunctor (R := R)).map_id, NatTrans.id_app,
    Category.id_comp] at h

private lemma comparison_at_unit (P L : CochainComplex A ℤ) :
    (tensorUnitIso.{u, v, r} J R ((homFixed.{u, v, r} J R P).obj L)).inv ≫
        (comparison.{u, v, r} J R P L).app (SheafOfModules.unit O) =
      ((homComplexFunctor (R := R)).obj (op P)).map
        ((tensorUnitIso.{u, v, r} J R
          ((coefficientHomResolution.{r, u, v} J R).obj L)).inv ≫
          (resolutionUnit.{u, v, r} J R).app
            ((tensorFixed.{u, v, r} J R
              ((coefficientHomResolution.{r, u, v} J R).obj L)).obj
                (SheafOfModules.unit O))) := by
  let I := (coefficientHomResolution.{r, u, v} J R).obj L
  let K := (tensor.{u, v, r} J R).obj (SheafOfModules.unit O, I)
  let g : I ⟶ (coefficientHomResolution.{r, u, v} J R).obj K :=
    (tensorUnitIso.{u, v, r} J R I).inv ≫ (resolutionUnit.{u, v, r} J R).app K
  have ha : Normalized.{u, v, r} J R P L (comparison.{u, v, r} J R P L) :=
    (comparison_existsUnique.{u, v, r} J R P L).exists.choose_spec
  apply homValue_ext.{u, v, r} J R P
    ((coefficientHomResolution.{r, u, v} J R).obj K) (homComplex (R := R) P I)
  intro n p q hpq U k x
  have hm := homValue_map.{u, v, r} J R P I
    ((coefficientHomResolution.{r, u, v} J R).obj K) g n p q hpq U k x
  change _ = (((resolutionUnit.{u, v, r} J R).app K).f q).val.app U
    (((tensorUnitIso.{u, v, r} J R I).inv.f q).val.app U
      (homValue.{u, v, r} J R P I n p q hpq U k x)) at hm
  rw [tensorUnitIso_inv_apply.{u, v, r} J R I] at hm
  have hn := ha (SheafOfModules.unit O) n p q hpq U (1 : R.obj.obj U) k x
  have hgen := tensorUnitIso_inv_apply.{u, v, r} J R
    ((homFixed.{u, v, r} J R P).obj L) n U k
  change homValue.{u, v, r} J R P _ n p q hpq U
    ((((comparison.{u, v, r} J R P L).app (SheafOfModules.unit O)).f n).val.app U
      (((tensorUnitIso.{u, v, r} J R ((homFixed.{u, v, r} J R P).obj L)).inv.f n).val.app
        U k)) x = _
  rw [hgen]
  exact hn.trans hm.symm

private lemma comparison_unit_quasiIso (P L : CochainComplex A ℤ) :
    QuasiIso ((comparison.{u, v, r} J R P L).app (SheafOfModules.unit O)) := by
  let I := (coefficientHomResolution.{r, u, v} J R).obj L
  have : I.IsKInjective := (resolutionProperties.{u, v, r} J R L).2
  have hI : ((tensorFixed.{u, v, r} J R I).obj (SheafOfModules.unit O)).IsKInjective :=
    CochainComplex.isKInjective_of_iso (tensorUnitIso.{u, v, r} J R I).symm
  have : QuasiIso (((homComplexFunctor (R := R)).obj (op P)).map
      ((tensorUnitIso.{u, v, r} J R I).inv ≫
        (resolutionUnit.{u, v, r} J R).app _)) := by
    rw [Functor.map_comp]
    exact (quasiIso_iff_comp_left _ _).mpr
      (rawToResolvedQuasiIso.{u, v, r} J R P
        ((tensorFixed.{u, v, r} J R I).obj (SheafOfModules.unit O)))
  apply (quasiIso_iff_comp_left
    (tensorUnitIso.{u, v, r} J R ((homFixed.{u, v, r} J R P).obj L)).inv _).mp
  rw [comparison_at_unit.{u, v, r} J R]
  exact this

private lemma numeratorFiniteFree (T : A) (d : ℕ)
    (e : T ≅ ∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit O)
    (P L : CochainComplex A ℤ) :
    QuasiIso ((comparison.{u, v, r} J R P L).app T) := by
  let B := (coefficientHomResolution.{r, u, v} J R).obj L
  let V := tensorFixed.{u, v, r} J R B
  let H := (homComplexFunctor (R := R)).obj (op P)
  have : B.IsKInjective := (resolutionProperties.{u, v, r} J R L).2
  have : (V.obj T).IsKInjective := tensorKInjective.{u, v, r} J R T d e B
  have : (V.obj (SheafOfModules.unit O)).IsKInjective :=
    CochainComplex.isKInjective_of_iso (tensorUnitIso.{u, v, r} J R B).symm
  let ψ : V ⋙ H ⟶ V ⋙ homFixed.{u, v, r} J R P :=
    Functor.whiskerLeft V (Functor.whiskerRight (resolutionUnit.{u, v, r} J R) H)
  have : QuasiIso (ψ.app T) := rawToResolvedQuasiIso.{u, v, r} J R P (V.obj T)
  have : QuasiIso (ψ.app (SheafOfModules.unit O)) :=
    rawToResolvedQuasiIso.{u, v, r} J R P (V.obj (SheafOfModules.unit O))
  have := comparison_unit_quasiIso.{u, v, r} J R P L
  have := tensorFixedAdditive.{u, v, r} J R B
  have := tensorFixedAdditive.{u, v, r} J R ((homFixed.{u, v, r} J R P).obj L)
  have := rawHomAdditive.{u, v, r} J R P
  let π (i : Fin d) := e.hom ≫ Pi.π (fun _ : Fin d ↦ SheafOfModules.unit O) i
  have hπ := finitePowerFanLimit.{u, v, r} J R T d e
  refine ⟨fun n ↦ ?_⟩
  apply (quasiIsoAt_iff_isIso_homologyMap _ n).mpr
  let h := HomologicalComplex.homologyFunctor A (.up ℤ) n
  let F := tensorFixed.{u, v, r} J R ((homFixed.{u, v, r} J R P).obj L) ⋙ h
  let F' := (V ⋙ H) ⋙ h
  let G := (V ⋙ homFixed.{u, v, r} J R P) ⋙ h
  let a : F ⟶ G := Functor.whiskerRight (comparison.{u, v, r} J R P L) h
  let b : F' ⟶ G := Functor.whiskerRight ψ h
  have : IsIso (b.app T) :=
    (quasiIsoAt_iff_isIso_homologyMap (ψ.app T) n).mp inferInstance
  have : IsIso (b.app (SheafOfModules.unit O)) :=
    (quasiIsoAt_iff_isIso_homologyMap
      (ψ.app (SheafOfModules.unit O)) n).mp inferInstance
  have : IsIso (a.app (SheafOfModules.unit O)) :=
    (quasiIsoAt_iff_isIso_homologyMap
      ((comparison.{u, v, r} J R P L).app (SheafOfModules.unit O)) n).mp inferInstance
  have hF := isLimitFanMkObjOfIsLimit F _ π hπ
  have hF' := isLimitFanMkObjOfIsLimit F' _ π hπ
  have hG : IsLimit (Fan.mk (G.obj T) (fun i : Fin d ↦ G.map (π i))) := by
    refine Fan.IsLimit.ofIsos hF'
      (fun _ ↦ (asIso (b.app (SheafOfModules.unit O))).symm)
      (asIso (b.app T)).symm ?_
    intro i
    change inv (b.app T) ≫ F'.map (π i) =
      G.map (π i) ≫ inv (b.app (SheafOfModules.unit O))
    apply (cancel_mono (b.app (SheafOfModules.unit O))).1
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [b.naturality, IsIso.inv_hom_id_assoc]
  exact Fan.IsLimit.isIso_of_isos hF hG
    (fun _ ↦ asIso (a.app (SheafOfModules.unit O))) (a.app T)
    (fun i ↦ (a.naturality (π i)).symm)

end RegularTensor

/-- A finite-free coefficient module gives quasi-isomorphisms in the strict Hom roof.
Source: Bhatt--Scholze, Remark 6.8.15, finite-free case of the conditional ring-sheaf
argument; Stacks Project, Tags 08J9 and 079P.
(blueprint: lem-sfb-internal-hom-finite-free-stage).

Proof: choose the given isomorphism with a finite power of the unit. Tensoring by this
module is naturally a finite direct sum of the identity, and therefore exact. Its tensor
with the augmentation of L is a quasi-isomorphism, which the functorial derived Hom
representative preserves. This proves the denominator assertion. Finite direct sums of
the chosen K-injective replacement of L are K-injective, and internal Hom commutes with
these finite sums. Under these identifications the normalized comparison is the finite
sum of the identity followed by the target augmentation. Applying Hom to the resulting
quasi-isomorphism between K-injectives gives a quasi-isomorphism. The evaluation formula
fixes this identification independently of the chosen basis. For rank zero all complexes
and maps are zero, and both assertions still hold. No boundedness is required. -/
theorem internalHom_finiteFree_stage (R : Sheaf J CommRingCat.{max u v r})
    (T : Modules.{u, v, r} J R)
    (hfree : ∃ d : ℕ, Nonempty
      (T ≅ limit (Discrete.functor (fun _ : Fin d ↦
        SheafOfModules.unit ((sheafCompose J
          (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R)))))
    (P L : CochainComplex (Modules.{u, v, r} J R) ℤ) :
    QuasiIso ((comparison.{u, v, r} J R P L).app T) ∧
      QuasiIso (roofDenominator.{u, v, r} J R P L T) := by
  obtain ⟨d, ⟨e⟩⟩ := hfree
  exact ⟨numeratorFiniteFree.{u, v, r} J R T d e P L,
    denominatorFiniteFree.{u, v, r} J R T d e P L⟩

end WeilConjectures.SfbHomFilteredColimit
