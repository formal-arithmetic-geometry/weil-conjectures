/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A8
-/
module

public import Sheaf.Paper.PointDerivedHomModels
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all Sheaf.SecSmoothPurity.CochainInverseComparison
import all Sheaf.SecSmoothPurity.CochainCoefficientArrows
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.HomComplexComponents
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-! # Sheaf evaluation and tensoring sections at a point

Source: Stacks Project, Tags 0A8X and 08J7.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace WeilConjectures.PointDerivedHom

variable (k : Type t) [Field k]
  {R : CommRingCat.{max u (t + 1)}}
  (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{max u (t + 1)})
  (α : constantRing.{t, u} k R ⟶ B)
  (L : ModuleCat.{max u (t + 1)} R ⥤ Modules.{t, u} k B)
  (hobj : ∀ M : ModuleCat.{max u (t + 1)} R,
    L.obj M = extensionObject.{t, u} k B α M)
  (adj : L ⊣ sections.{t, u} k B α)
  (c : CochainComplex (ModuleCat.{max u (t + 1)} R) ℤ)

namespace EvaluationConstruction

open CategoryTheory.MonoidalCategory
open SheafOfModules.CochainScalarConstruction
open scoped TensorProduct

attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.tensorObjIsoSheafification
  PresheafOfModules.sheafificationAdjunction
  PresheafOfModules.sheafification

local instance (priority := 10000) : MonoidalCategory (Modules.{t, u} k B) :=
  SheafOfModules.monoidalCategory B

local instance : HasColimitsOfSize.{0, 0} (Modules.{t, u} k B) :=
  IntegralHom.countableColimits (Spec (.of k)) B

local instance (P Q : CochainComplex (Modules.{t, u} k B) ℤ) :
    HomologicalComplex.HasMapBifunctor P Q
      (IntegralHom.ordinaryTensor.{t, u} (Spec (.of k)) B) (.up ℤ) := by
  infer_instance

variable (P I : CochainComplex (Modules.{t, u} k B) ℤ)

private def value (p j n : ℤ) (hpj : p + j = n)
    (U : (Scheme.ProEt (Spec (.of k)))ᵒᵖ)
    (h : ((sheafHom.{t, u} k B P I).X j).val.obj U)
    (x : (P.X p).val.obj U) : (I.X n).val.obj U :=
  (((homComplexπ.{t + 1, t, max u (t + 1), max u (t + 1)}
    (R := B) P I j p n hpj).val.app U h).app
    (op (Over.mk (𝟙 U.unop)))).hom x

private def term (p j n : ℤ) (hpj : p + j = n) :
    P.X p ⊗ (sheafHom.{t, u} k B P I).X j ⟶ I.X n :=
  let π := homComplexπ.{t + 1, t, max u (t + 1), max u (t + 1)} (R := B) P I j p n hpj
  let a := PresheafOfModules.sheafificationAdjunction.{max u (t + 1)}
    (𝟙 (ring.{t, u} k B).obj)
  (p * j).negOnePow • ((SheafOfModules.tensorObjIsoSheafification
    (P.X p) ((sheafHom.{t, u} k B P I).X j)).hom ≫
      (a.homEquiv _ (I.X n)).symm (CategoryTheory.IsoTensorHom.tensorHomUncurry.{t + 1, t, u}
        (R := B.obj) (M := (P.X p).val)
        (P := ((sheafHom.{t, u} k B P I).X j).val) (N := (I.X n).val) π.val))

private theorem uncurry_apply (M N V : Modules.{t, u} k B)
    (ψ : M.val ⊗ N.val ⟶ V.val)
    (U : (Scheme.ProEt (Spec (.of k)))ᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    ((SheafOfModules.tensorObjIsoSheafification M N).hom ≫
      ((PresheafOfModules.sheafificationAdjunction.{max u (t + 1)}
        (𝟙 (ring.{t, u} k B).obj)).homEquiv _ V).symm ψ).val.app U
        (pure B M N U x y) = ψ.app U (x ⊗ₜ[B.obj.obj U] y) := by
  let a := PresheafOfModules.sheafificationAdjunction.{max u (t + 1)}
    (𝟙 (ring.{t, u} k B).obj)
  let e := SheafOfModules.tensorObjIsoSheafification M N
  let f := (a.homEquiv _ V).symm ψ
  have hh : a.homEquiv _ V (e.inv ≫ e.hom ≫ f) = ψ := by
    rw [e.inv_hom_id_assoc]
    exact (a.homEquiv _ V).apply_symm_apply ψ
  rw [Adjunction.homEquiv_unit] at hh
  exact congrArg (fun g ↦ (g.app U).hom (x ⊗ₜ[B.obj.obj U] y)) hh


private theorem scalar_app {M N : Modules.{t, u} k B} (a : ℤˣ) (f : M ⟶ N)
    (U : (Scheme.ProEt (Spec (.of k)))ᵒᵖ) (x : M.val.obj U) :
    (a • f).val.app U x = a • f.val.app U x := by
  let V := SheafOfModules.forget (ring.{t, u} k B) ⋙
    PresheafOfModules.evaluation (ring.{t, u} k B).obj U
  change (V.map (a • f)).hom x = _
  simp only [Units.smul_def, Functor.map_zsmul, ModuleCat.hom_zsmul,
    LinearMap.smul_apply]
  rfl

private theorem term_apply (p j n : ℤ) (hpj : p + j = n)
    (U : (Scheme.ProEt (Spec (.of k)))ᵒᵖ)
    (x : (P.X p).val.obj U) (h : ((sheafHom.{t, u} k B P I).X j).val.obj U) :
    (term k B P I p j n hpj).val.app U
      (pure B (P.X p) ((sheafHom.{t, u} k B P I).X j) U x h) =
      (p * j).negOnePow • value k B P I p j n hpj U h x := by
  dsimp only [term]
  rw [scalar_app k B, uncurry_apply k B]
  rfl

attribute [local irreducible] term

private def degree (n : ℤ) : (total.{t, u} k B P (sheafHom.{t, u} k B P I)).X n ⟶ I.X n :=
  HomologicalComplex.mapBifunctorDesc (fun p j hpj ↦ term k B P I p j n hpj)

private theorem degree_ι (p j n : ℤ) (hpj : p + j = n) :
    HomologicalComplex.ιMapBifunctor P (sheafHom.{t, u} k B P I)
      (IntegralHom.ordinaryTensor.{t, u} (Spec (.of k)) B) (.up ℤ) p j n hpj ≫
        degree k B P I n = term k B P I p j n hpj :=
  HomologicalComplex.ι_mapBifunctorDesc _ p j hpj

attribute [local irreducible] degree

private theorem section_sub_units
    {M N : Modules.{t, u} k B} (f g : M ⟶ N) (a : ℤˣ)
    (U : (Scheme.ProEt (Spec (.of k)))ᵒᵖ) (x : M.val.obj U) :
    ((f - a • g).val.app U) x = (f.val.app U) x - a • (g.val.app U) x := by
  let V := SheafOfModules.forget (ring.{t, u} k B) ⋙
    PresheafOfModules.evaluation (ring.{t, u} k B).obj U
  change (V.map (f - a • g)).hom x = _
  rw [Functor.map_sub]
  simp only [Units.smul_def, Functor.map_zsmul, ModuleCat.hom_sub,
    ModuleCat.hom_zsmul, LinearMap.sub_apply, LinearMap.smul_apply]
  rfl

private theorem eval_d (p j n : ℤ) (hpj : p + j + 1 = n)
    (U : (Scheme.ProEt (Spec (.of k)))ᵒᵖ)
    (x : (P.X p).val.obj U) (h : ((sheafHom.{t, u} k B P I).X j).val.obj U) :
    value k B P I p (j + 1) n (by omega) U
      ((sheafHom.{t, u} k B P I).d j (j + 1) |>.val.app U h) x =
      (I.d (p + j) n).val.app U (value k B P I p j (p + j) rfl U h x) -
        j.negOnePow • value k B P I (p + 1) j n (by omega) U h
          ((P.d p (p + 1)).val.app U x) := by
  have hd := congrArg (fun f ↦ f.val.app U h)
    (homComplex_d_π (R := B) P I j (j + 1) p n (p + j) (p + 1) rfl (by omega) rfl (by omega))
  rw [section_sub_units k B] at hd
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.hom_comp, LinearMap.comp_apply] at hd
  let ev := CategoryTheory.IsoTensorHom.homObjEvalId.{t + 1, t, u}
    (R := B.obj) (P.X p).val (I.X n).val U.unop
  have he := congrArg (fun f ↦ ev f x) hd
  simp only [map_sub, Units.smul_def, map_zsmul] at he
  exact he

attribute [local irreducible] value

private theorem degree_comm (n m : ℤ) (hnm : n + 1 = m) :
    degree k B P I n ≫ I.d n m =
      (total.{t, u} k B P (sheafHom.{t, u} k B P I)).d n m ≫ degree k B P I m := by
  apply HomologicalComplex.mapBifunctor.hom_ext (K₁ := P)
    (K₂ := sheafHom.{t, u} k B P I)
    (F := IntegralHom.ordinaryTensor.{t, u} (Spec (.of k)) B) (c := .up ℤ)
  intro p j hpj
  change p + j = n at hpj
  subst n
  erw [← Category.assoc, degree_ι k B P I]
  have hd : HomologicalComplex.ιMapBifunctor P (sheafHom.{t, u} k B P I)
      (IntegralHom.ordinaryTensor.{t, u} (Spec (.of k)) B) (.up ℤ) p j (p + j) rfl ≫
        (total.{t, u} k B P (sheafHom.{t, u} k B P I)).d (p + j) m =
      P.d p (p + 1) ▷ (sheafHom.{t, u} k B P I).X j ≫
        HomologicalComplex.ιMapBifunctor P (sheafHom.{t, u} k B P I)
          (IntegralHom.ordinaryTensor.{t, u} (Spec (.of k)) B) (.up ℤ)
          (p + 1) j m (show p + 1 + j = m by omega) +
      p.negOnePow • (P.X p ◁ (sheafHom.{t, u} k B P I).d j (j + 1) ≫
        HomologicalComplex.ιMapBifunctor P (sheafHom.{t, u} k B P I)
          (IntegralHom.ordinaryTensor.{t, u} (Spec (.of k)) B) (.up ℤ)
          p (j + 1) m (show p + (j + 1) = m by omega)) := by
    erw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
      HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
        (rfl : (ComplexShape.up ℤ).Rel p (p + 1)) _ _ (by dsimp; omega),
      HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _
        (rfl : (ComplexShape.up ℤ).Rel j (j + 1)) _ (by dsimp; omega)]
    simp
  erw [← Category.assoc, hd, Preadditive.add_comp]
  simp only [Units.smul_def, Preadditive.zsmul_comp, Category.assoc, degree_ι k B P I]
  apply pure_hom_ext B (P.X p) ((sheafHom.{t, u} k B P I).X j) (I.X m)
  intro U x h
  let V := SheafOfModules.forget (ring.{t, u} k B) ⋙
    PresheafOfModules.evaluation (ring.{t, u} k B).obj U
  change (V.map (_ ≫ _)).hom (pure B _ _ U x h) =
    (V.map (_ + (p.negOnePow : ℤ) • _)).hom (pure B _ _ U x h)
  simp only [Functor.map_comp, Functor.map_add, Functor.map_zsmul, ModuleCat.hom_comp,
    ModuleCat.hom_add, ModuleCat.hom_zsmul, LinearMap.comp_apply,
    LinearMap.add_apply, LinearMap.smul_apply]
  change (I.d (p + j) m).val.app U ((term k B P I p j (p + j) rfl).val.app U
    (pure B _ _ U x h)) =
      (term k B P I (p + 1) j m (by omega)).val.app U
        ((P.d p (p + 1) ▷ (sheafHom.{t, u} k B P I).X j).val.app U
          (pure B _ _ U x h)) +
      (p.negOnePow : ℤ) • (term k B P I p (j + 1) m (by omega)).val.app U
        ((P.X p ◁ (sheafHom.{t, u} k B P I).d j (j + 1)).val.app U
          (pure B _ _ U x h))
  have hpre := pure_map B (P.d p (p + 1)) (𝟙 ((sheafHom.{t, u} k B P I).X j)) U x h
  have hpost := pure_map B (𝟙 (P.X p)) ((sheafHom.{t, u} k B P I).d j (j + 1)) U x h
  erw [tensorHom_id] at hpre
  erw [id_tensorHom] at hpost
  change (P.d p (p + 1) ▷ (sheafHom.{t, u} k B P I).X j).val.app U
    (pure B _ _ U x h) = pure B _ _ U ((P.d p (p + 1)).val.app U x) h at hpre
  change (P.X p ◁ (sheafHom.{t, u} k B P I).d j (j + 1)).val.app U
    (pure B _ _ U x h) = pure B _ _ U x
      ((sheafHom.{t, u} k B P I).d j (j + 1) |>.val.app U h) at hpost
  erw [hpre, hpost]
  have e₀ : (term k B P I p j (p + j) rfl).val.app U
      (pure B _ _ U x h) =
        (p * j).negOnePow • value k B P I p j (p + j) rfl U h x :=
    term_apply k B P I p j (p + j) rfl U x h
  have e₁ : (term k B P I (p + 1) j m (by omega)).val.app U
      (pure B _ _ U ((P.d p (p + 1)).val.app U x) h) =
        ((p + 1) * j).negOnePow • value k B P I (p + 1) j m (by omega) U h
          ((P.d p (p + 1)).val.app U x) :=
    term_apply k B P I (p + 1) j m (by omega) U ((P.d p (p + 1)).val.app U x) h
  have e₂ : (term k B P I p (j + 1) m (by omega)).val.app U
      (pure B _ _ U x ((sheafHom.{t, u} k B P I).d j (j + 1) |>.val.app U h)) =
        (p * (j + 1)).negOnePow • value k B P I p (j + 1) m (by omega) U
          ((sheafHom.{t, u} k B P I).d j (j + 1) |>.val.app U h) x :=
    term_apply k B P I p (j + 1) m (by omega) U x
      ((sheafHom.{t, u} k B P I).d j (j + 1) |>.val.app U h)
  rw [e₀, e₁, e₂]
  change (I.d (p + j) m).val.app U ((p * j).negOnePow •
    value k B P I p j (p + j) rfl U h x) =
      ((p + 1) * j).negOnePow • value k B P I (p + 1) j m (by omega) U h
        ((P.d p (p + 1)).val.app U x) +
      (p.negOnePow : ℤ) • (p * (j + 1)).negOnePow •
        value k B P I p (j + 1) m (by omega) U
          ((sheafHom.{t, u} k B P I).d j (j + 1) |>.val.app U h) x
  rw [eval_d k B P I p j m hnm U x h]
  have hs₀ : p.negOnePow * (p * (j + 1)).negOnePow = (p * j).negOnePow := by
    rw [← Int.negOnePow_add, show p + p * (j + 1) = p * j + 2 * p by ring,
      Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]
  have hs : (p.negOnePow : ℤ) * ((p * (j + 1)).negOnePow : ℤ) =
      ((p * j).negOnePow : ℤ) := congrArg Units.val hs₀
  have hb : (((p + 1) * j).negOnePow : ℤ) =
      ((p * j).negOnePow : ℤ) * (j.negOnePow : ℤ) := by
    rw [show (p + 1) * j = p * j + j by ring, Int.negOnePow_add]
    rfl
  simp only [Units.smul_def, map_zsmul, smul_smul, hs, hb, smul_sub]
  simp only [← mul_assoc, hs]
  abel

private theorem degree_on_totalElement (p j : ℤ)
    (U : (Scheme.ProEt (Spec (.of k)))ᵒᵖ)
    (x : (P.X p).val.obj U) (h : ((sheafHom.{t, u} k B P I).X j).val.obj U) :
    (degree k B P I (p + j)).val.app U
      (totalElement.{t, u} k B P (sheafHom.{t, u} k B P I) p j U x h) =
        (p * j).negOnePow • homValue.{t, u} k B P I j p U h x := by
  have hi := congrArg (fun f ↦ f.val.app U
    (pure B (P.X p) ((sheafHom.{t, u} k B P I).X j) U x h))
    (degree_ι k B P I p j (p + j) rfl)
  change (degree k B P I (p + j)).val.app U
    (totalElement.{t, u} k B P (sheafHom.{t, u} k B P I) p j U x h) =
      (term k B P I p j (p + j) rfl).val.app U
        (pure B (P.X p) ((sheafHom.{t, u} k B P I).X j) U x h) at hi
  have ht := term_apply k B P I p j (p + j) rfl U x h
  with_unfolding_all exact hi.trans ht

end EvaluationConstruction

namespace SectionsTensorConstruction

open CategoryTheory.MonoidalCategory
open SheafOfModules.CochainScalarConstruction
open scoped TensorProduct

attribute [local irreducible] SheafOfModules.monoidalCategory

local instance (priority := 10000) : MonoidalCategory (Modules.{t, u} k B) :=
  SheafOfModules.monoidalCategory B

local instance : HasColimitsOfSize.{0, 0} (Modules.{t, u} k B) :=
  IntegralHom.countableColimits.{t, u} (Spec (.of k)) B

private def bilin (M N : Modules.{t, u} k B) :
    (sections.{t, u} k B α).obj M →ₗ[R]
      (sections.{t, u} k B α).obj N →ₗ[R]
        (sections.{t, u} k B α).obj (M ⊗ N) where
  toFun x :=
    { toFun := fun y ↦ pure B M N (op (finalObject k)) x y
      map_add' := fun y z ↦ pure_add_right B M N _ x y z
      map_smul' := by
        intro r y
        change pure B M N (op (finalObject k)) x
          (scalar.{t, u} k B α (op (finalObject k)) r •
            (show N.val.obj (op (finalObject k)) from y)) =
          scalar.{t, u} k B α (op (finalObject k)) r • pure B M N (op (finalObject k)) x y
        exact pure_smul_right B M N _ _ x y }
  map_add' x y := by
    ext z
    exact pure_add_left B M N _ x y z
  map_smul' r x := by
    ext y
    change pure B M N (op (finalObject k))
      (scalar.{t, u} k B α (op (finalObject k)) r •
        (show M.val.obj (op (finalObject k)) from x)) y =
      scalar.{t, u} k B α (op (finalObject k)) r • pure B M N (op (finalObject k)) x y
    exact pure_smul_left B M N _ _ x y

private def component (M N : Modules.{t, u} k B) :
    (sections.{t, u} k B α).obj M ⊗ (sections.{t, u} k B α).obj N ⟶
      (sections.{t, u} k B α).obj (M ⊗ N) :=
  ModuleCat.homEquiv.symm (TensorProduct.lift (bilin k B α M N))

private theorem component_natural
    {M M' N N' : Modules.{t, u} k B} (f : M ⟶ M') (g : N ⟶ N') :
    component k B α M N ≫ (sections.{t, u} k B α).map (f ⊗ₘ g) =
      ((sections.{t, u} k B α).map f ⊗ₘ (sections.{t, u} k B α).map g) ≫
        component k B α M' N' := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  exact pure_map B f g (op (finalObject k)) x y

private def chain (P H : CochainComplex (Modules.{t, u} k B) ℤ) :
    moduleTotal ((sectionComplex.{t, u} k B α).obj P)
      ((sectionComplex.{t, u} k B α).obj H) ⟶
        (sectionComplex.{t, u} k B α).obj (total.{t, u} k B P H) :=
  { f := CategoryTheory.CochainPullback.laxTotalComponent
      (sections.{t, u} k B α) (component k B α) P H
    comm' := fun n m _ ↦ CategoryTheory.CochainPullback.laxTotalComponent_comm
      (sections.{t, u} k B α) (component k B α) (component_natural k B α) P H n m }

private theorem chain_apply (P H : CochainComplex (Modules.{t, u} k B) ℤ)
    (p j : ℤ) (x : ((sectionComplex.{t, u} k B α).obj P).X p)
    (h : ((sectionComplex.{t, u} k B α).obj H).X j) :
    ((chain k B α P H).f (p + j)).hom
      (moduleTotalElement ((sectionComplex.{t, u} k B α).obj P)
        ((sectionComplex.{t, u} k B α).obj H) p j x h) =
      totalElement.{t, u} k B P H p j (op (finalObject k)) x h := by
  have hi : HomologicalComplex.ιMapBifunctor
      ((sectionComplex.{t, u} k B α).obj P)
      ((sectionComplex.{t, u} k B α).obj H) (curriedTensor _) (.up ℤ)
        p j (p + j) rfl ≫ (chain k B α P H).f (p + j) =
      component k B α (P.X p) (H.X j) ≫ (sections.{t, u} k B α).map
        (HomologicalComplex.ιMapBifunctor P H
          (IntegralHom.ordinaryTensor.{t, u} (Spec (.of k)) B) (.up ℤ)
          p j (p + j) rfl) := by
    dsimp only [chain, CategoryTheory.CochainPullback.laxTotalComponent]
    exact HomologicalComplex.ι_mapBifunctorDesc _ p j rfl
  exact congrArg (fun f ↦ f.hom (x ⊗ₜ[R] h)) hi

private def beta (H : CochainComplex (Modules.{t, u} k B) ℤ) :
    moduleTotal c ((sectionComplex.{t, u} k B α).obj H) ⟶
      (sectionComplex.{t, u} k B α).obj
        (total.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c) H) :=
  letI := adj.left_adjoint_additive
  HomologicalComplex.mapBifunctorMap
    ((adj.mapHomologicalComplex (.up ℤ)).unit.app c) (𝟙 _)
      (curriedTensor _) (.up ℤ) ≫ chain k B α _ H

private theorem beta_apply (hex : ExplicitAdjunction.{t, u} k B α L hobj adj)
    (H : CochainComplex (Modules.{t, u} k B) ℤ)
    (p j : ℤ) (x : c.X p) (h : ((sectionComplex.{t, u} k B α).obj H).X j) :
    ((beta k B α L adj c H).f (p + j)).hom
      (moduleTotalElement c ((sectionComplex.{t, u} k B α).obj H) p j x h) =
      totalElement.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c) H
        p j (op (finalObject k))
        (generator.{t, u} k B α L hobj (c.X p) (op (finalObject k)) 1 x) h := by
  let := adj.left_adjoint_additive
  have hu := hex.1 (c.X p) (L.obj (c.X p)) (𝟙 _) x
  rw [adj.homEquiv_id] at hu
  have hi := congrArg (fun f ↦ f.hom (x ⊗ₜ[R] h))
    (HomologicalComplex.ι_mapBifunctorMap
      ((adj.mapHomologicalComplex (.up ℤ)).unit.app c) (𝟙 _)
      (curriedTensor _) (.up ℤ) p j (p + j) rfl)
  simp only [Adjunction.mapHomologicalComplex_unit_app_f,
    HomologicalComplex.id_f] at hi
  change (((HomologicalComplex.mapBifunctorMap
    ((adj.mapHomologicalComplex (.up ℤ)).unit.app c) (𝟙 _)
      (curriedTensor _) (.up ℤ)).f (p + j)).hom
      (moduleTotalElement c ((sectionComplex.{t, u} k B α).obj H) p j x h)) =
        moduleTotalElement ((sectionComplex.{t, u} k B α).obj
          ((extensionComplex.{t, u} k B α L adj).obj c))
          ((sectionComplex.{t, u} k B α).obj H) p j ((adj.unit.app (c.X p)).hom x) h at hi
  dsimp only [beta, HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  erw [hi, chain_apply, hu]
  rfl

end SectionsTensorConstruction

/-- The ordinary signed sheaf evaluation and the sections-tensor map.
Source: Stacks Project, Tags 0A8X and 08J7
(blueprint: lem-pod-point-sheaf-hom-maps).

Proof: use the tensor-Hom counit, with the symmetry putting the argument before
Hom. Its component on degrees (p,j) is (-1)^(pj) times evaluation. The Hom
projection differential proves the chain identity, since the two h(dy) terms
cancel. The adjunction unit in degree p
is x mapped to 1 tensor x, by the explicit formula. Tensor it with a section h,
then apply the sheaf tensor unit and the inclusion of the (p,j) total summand.
This balanced R-bilinear map induces beta by the tensor and coproduct universal
properties. Naturality of the adjunction unit and the two tensor differentials
prove its chain identity. This uses maps into sections of a sum, never preservation
of infinite sums by sections. Both component formulas follow directly from
these constructions, also in negative degrees and for unbounded complexes.
No comparison q, exactness, flatness or injectivity is required. -/
theorem point_sheaf_hom_maps
    (hex : ExplicitAdjunction.{t, u} k B α L hobj adj)
    (I : CochainComplex (Modules.{t, u} k B) ℤ) :
  ∃ (eB : total.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c)
      (sheafHom.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c) I) ⟶ I)
    (beta : moduleTotal c ((sectionComplex.{t, u} k B α).obj
      (sheafHom.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c) I)) ⟶
        (sectionComplex.{t, u} k B α).obj (total.{t, u} k B
          ((extensionComplex.{t, u} k B α L adj).obj c)
          (sheafHom.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c) I))),
    (∀ (p j : ℤ) (U : (Scheme.ProEt (Spec (.of k)))ᵒᵖ)
      (y : (((extensionComplex.{t, u} k B α L adj).obj c).X p).val.obj U)
      (h : ((sheafHom.{t, u} k B
        ((extensionComplex.{t, u} k B α L adj).obj c) I).X j).val.obj U),
      (eB.f (p + j)).val.app U (totalElement.{t, u} k B
        ((extensionComplex.{t, u} k B α L adj).obj c)
        (sheafHom.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c) I) p j U y h) =
          (p * j).negOnePow • homValue.{t, u} k B
            ((extensionComplex.{t, u} k B α L adj).obj c) I j p U h y) ∧
    (∀ (p j : ℤ) (x : c.X p)
      (h : ((sectionComplex.{t, u} k B α).obj
        (sheafHom.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c) I)).X j),
      (beta.f (p + j)).hom (moduleTotalElement c
        ((sectionComplex.{t, u} k B α).obj
          (sheafHom.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c) I)) p j x h) =
        totalElement.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c)
          (sheafHom.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c) I)
          p j (op (finalObject k))
          (generator.{t, u} k B α L hobj (c.X p) (op (finalObject k)) 1 x) h) := by
  let P := (extensionComplex.{t, u} k B α L adj).obj c
  let H := sheafHom.{t, u} k B P I
  let eB : total.{t, u} k B P H ⟶ I :=
    { f := EvaluationConstruction.degree k B P I
      comm' := EvaluationConstruction.degree_comm k B P I }
  refine ⟨eB, SectionsTensorConstruction.beta k B α L adj c H, ?_, ?_⟩
  · exact EvaluationConstruction.degree_on_totalElement k B P I
  · exact SectionsTensorConstruction.beta_apply k B α L hobj adj c hex H

end WeilConjectures.PointDerivedHom
