/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Ringed.Slice.RingedSliceEvaluationModels
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import all WeilConjectures.CategoryTheory.Ringed.Tensor.RingedTensorConstraintCompletion
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement

/-! # Scalar-unit coherence of normalized slice tensor comparison

Source: Stacks Project, Tags 07A4 and 0FPT
(blueprint: lem-sfb-ringed-slice-scalar-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w w'
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open SheafOfModules WeilConjectures
namespace CategoryTheory
section TotalMapGeneric
universe a b
variable {A : Type a} [Category.{b} A] [Preadditive A]
  (G : A ⥤ A ⥤ A) [G.PreservesZeroMorphisms]
  [∀ X, (G.obj X).PreservesZeroMorphisms]
  [∀ P Q : CochainComplex A ℤ, HomologicalComplex.HasMapBifunctor P Q G (.up ℤ)]
private theorem total_map_generic
    {P P' Q Q' : CochainComplex A ℤ} (f : P ⟶ P') (g : Q ⟶ Q') :
    (Functor.uncurry.obj (G.map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ))).map
      (X := (P, Q)) (Y := (P', Q')) (Prod.mkHom f g) =
      HomologicalComplex.mapBifunctorMap f g G (.up ℤ) := by
  change HomologicalComplex.mapBifunctorMap f (𝟙 Q) G (.up ℤ) ≫
    HomologicalComplex.mapBifunctorMap (𝟙 P') g G (.up ℤ) = _
  simp only [HomologicalComplex.mapBifunctorMap, Functor.map_id, NatTrans.id_app,
    Category.id_comp, Category.comp_id, ← HomologicalComplex₂.total.map_comp]
end TotalMapGeneric
section Generic
universe a b x y
variable {D : Type a} [Category.{x} D] {E : Type b} [Category.{y} E]
  {H : Dᵒᵖ × D ⥤ D} {HU : Eᵒᵖ × E ⥤ E}
  (S : CoefficientClosedStructure H) (SU : CoefficientClosedStructure HU)
  {r : D ⥤ E} {K : Prop}
  (d : RingedSliceEvaluationComparisons H HU r S SU K)

private theorem scalar_of_models
    (P O X : D) (PU OU XU : E)
    (i : X ≅ S.tensor.obj (P, O)) (j : XU ≅ SU.tensor.obj (PU, OU))
    (aP : r.obj P ≅ PU) (aO : r.obj O ≅ OU) (c : r.obj X ≅ XU)
    (u : S.monoidal.tensorUnit ≅ O) (uU : SU.monoidal.tensorUnit ≅ OU)
    (b : X ⟶ P) (bU : XU ⟶ PU)
    (hr : r.map i.hom ≫ (d.rho P O).hom ≫
      SU.tensor.map (aP.hom, aO.hom) = c.hom ≫ j.hom)
    (hb : i.hom ≫ S.tensor.map (X := (P, O)) (Y := (P, S.monoidal.tensorUnit)) (𝟙 P, u.inv) ≫
      (S.monoidal.rightUnitor P).hom = b)
    (hbU : j.hom ≫ SU.tensor.map (X := (PU, OU))
      (Y := (PU, SU.monoidal.tensorUnit)) (𝟙 PU, uU.inv) ≫
      (SU.monoidal.rightUnitor PU).hom = bU)
    (hc : r.map b ≫ aP.hom = c.hom ≫ bU) :
    r.map (S.tensor.map (X := (P, O)) (Y := (P, S.monoidal.tensorUnit))
      (𝟙 P, u.inv) ≫ (S.monoidal.rightUnitor P).hom) =
      (d.rho P O).hom ≫ SU.tensor.map (X := (r.obj P, r.obj O))
        (Y := (r.obj P, OU)) (𝟙 (r.obj P), aO.hom) ≫
        SU.tensor.map (X := (r.obj P, OU))
          (Y := (r.obj P, SU.monoidal.tensorUnit)) (𝟙 (r.obj P), uU.inv) ≫
          (SU.monoidal.rightUnitor (r.obj P)).hom := by
  let := S.monoidal
  let := SU.monoidal
  apply (cancel_epi (r.map i.hom)).mp
  apply (cancel_mono aP.hom).mp
  simp only [Category.assoc, ← r.map_comp, hb]
  rw [hc, ← hbU]
  erw [← reassoc_of% hr]
  simp only [CoefficientClosedStructure.tensor, tensor_map,
    id_tensorHom]
  rw [← MonoidalCategory.rightUnitor_naturality]
  simp only [← id_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom_assoc,
    Category.comp_id, Category.id_comp]
private theorem scalar_of_iso :
    letI := S.monoidal
    letI := SU.monoidal
    ∀ (O : D) (OU : E) (u : 𝟙_ D ≅ O) (uU : 𝟙_ E ≅ OU) (o : r.obj O ≅ OU)
    {P N : D} (_e : P ≅ N)
    (_h : r.map ((𝟙 P ⊗ₘ u.inv) ≫ (ρ_ P).hom) =
      (d.rho P O).hom ≫ (𝟙 (r.obj P) ⊗ₘ o.hom) ≫
        (𝟙 (r.obj P) ⊗ₘ uU.inv) ≫ (ρ_ (r.obj P)).hom),
    r.map ((𝟙 N ⊗ₘ u.inv) ≫ (ρ_ N).hom) =
      (d.rho N O).hom ≫ (𝟙 (r.obj N) ⊗ₘ o.hom) ≫
        (𝟙 (r.obj N) ⊗ₘ uU.inv) ≫ (ρ_ (r.obj N)).hom := by
  let := S.monoidal
  let := SU.monoidal
  intro O OU u uU o P N e h
  have hz : IsIso (r.map (e.hom ⊗ₘ 𝟙 O)) := inferInstance
  apply (cancel_epi (r.map (e.hom ⊗ₘ 𝟙 O))).mp
  have hn := d.rho_naturality P O N O e.hom (𝟙 O)
  simp only [CoefficientClosedStructure.tensor, tensor_map, Functor.map_id] at hn
  have hact : (e.hom ⊗ₘ 𝟙 O) ≫ (𝟙 N ⊗ₘ u.inv) ≫ (ρ_ N).hom =
      (𝟙 P ⊗ₘ u.inv) ≫ (ρ_ P).hom ≫ e.hom := by
    simp only [tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]
    rw [← MonoidalCategory.rightUnitor_naturality]
    simp only [← tensorHom_id, tensorHom_comp_tensorHom_assoc,
      Category.id_comp, Category.comp_id]
  rw [← r.map_comp, hact]
  simp only [r.map_comp]
  erw [reassoc_of% hn]
  rw [Functor.map_comp] at h
  rw [← Category.assoc, h]
  simp only [Category.assoc]
  erw [← MonoidalCategory.rightUnitor_naturality]
  simp only [← tensorHom_id, tensorHom_comp_tensorHom_assoc,
    Category.id_comp, Category.comp_id]
end Generic
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J R)]
  (U : C)
  [HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasDerivedCategory.{w'} (RingedTensorModules.{max c v, v, r} (J.over U) (R.over U))]
  (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R))
  (T : CoefficientTensorModels.{r, c, v, w} J R S)
  (s : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, r} J R))
    _ S.monoidal)
  (K : RingedDerivedTensorCoherence.{c, v, r, w} J R S T s)
  (SU : CoefficientClosedStructure
    (derivedInternalHomOfUniverses.{max c v, v, r, w'} (J.over U) (R.over U)))
  (TU : CoefficientTensorModels.{r, max c v, v, w'} (J.over U) (R.over U) SU)
  (sU : @SymmetricCategory
    (DerivedCategory (RingedTensorModules.{max c v, v, r} (J.over U) (R.over U)))
    _ SU.monoidal)
  (KU : RingedDerivedTensorCoherence.{max c v, v, r, w'} (J.over U) (R.over U) SU TU sU)
  (d : RingedSliceEvaluationComparisons (derivedInternalHomOfUniverses.{c, v, r, w} J R)
    (derivedInternalHomOfUniverses.{max c v, v, r, w'} (J.over U) (R.over U))
    (ringedSliceDerivedRestriction.{c, v, r, w, w'} J R U) S SU
    (RingedSliceFlatRestriction.{c, v, r} J R U))
  (hd : RingedSliceEvaluationNormalized.{c, v, r, w, w'} J R U S T SU TU d)

omit [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J R)] in
private theorem tensorGenerator_map
    {P P' Q Q' : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') (p q k : ℤ) (hpq : p + q = k)
    (U : Cᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    (((coefficientTotalTensor.{r, c, v} J R).map
      (X := (P, Q)) (Y := (P', Q')) (Prod.mkHom f g)).f k).val.app U
      (coefficientTensorGenerator.{r, c, v} J R P Q p q k hpq U x y) =
    coefficientTensorGenerator.{r, c, v} J R P' Q' p q k hpq U
      ((f.f p).val.app U x) ((g.f q).val.app U y) := by
  subst k
  let := SheafOfModules.monoidalCategory R
  unfold coefficientTotalTensor
  rewrite [total_map_generic]
  have h := HomologicalComplex.ι_mapBifunctorMap f g
    (curriedTensor (RingedTensorModules.{c, v, r} J R)) (.up ℤ) p q (p + q) rfl
  simp only [curriedTensor_map_app, curriedTensor_obj_map] at h
  rw [← Category.assoc, ← tensorHom_def] at h
  have hh := congrArg (fun a ↦ a.val.app U
    (CochainPullback.moduleTmul (P.X p) (Q.X q) U x y)) h
  have hm := CochainPullback.moduleTmul_map (f.f p) (g.f q) U x y
  exact hh.trans (congrArg
    ((HomologicalComplex.ιMapBifunctor P' Q'
      (curriedTensor (RingedTensorModules.{c, v, r} J R)) (.up ℤ) p q (p + q) rfl).val.app U) hm)
omit [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J R)]
  [HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasDerivedCategory.{w'} (RingedTensorModules.{max c v, v, r} (J.over U) (R.over U))] in
private theorem unit_flat : ∀ n : ℤ,
    SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r} (J := J) (R := R)
      ((ringedTensorUnitComplex.{c, v, r} J R).X n) := by
  intro n
  by_cases hn : n = 0
  · subst n
    have h : ObjectProperty.flat (𝟙_ (RingedTensorModules.{c, v, r} J R)) :=
      ObjectProperty.flat_of_tensorIso
        (leftUnitor (𝟙_ (RingedTensorModules.{c, v, r} J R)))
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R _).symm h.2
  · have hz := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
      (SheafOfModules.unit ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) n hn
    have h : ObjectProperty.flat ((ringedTensorUnitComplex.{c, v, r} J R).X n) :=
      ObjectProperty.flat_of_isZero hz
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R _).symm h.2

omit [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J R)]
  [HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasDerivedCategory.{w'} (RingedTensorModules.{max c v, v, r} (J.over U) (R.over U))] in
private theorem unit_kflat :
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R)
      (ringedTensorUnitComplex.{c, v, r} J R) := by
  have : (ringedTensorUnitComplex.{c, v, r} J R).IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ n (by omega)
  exact SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
    R (ringedTensorUnitComplex.{c, v, r} J R) 0 (unit_flat.{c, v, r} J R)

omit [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J R)] in
private theorem total_hom_ext
    (P Q Z : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (φ ψ : (coefficientTotalTensor.{r, c, v} J R).obj (P, Q) ⟶ Z)
    (h : ∀ (k p q : ℤ) (hpq : p + q = k),
      HomologicalComplex.ιMapBifunctor P Q
        (curriedTensor (RingedTensorModules.{c, v, r} J R)) (.up ℤ) p q k hpq ≫ φ.f k =
      HomologicalComplex.ιMapBifunctor P Q
        (curriedTensor (RingedTensorModules.{c, v, r} J R)) (.up ℤ) p q k hpq ≫ ψ.f k) :
    φ = ψ := by
  apply HomologicalComplex.hom_ext
  intro k
  apply HomologicalComplex.mapBifunctor.hom_ext
    (K₁ := P) (K₂ := Q)
    (F := curriedTensor (RingedTensorModules.{c, v, r} J R)) (c := .up ℤ)
  intro p q hpq
  exact h k p q hpq

attribute [local irreducible] coefficientTotalTensor ringedSliceDerivedRestriction

-- Keep the representative scalar square at its normalized endpoints.
include hd in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Scalar action is preserved by the normalized slice tensor comparison, using the
coefficient identification furnished by termwise restriction and localization.
Source: Stacks Tags 03DJ, 07A4 and 0FPT
(blueprint: lem-sfb-ringed-slice-scalar-unit).

Proof: restriction of the coefficient complex is the coefficient complex on the slice.
Use this identification and the localization comparison for the coefficient isomorphism.
On a flat-term K-flat representative, compare scalar multiplication with the tensor
restriction square. Both chain maps send a pure tensor x tensor a to a times x.
The normalized unit constraints therefore give the desired square after localization.
Naturality of tensor comparison and of the unit constraints transports it along a
flat-term K-flat resolution to every derived object. -/
theorem ringedSlice_scalar_unit :
    let r := ringedSliceDerivedRestriction.{c, v, r, w, w'} J R U
    let O := DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, r} J R)
    let OU := DerivedCategory.Q.obj
      (ringedTensorUnitComplex.{max c v, v, r} (J.over U) (R.over U))
    ∃ o : r.obj O ≅ OU, ∀ N,
      r.map (S.tensor.map (X := (N, O)) (Y := (N, S.monoidal.tensorUnit))
        (𝟙 N, K.unitIso.inv) ≫ (S.monoidal.rightUnitor N).hom) =
        (d.rho N O).hom ≫ SU.tensor.map
          (X := (r.obj N, r.obj O)) (Y := (r.obj N, OU)) (𝟙 (r.obj N), o.hom) ≫
          SU.tensor.map (X := (r.obj N, OU))
            (Y := (r.obj N, SU.monoidal.tensorUnit)) (𝟙 (r.obj N), KU.unitIso.inv) ≫
              (SU.monoidal.rightUnitor (r.obj N)).hom := by
  let F := ringedSliceComplexRestriction.{c, v, r} J R U
  let O := ringedTensorUnitComplex.{c, v, r} J R
  let OU := ringedTensorUnitComplex.{max c v, v, r} (J.over U) (R.over U)
  let B := ((sheafCompose J
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)
  let := (ringedOverFunctor_exactGeneral.{c, v, max c v r, max c v r} B U).1
  let e : F.obj O ≅ OU :=
    (HomologicalComplex.singleMapHomologicalComplex
      (SheafOfModules.overFunctor.{max c v r} B U) (.up ℤ) (0 : ℤ)).app
        (SheafOfModules.unit B)
  let o := (ringedSliceLocalizationIso.{c, v, r, w, w'} J R U).app O ≪≫
    DerivedCategory.Q.mapIso e
  let r := ringedSliceDerivedRestriction.{c, v, r, w, w'} J R U
  have base (P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
      (fP : ∀ n, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
        (J := J) (R := R) (P.X n)) :
      r.map (S.tensor.map (X := (DerivedCategory.Q.obj P, DerivedCategory.Q.obj O))
          (Y := (DerivedCategory.Q.obj P, S.monoidal.tensorUnit))
          (𝟙 _, K.unitIso.inv) ≫
            (S.monoidal.rightUnitor (DerivedCategory.Q.obj P)).hom) =
        (d.rho (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj O)).hom ≫
          SU.tensor.map (X := (r.obj (DerivedCategory.Q.obj P), r.obj (DerivedCategory.Q.obj O)))
            (Y := (r.obj (DerivedCategory.Q.obj P), DerivedCategory.Q.obj OU))
            (𝟙 _, o.hom) ≫ SU.tensor.map
              (X := (r.obj (DerivedCategory.Q.obj P), DerivedCategory.Q.obj OU))
              (Y := (r.obj (DerivedCategory.Q.obj P), SU.monoidal.tensorUnit))
              (𝟙 _, KU.unitIso.inv) ≫
                (SU.monoidal.rightUnitor (r.obj (DerivedCategory.Q.obj P))).hom := by
    obtain ⟨γ, hγ, hρ⟩ := hd.1 P O hP (unit_kflat.{c, v, r} J R) fP (unit_flat.{c, v, r} J R)
    obtain ⟨β, hβ, heβ⟩ := K.rightUnitor_model P hP
    obtain ⟨βU, hβU, heβU⟩ := KU.rightUnitor_model (F.obj P) (d.kflat P hP fP).1
    rw [K.tensorIso_both P O hP (unit_kflat.{c, v, r} J R)] at heβ
    have hchain : F.map β.hom = γ.hom ≫
        (coefficientTotalTensor.{r, max c v, v} (J.over U) (R.over U)).map
          (𝟙 (F.obj P), e.hom) ≫ βU.hom := by
      apply (cancel_epi γ.inv).mp
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      apply total_hom_ext.{max c v, v, r} (J.over U) (R.over U)
      intro k p q hpq
      by_cases hq : q = 0
      · subst q
        have hk : k = p := by omega
        subst hk
        apply pure_ext.{max c v, v, r} (J.over U) (R.over U)
          ((F.obj P).X k) ((F.obj O).X 0) ((F.obj P).X k)
        intro V x a
        have hi : (γ.inv.f k).val.app V
            (coefficientTensorGenerator.{r, max c v, v} (J.over U) (R.over U)
              (F.obj P) (F.obj O) k 0 k (Int.add_zero k) V x a) =
            coefficientTensorGenerator.{r, c, v} J R P O k 0 k
              (Int.add_zero k) (op V.unop.left) x a := by
          have h := congrArg ((γ.inv.f k).val.app V)
            (hγ k 0 k (Int.add_zero k) V.unop x a)
          have h' := congrArg (fun f ↦ (f.f k).val.app V
            (coefficientTensorGenerator.{r, c, v} J R P O k 0 k
              (Int.add_zero k) (op V.unop.left) x a)) γ.hom_inv_id
          set_option backward.isDefEq.respectTransparency false in
           simpa only [HomologicalComplex.comp_f, SheafOfModules.comp_val,
            PresheafOfModules.comp_app, ModuleCat.comp_apply,
            HomologicalComplex.id_f, SheafOfModules.id_val, PresheafOfModules.id_app,
            ModuleCat.id_apply] using h.symm.trans h'
        change (β.hom.f k).val.app (op V.unop.left)
            ((γ.inv.f k).val.app V
              (coefficientTensorGenerator.{r, max c v, v} (J.over U) (R.over U)
                (F.obj P) (F.obj O) k 0 k (Int.add_zero k) V x a)) = _
        -- Apply both scalar formulas before asking Lean to check reflexivity.
        rewrite [hi]
        let b : R.obj.obj (op V.unop.left) := (HomologicalComplex.singleObjXSelf (.up ℤ) 0
          (SheafOfModules.unit B)).hom.val.app (op V.unop.left) a
        have ha : ringedTensorUnitSection.{c, v, r} J R (op V.unop.left) b = a := by
          have hh := congrArg (fun f ↦ f.val.app (op V.unop.left) a)
            (HomologicalComplex.singleObjXSelf (.up ℤ) 0
              (SheafOfModules.unit B)).hom_inv_id
          exact hh
        rewrite [← ha, hβ k (Int.add_zero k) (op V.unop.left) b x]
        set_option backward.isDefEq.respectTransparency.types false in
        set_option backward.isDefEq.respectTransparency false in
         change b • x = (βU.hom.f k).val.app V
          ((((coefficientTotalTensor.{r, max c v, v} (J.over U) (R.over U)).map
            (𝟙 (F.obj P), e.hom)).f k).val.app V
              (coefficientTensorGenerator.{r, max c v, v} (J.over U) (R.over U)
                (F.obj P) (F.obj O) k 0 k (Int.add_zero k) V x
                (ringedTensorUnitSection.{c, v, r} J R (op V.unop.left) b)))
        rewrite [tensorGenerator_map]
        simp only [HomologicalComplex.id_f, SheafOfModules.id_val,
          PresheafOfModules.id_app, ModuleCat.id_apply]
        have he : (e.hom.f 0).val.app V
            (ringedTensorUnitSection.{c, v, r} J R (op V.unop.left) b) =
              ringedTensorUnitSection.{max c v, v, r} (J.over U) (R.over U) V b := by
          rfl
        rewrite [he, hβU]
        set_option backward.isDefEq.respectTransparency.types false in
        set_option backward.isDefEq.respectTransparency false in
         rfl
      · apply IsZero.eq_of_src
        apply (tensorLeft ((F.obj P).X p)).map_isZero
        exact (SheafOfModules.overFunctor.{max c v r} B U).map_isZero
          (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ q hq)
    let α := ringedSliceLocalizationIso.{c, v, r, w, w'} J R U
    have hPU := (d.kflat P hP fP).1
    have hOU := unit_kflat.{max c v, v, r} (J.over U) (R.over U)
    rw [KU.tensorIso_both _ _ hPU hOU] at heβU
    let c := α.app ((coefficientTotalTensor.{r, c, v} J R).obj (P, O)) ≪≫
      DerivedCategory.Q.mapIso γ ≪≫ DerivedCategory.Q.mapIso
        ((coefficientTotalTensor.{r, max c v, v} (J.over U) (R.over U)).mapIso
          ((Iso.refl (F.obj P)).prod e))
    apply scalar_of_models S SU d _ _ _ _ _ _
      (T.iso J R S P O hP (unit_kflat.{c, v, r} J R))
      (TU.iso (J.over U) (R.over U) SU (F.obj P) OU hPU hOU)
      (α.app P) o c K.unitIso KU.unitIso
      (DerivedCategory.Q.map β.hom) (DerivedCategory.Q.map βU.hom)
      (by
        have hn := KU.tensorIso_naturality (F.obj P) (F.obj O) (F.obj P) OU
          (Or.inl hPU) (Or.inl hPU) (𝟙 (F.obj P)) e.hom
        conv at hn =>
          lhs
          arg 2
          rw [KU.tensorIso_both (F.obj P) OU hPU hOU]
        conv at hn =>
          rhs
          arg 1
          rw [KU.tensorIso_both (F.obj P) (F.obj O) hPU (d.kflat O
            (unit_kflat.{c, v, r} J R) (unit_flat.{c, v, r} J R)).1]
        simp only [Functor.map_id] at hn
        dsimp only [c, o, Iso.trans_hom, Functor.mapIso_hom]
        simp only [Category.assoc]
        simp only [Iso.prod_hom, Iso.refl_hom, Prod.mkHom]
        conv =>
          rhs
          arg 2
          arg 2
          rw [hn]
        have hh := congrArg (fun f ↦ f ≫ SU.tensor.map
          (X := (DerivedCategory.Q.obj (F.obj P), DerivedCategory.Q.obj (F.obj O)))
          (Y := (DerivedCategory.Q.obj (F.obj P), DerivedCategory.Q.obj OU))
          (𝟙 _, DerivedCategory.Q.map e.hom)) hρ
        set_option backward.isDefEq.respectTransparency.types false in
        set_option backward.isDefEq.respectTransparency false in
         simpa only [F, Category.assoc, ← SU.tensor.map_comp, prod_comp, Prod.mkHom,
          Category.id_comp, Category.comp_id, Iso.app_hom, Iso.trans_hom,
          Functor.mapIso_hom, α] using hh) heβ heβU
    dsimp only [c, Iso.trans_hom, Functor.mapIso_hom]
    simp only [Category.assoc]
    have hh := α.hom.naturality β.hom
    simp only [Functor.comp_map] at hh
    change r.map (DerivedCategory.Q.map β.hom) ≫ (α.app P).hom = _ at hh
    rewrite [hh, hchain, DerivedCategory.Q.map_comp, DerivedCategory.Q.map_comp]
    rfl
  refine ⟨o, ?_⟩
  intro N
  classical
  obtain ⟨P, f, hP, fP, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R)
      (DerivedCategory.Q.objPreimage N)
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hf
  let eP := asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso N
  apply scalar_of_iso S SU d _ _ K.unitIso KU.unitIso o eP
  apply base P hP
  intro n
  exact (exactFunctor _ _).prop_of_iso
    (siteSheafTensorRightIso R (P.X n)).symm (fP n)

end CategoryTheory
