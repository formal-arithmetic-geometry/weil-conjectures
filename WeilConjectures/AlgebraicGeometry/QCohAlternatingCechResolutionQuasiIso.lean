/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechTotalComplex
public import WeilConjectures.AlgebraicGeometry.Coherent
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import WeilConjectures.AlgebraicGeometry.AffineOpenSectionsResolutionQuasiIso
import Mathlib.Algebra.Category.ModuleCat.Products
import WeilConjectures.Algebra.Homology.KInjectiveRestrictOpen
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.QCohAcyclicDerivedSectionsComparison

/-! # Čech totalization of a quasi-coherent resolution

Source: Stacks Project, Cohomology, Lemma 08C2.
(blueprint: lem-sc-qcoh-alternating-cech-resolution-quasi-iso)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private def alternatingCechTermsProjection
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens)
    (G : X.Opensᵒᵖ ⥤ ModuleCat.{u}
      ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
    (k : ℕ) (t : Fin (k + 1) ↪o Fin r) :
    alternatingCechTerms U G k ⟶ G.obj (op (alternatingCechIntersection U t)) :=
  ModuleCat.ofHom (LinearMap.proj t)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def alternatingCechColumnProjection
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens)
    (F : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (k : ℕ) (t : Fin (k + 1) ↪o Fin r) :
    (((alternatingCechDoubleFunctor U).obj F).X (k : ℤ)) ⟶
      (((alternatingCechModulePresheaf (X := X) ⋙
        (CategoryTheory.evaluation X.Opensᵒᵖ
          (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))).obj
            (op (alternatingCechIntersection U t))).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj F) where
  f n := (HomologicalComplex.extendXIso
      (alternatingCechComplex U ((alternatingCechModulePresheaf (X := X)).obj (F.X n)))
        ComplexShape.embeddingUpNat (i := k) rfl).hom ≫
    alternatingCechTermsProjection U
      ((alternatingCechModulePresheaf (X := X)).obj (F.X n)) k t
  comm' n m _ := by
    change _ = (HomologicalComplex.extendMap
      (alternatingCechComplexMap U ((alternatingCechModulePresheaf (X := X)).map
        (F.d n m))) ComplexShape.embeddingUpNat).f (k : ℤ) ≫ _
    erw [HomologicalComplex.extendMap_f _ _ (i := k) rfl]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem alternatingCechColumnProjection_isIso
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens)
    (F : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (k : ℕ) :
    IsIso (Limits.Pi.lift (alternatingCechColumnProjection U F k)) := by
  classical
  suffices h : ∀ n, IsIso ((Limits.Pi.lift
      (alternatingCechColumnProjection U F k)).f n) from
    by
      have := h
      exact HomologicalComplex.Hom.isIso_of_components _
  intro n
  let C := ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))
  let E := HomologicalComplex.eval C (ComplexShape.up ℤ) n
  let P := fun t : Fin (k + 1) ↪o Fin r ↦
    (((alternatingCechModulePresheaf (X := X) ⋙
      (CategoryTheory.evaluation X.Opensᵒᵖ C).obj
        (op (alternatingCechIntersection U t))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj F)
  let e := HomologicalComplex.extendXIso
    (alternatingCechComplex U ((alternatingCechModulePresheaf (X := X)).obj (F.X n)))
      ComplexShape.embeddingUpNat (i := k) rfl
  have he : (Limits.Pi.lift (alternatingCechColumnProjection U F k)).f n ≫
      piComparison E P = e.hom ≫ (ModuleCat.piIsoPi (fun t ↦ (P t).X n)).inv := by
    apply Limits.Pi.hom_ext
    intro t
    simp only [Category.assoc, piComparison_comp_π]
    change ((Limits.Pi.lift (alternatingCechColumnProjection U F k)) ≫
      Limits.Pi.π P t).f n = _
    rw [Limits.Pi.lift_π]
    erw [ModuleCat.piIsoPi_inv_kernel_ι]
    rfl
  have : IsIso ((Limits.Pi.lift (alternatingCechColumnProjection U F k)).f n ≫
      piComparison E P) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (piComparison E P)

set_option backward.isDefEq.respectTransparency false in
private theorem alternatingCechDouble_isZero_column
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens)
    (F : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (p : ℤ) (hp : p < 0 ∨ (r : ℤ) ≤ p) :
    IsZero (((alternatingCechDoubleFunctor U).obj F).X p) := by
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex.hom_ext
  intro n
  apply (show IsZero ((((alternatingCechDoubleFunctor U).obj F).X p).X n) from ?_).eq_of_src
  change IsZero (((alternatingCechModuleFunctor U).obj (F.X n)).X p)
  change IsZero (((alternatingCechComplex U
    ((alternatingCechModulePresheaf (X := X)).obj (F.X n))).extend
      ComplexShape.embeddingUpNat).X p)
  rcases hp with hp | hp
  · apply HomologicalComplex.isZero_extend_X
    intro k
    change (k : ℤ) ≠ p
    omega
  · have hnonneg : 0 ≤ p := le_trans (by omega) hp
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hnonneg
    apply IsZero.of_iso _ (HomologicalComplex.extendXIso _
      ComplexShape.embeddingUpNat (i := k) rfl)
    change IsZero (alternatingCechTerms U
      ((alternatingCechModulePresheaf (X := X)).obj (F.X n)) k)
    have : IsEmpty (Fin (k + 1) ↪o Fin r) := ⟨fun t ↦ by
      have ht := Fintype.card_le_of_injective t t.injective
      simp only [Fintype.card_fin] at ht
      omega⟩
    unfold alternatingCechTerms
    exact ModuleCat.isZero_of_subsingleton _

set_option backward.isDefEq.respectTransparency false in
private theorem alternatingCechDouble_strictlyGE
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens)
    (F : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    CochainComplex.IsStrictlyGE ((alternatingCechDoubleFunctor U).obj F) 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro p hp
  exact alternatingCechDouble_isZero_column U F p (Or.inl hp)

set_option backward.isDefEq.respectTransparency false in
private theorem alternatingCechDouble_strictlyLE
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens)
    (F : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    CochainComplex.IsStrictlyLE ((alternatingCechDoubleFunctor U).obj F) ((r : ℤ) - 1) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro p hp
  exact alternatingCechDouble_isZero_column U F p (Or.inr (by omega))

end AlgebraicGeometry
