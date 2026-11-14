/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainData
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Homology.KFlatClosure
import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import WeilConjectures.Algebra.Homology.Picard.AdditiveAdjunctionConeSquare
import WeilConjectures.AlgebraicGeometry.Picard.KFlatPullbackAdjunctionComparison

/-! # Derived transposition of a specified cone square -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 2048 in
private theorem replacement (S : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (A B : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ)
    (t : A ⟶ B) :
    ∃ (P Q : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ)
      (p : P ⟶ Q) (x : P ⟶ A) (y : Q ⟶ B) (_h : p ≫ y = x ≫ t),
      P.IsAcyclicTensorKFlat ∧ Q.IsAcyclicTensorKFlat ∧ QuasiIso x ∧ QuasiIso y := by
  classical
  let E := SheafOfModules.{u} (moduleRings S.toRingedSpace)
  let := SheafOfModules.monoidalCategory S.sheaf
  let := SheafOfModules.symmetricCategory S.sheaf
  have : MonoidalPreadditive E := Classical.choice (SheafOfModules.tensorClosed S.sheaf).1
  let : MonoidalClosed E := Classical.choice (SheafOfModules.tensorClosed S.sheaf).2.1
  have : IsGrothendieckAbelian.{u} E := SheafOfModules.isGrothendieckAbelian _
  have : HasColimitsOfSize.{0, 0} E := hasColimitsOfSizeShrink.{0, 0, u, u} E
  have := schemeModule_hasFunctorialFlatResolution S
  have (M : E) : PreservesColimitsOfShape ℤ
      ((MonoidalCategory.curriedTensor E).flip.obj M) :=
    preservesColimitsOfShape_of_natIso (F := MonoidalCategory.tensorLeft M)
      (NatIso.ofComponents (fun N ↦ β_ M N) (by intros; simp [MonoidalCategory.curriedTensor]))
  let Λ := (inferInstance : Abelian.HasFunctorialFlatResolution E).some.reduced
  let R := Λ.kFlatResolutionFunctor ObjectProperty.flat.essImage_ι_le
  let ε := Λ.kFlatResolutionNatTrans ObjectProperty.flat.essImage_ι_le
  have toLean (K : CochainComplex.KFlat E) :
      CochainComplex.IsAcyclicTensorKFlat (R := S.sheaf) K.obj := by
    have h := (HomotopyCategory.kFlat_quotient_obj_iff K.obj).2 K.property
    rw [HomotopyCategory.kFlat_iff_preserves_acyclic] at h
    intro N hN
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1
      ((h ((HomotopyCategory.quotient E (.up ℤ)).obj N)
        ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic N).2 hN)).2)
  refine ⟨(R.obj A).obj, (R.obj B).obj, (R.map t).hom, ε.app A, ε.app B,
    ε.naturality t, toLean _, toLean _, ?_, ?_⟩
  · infer_instance
  · infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 2048 in
private theorem cone_precompose
    {E : Type*} [Category E] [Preadditive E] [HasBinaryBiproducts E]
    {P Q A B A' B' : CochainComplex E ℤ}
    (p : P ⟶ Q) (t : A ⟶ B) (t' : A' ⟶ B')
    (x : P ⟶ A) (y : Q ⟶ B) (h : p ≫ y = x ≫ t)
    (α : A ⟶ A') (β : B ⟶ B') (H : Homotopy (t ≫ β) (α ≫ t')) :
    ∃ H₀ : Homotopy (p ≫ (y ≫ β)) ((x ≫ α) ≫ t'),
      CochainComplex.mappingCone.mapOfHomotopy H₀ =
        CochainComplex.mappingCone.map p t x y h ≫
          CochainComplex.mappingCone.mapOfHomotopy H := by
  let H₀ : Homotopy (p ≫ (y ≫ β)) ((x ≫ α) ≫ t') :=
    (Homotopy.ofEq (by rw [← Category.assoc, h, Category.assoc])).trans
      ((H.compLeft x).trans (Homotopy.ofEq (Category.assoc x α t').symm))
  refine ⟨H₀, ?_⟩
  apply HomologicalComplex.Hom.ext
  funext n
  apply (CochainComplex.mappingCone.ext_from_iff p (n + 1) n rfl _ _).2
  constructor
  · simp [CochainComplex.mappingCone.mapOfHomotopy, CochainComplex.mappingCone.map,
      CochainComplex.HomComplex.Cochain.equivHomotopy, H₀, Homotopy.trans,
      Homotopy.ofEq, Homotopy.compLeft, Category.assoc,
      CochainComplex.HomComplex.Cochain.ofHomotopy]
  · simp [CochainComplex.mappingCone.mapOfHomotopy, CochainComplex.mappingCone.map,
      Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 2048 in
set_option maxHeartbeats 800000 in
-- The functorial flat resolution and the concrete sheaf adjunction need more heartbeats.
/-- Transpose a specified cone-square through derived pullback/direct image.
This is independent of open covers and of base-change comparison maps.
Source: Stacks Project, Cohomology, Tags 06YI and 06YJ (K-flat computations),
079W (derived adjunction), and Derived Categories, Tag 014P (cone formulas). -/
theorem derivedPullback_cone_square_transposition
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {S S' : Scheme.{u}} (g : S' ⟶ S)
    (A B : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ)
    (A' B' : CochainComplex (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) ℤ)
    (t : A ⟶ B) (t' : A' ⟶ B') :
    let G := RingedSpace.moduleDirectImage g.toLRSHom.toShHom
    let F := G.mapHomologicalComplex (.up ℤ)
    let η := schemeMVDirectImageLocalization g
    let adj := relativeMVAdj g
    ∀ (α : A ⟶ F.obj A') (β : B ⟶ F.obj B')
      (H : Homotopy (t ≫ β) (α ≫ F.map t')),
    ∃ (C D : CochainComplex
        (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) ℤ)
      (s : C ⟶ D) (a : C ⟶ A') (b : D ⟶ B')
      (H' : Homotopy (s ≫ b) (a ≫ t'))
      (d₁ : DerivedCategory.Q.obj C ≅ (derivedPullback g).obj (DerivedCategory.Q.obj A))
      (d₂ : DerivedCategory.Q.obj D ≅ (derivedPullback g).obj (DerivedCategory.Q.obj B))
      (d₃ : DerivedCategory.Q.obj (CochainComplex.mappingCone s) ≅
        (derivedPullback g).obj (DerivedCategory.Q.obj (CochainComplex.mappingCone t))),
      DerivedCategory.Q.map a =
        d₁.hom ≫ (adj.homEquiv _ _).symm (DerivedCategory.Q.map α ≫ η.app A') ∧
      DerivedCategory.Q.map b =
        d₂.hom ≫ (adj.homEquiv _ _).symm (DerivedCategory.Q.map β ≫ η.app B') ∧
      DerivedCategory.Q.map (CochainComplex.mappingCone.mapOfHomotopy H') =
        d₃.hom ≫ (adj.homEquiv _ _).symm
          (DerivedCategory.Q.map (CochainComplex.mappingCone.mapOfHomotopy H ≫
            (CochainComplex.mappingCone.mapHomologicalComplexIso t' G).inv) ≫
              η.app (CochainComplex.mappingCone t')) := by
  classical
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf, moduleRings] at *
  intro α β H
  obtain ⟨hL, e, he⟩ := kFlat_pullback_adjunction_comparison g
  let E : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings S'.toRingedSpace) := Scheme.Modules.tensorPullback g
  let G := RingedSpace.moduleDirectImage g.toLRSHom.toShHom
  let L := E.mapHomologicalComplex (.up ℤ)
  let F := G.mapHomologicalComplex (.up ℤ)
  let adj₀ : E ⊣ G := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)
  let ac := adj₀.mapHomologicalComplex (.up ℤ)
  obtain ⟨P, Q, p, x, y, hc, hP, hQ, hx, hy⟩ := replacement S A B t
  obtain ⟨H₀, hcone⟩ := cone_precompose p t (F.map t') x y hc α β H
  obtain ⟨H', htrans⟩ := CochainComplex.additiveAdjunction_cone_square
    adj₀ p t' (x ≫ α) (y ≫ β) H₀
  let c := CochainComplex.mappingCone.map p t x y hc
  have : IsIso (DerivedCategory.Q.map x) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ x).2 hx
  have : IsIso (DerivedCategory.Q.map y) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ y).2 hy
  have : IsIso (DerivedCategory.Q.map c) := by
    let m := DerivedCategory.Q.mapTriangle.map
      (CochainComplex.mappingCone.triangleMap p t x y hc)
    have h₁ : IsIso m.hom₁ := by
      change IsIso (DerivedCategory.Q.map x)
      infer_instance
    have h₂ : IsIso m.hom₂ := by
      change IsIso (DerivedCategory.Q.map y)
      infer_instance
    exact CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂ m
      (DerivedCategory.mappingCone_triangle_distinguished p)
      (DerivedCategory.mappingCone_triangle_distinguished t) h₁ h₂
  have hconeP := CochainComplex.isKFlat_mappingCone p hP hQ
  refine ⟨L.obj P, L.obj Q, L.map p, (ac.homEquiv _ _).symm (x ≫ α),
    (ac.homEquiv _ _).symm (y ≫ β), H',
    e P hP ≪≫ (derivedPullback g).mapIso (asIso (DerivedCategory.Q.map x)),
    e Q hQ ≪≫ (derivedPullback g).mapIso (asIso (DerivedCategory.Q.map y)),
    DerivedCategory.Q.mapIso (CochainComplex.mappingCone.mapHomologicalComplexIso p E).symm ≪≫
      e _ hconeP ≪≫ (derivedPullback g).mapIso (asIso (DerivedCategory.Q.map c)), ?_, ?_, ?_⟩
  · have hh := he P hP A' (x ≫ α)
    simp only [Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Functor.map_comp,
      Adjunction.homEquiv_naturality_left_symm, Category.assoc, ac, adj₀, E, L] at hh ⊢
    convert hh using 2
  · have hh := he Q hQ B' (y ≫ β)
    simp only [Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Functor.map_comp,
      Adjunction.homEquiv_naturality_left_symm, Category.assoc, ac, adj₀, E, L] at hh ⊢
    convert hh using 2
  · rw [htrans, Functor.map_comp]
    have h := he _ hconeP (CochainComplex.mappingCone t')
      (CochainComplex.mappingCone.mapOfHomotopy H₀ ≫
        (CochainComplex.mappingCone.mapHomologicalComplexIso t' G).inv)
    rw [hcone] at h
    rw [hcone]
    have hh := congrArg (fun k ↦ DerivedCategory.Q.map
      (CochainComplex.mappingCone.mapHomologicalComplexIso p E).inv ≫ k) h
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_hom,
      Functor.map_comp, Adjunction.homEquiv_naturality_left_symm, Category.assoc,
      adj₀, E, L, c, F, G] at hh ⊢
    convert hh using 2

end AlgebraicGeometry
