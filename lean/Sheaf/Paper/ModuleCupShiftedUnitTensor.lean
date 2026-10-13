/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.Paper.ModuleCupHomologyRepresentability
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import Sheaf.Paper.ModuleCupShiftedUnitChainTensor
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidalComp

/-! # The normalized tensor of shifted free rank-one modules

Source: Stacks Project, Tag 068G, the tensor-of-cocycles construction.
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

variable (k : Type u) [CommRing k] [HasDerivedCategory.{u} (ModuleCat.{u} k)]

private lemma cup_flat_comparison (P L : CochainComplex (ModuleCat.{u} k) ℤ)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} k) (.up ℤ)).kFlat P) :
    (DerivedCategory.QObjTensorQObjIsoOfKFlatLeft P L hP).hom =
      Functor.LaxMonoidal.μ DerivedCategory.Q P L := by
  simp only [DerivedCategory.QObjTensorQObjIsoOfKFlatLeft, Iso.trans_hom,
    tensorIso_hom, Iso.app_hom, Iso.symm_hom, asIso_hom, Functor.mapIso_hom]
  change _ = ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} k)).inv.app P ⊗ₘ
    (DerivedCategory.quotientCompQhIso (ModuleCat.{u} k)).inv.app L) ≫
    (Functor.LaxMonoidal.μ DerivedCategory.Qh
      ((HomotopyCategory.quotient (ModuleCat.{u} k) (.up ℤ)).obj P)
      ((HomotopyCategory.quotient (ModuleCat.{u} k) (.up ℤ)).obj L) ≫
      DerivedCategory.Qh.map
        (Functor.LaxMonoidal.μ (HomotopyCategory.quotient (ModuleCat.{u} k) (.up ℤ))
          P L)) ≫ (DerivedCategory.quotientCompQhIso (ModuleCat.{u} k)).hom.app (P ⊗ L)
  simp only [Category.assoc, Functor.Monoidal.μIso_hom]
  rfl

/-- The shifted-unit tensor identification with its representative formula.
Source: Stacks Project, Tag 068G, equation-simple-tor-product and its construction;
Tag 0FKU, the localization comparison for tensor products.
(blueprint: lem-sc-module-cup-shifted-unit-tensor)
Proof: the tensor of the two single free complexes is zero outside degree p+q.
In that degree use k tensor k = k, with inverse taking 1 to 1 tensor 1, to construct
an isomorphism from the single free complex in degree p+q. Both single complexes
are K-flat, so the lax localization comparison on them is invertible. Compose Q
of the complex isomorphism with its inverse to obtain e. For maps f and g into
arbitrary complexes K and L, let h be the complex isomorphism followed by f tensor g.
The degree p+q component of h sends 1 to the displayed tensor summand. Naturality
of the lax tensor comparison gives the displayed derived-morphism equation, since
the comparison on the single complexes cancels with its inverse. Hence if f and g
represent cycles, h represents their tensor cycle, without any additional sign.
This argument includes p=0, q=0, negative degrees, the zero ring and zero maps;
no flatness of K or L is needed. -/
theorem exists_cupShiftedUnitTensor (p q : ℤ) :
    ∃ e : DerivedCategory.Q.obj (cupSingleModule k (p + q)) ≅
      DerivedCategory.Q.obj (cupSingleModule k p) ⊗
        DerivedCategory.Q.obj (cupSingleModule k q),
    ∀ (K L : CochainComplex (ModuleCat.{u} k) ℤ)
      (f : cupSingleModule k p ⟶ K) (g : cupSingleModule k q ⟶ L),
    ∃ h : cupSingleModule k (p + q) ⟶ K ⊗ L,
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (p + q)
          (ModuleCat.of k k)).inv ≫ h.f (p + q)) (1 : k) =
        (HomologicalComplex.ιTensorObj K L p q (p + q) rfl)
          ((((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) p
              (ModuleCat.of k k)).inv ≫ f.f p) (1 : k)) ⊗ₜ[k]
            (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q
              (ModuleCat.of k k)).inv ≫ g.f q) (1 : k))) ∧
      e.hom ≫ (DerivedCategory.Q.map f ⊗ₘ DerivedCategory.Q.map g) ≫
          Functor.LaxMonoidal.μ DerivedCategory.Q K L = DerivedCategory.Q.map h := by
  obtain ⟨i, hi⟩ := exists_cupShiftedUnitChainTensor k p q
  have hP : (HomologicalComplex.quasiIso (ModuleCat.{u} k) (.up ℤ)).kFlat
      (cupSingleModule k p) :=
    (CochainComplex.kFlat_single_obj_iff_flat (ModuleCat.of k k) p).2
      ((ModuleCat.flat_iff_flat _).2 inferInstance)
  let c := DerivedCategory.QObjTensorQObjIsoOfKFlatLeft
    (cupSingleModule k p) (cupSingleModule k q) hP
  refine ⟨DerivedCategory.Q.mapIso i ≪≫ c.symm, ?_⟩
  intro K L f g
  refine ⟨i.hom ≫ (f ⊗ₘ g), ?_, ?_⟩
  · change (f ⊗ₘ g).f (p + q)
      (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (p + q)
        (ModuleCat.of k k)).inv ≫ i.hom.f (p + q)) (1 : k)) = _
    rw [hi]
    have hn := CochainComplex.ιTensorObj_tensorHom_f f g p q (p + q) rfl
    have hn' := congrArg (fun t ↦ t
      (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) p
        (ModuleCat.of k k)).inv (1 : k)) ⊗ₜ[k]
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q
        (ModuleCat.of k k)).inv (1 : k)))) hn
    exact hn'
  · simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    rw [Category.assoc, Functor.LaxMonoidal.μ_natural]
    have hc : c.hom = Functor.LaxMonoidal.μ DerivedCategory.Q
        (cupSingleModule k p) (cupSingleModule k q) := cup_flat_comparison k _ _ hP
    rw [← hc, Iso.inv_hom_id_assoc, ← Functor.map_comp]

end
end AlgebraicGeometry.Scheme.Modules
