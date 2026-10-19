/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J8
-/
module

public import Sheaf.Paper.FieldDerivedScalarTower
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
import Sheaf.Paper.FieldCohomologyScalarExtension
import Sheaf.Algebra.Homology.FieldComplexCohomologySplitting
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Descent of a morphism between finite coefficient complexes

Source: blueprint order 1509, the common-stage Hom construction for
`def-weil-finite-coefficient-point` (blueprint: lem-weil-point-fd-morphism-descent).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace DerivedCategory

attribute [local irreducible] Module.Basis.baseChange ModuleCat.extendScalarsComp

open scoped TensorProduct

private theorem finiteCoefficientFields_finset
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω]
    (E F : Padic.FiniteCoefficientFields l Ω) (s : Finset Ω) :
    ∃ N : Padic.FiniteCoefficientFields l Ω, E ≤ N ∧ F ≤ N ∧ ∀ x ∈ s, x ∈ N.val := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨Padic.finiteCoefficientCompositum l Ω E F,
        (show E.val ≤ E.val ⊔ F.val from le_sup_left),
        (show F.val ≤ E.val ⊔ F.val from le_sup_right),
        by simp⟩
  | @insert x s hx ih =>
      obtain ⟨N, hE, hF, hN⟩ := ih
      obtain ⟨X, hX⟩ := (Padic.finiteCoefficientFields_properties l Ω).2.1 x
      refine ⟨Padic.finiteCoefficientCompositum l Ω N X,
        hE.trans (show N.val ≤ N.val ⊔ X.val from le_sup_left),
        hF.trans (show N.val ≤ N.val ⊔ X.val from le_sup_left), ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact (show X.val ≤ N.val ⊔ X.val from le_sup_right) hX
      · exact (show N.val ≤ N.val ⊔ X.val from le_sup_left) (hN y hy)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem basis_map_descend
    {k : Type v} {Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]
    (E F N : IntermediateField k Ω) (hE : E ≤ N) (hF : F ≤ N)
    (A : ModuleCat.{u} E) (B : ModuleCat.{u} F)
    {ι κ : Type} [Finite ι] [Finite κ]
    (a : Module.Basis ι E A) (b : Module.Basis κ F B)
    (m : (ModuleCat.extendScalars.{u, u, u} (R := E) (S := Ω) E.subtype).obj A ⟶
      (ModuleCat.extendScalars.{u, u, u} (R := F) (S := Ω) F.subtype).obj B)
    (hc : ∀ i j, (b.baseChange Ω).repr (m ((a.baseChange Ω) i)) j ∈ N) :
    ∃ g : (ModuleCat.extendScalars.{u, u, u} (IntermediateField.inclusion hE).toRingHom).obj A ⟶
        (ModuleCat.extendScalars.{u, u, u} (IntermediateField.inclusion hF).toRingHom).obj B,
      m = (ModuleCat.extendScalarsComp.{u} (R₁ := E) (R₂ := N) (R₃ := Ω)
          (IntermediateField.inclusion hE).toRingHom N.subtype).hom.app A ≫
        (ModuleCat.extendScalars.{u, u, u} (R := N) (S := Ω) N.subtype).map g ≫
        (ModuleCat.extendScalarsComp.{u} (IntermediateField.inclusion hF).toRingHom
          N.subtype).inv.app B := by
  classical
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite κ
  let := (IntermediateField.inclusion hE).toRingHom.toAlgebra
  let := (IntermediateField.inclusion hF).toRingHom.toAlgebra
  have : IsScalarTower E N Ω := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower F N Ω := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let aN : Module.Basis ι N
      ((ModuleCat.extendScalars.{u, u, u} (IntermediateField.inclusion hE).toRingHom).obj A) :=
    a.baseChange N
  let bN : Module.Basis κ N
      ((ModuleCat.extendScalars.{u, u, u} (IntermediateField.inclusion hF).toRingHom).obj B) :=
    b.baseChange N
  let c (i : ι) (j : κ) : N :=
    ⟨(b.baseChange Ω).repr (m ((a.baseChange Ω) i)) j, hc i j⟩
  let g : (ModuleCat.extendScalars.{u, u, u} (IntermediateField.inclusion hE).toRingHom).obj A ⟶
      (ModuleCat.extendScalars.{u, u, u} (IntermediateField.inclusion hF).toRingHom).obj B :=
    ModuleCat.ofHom (aN.constr N (fun i ↦ ∑ j, c i j • bN j))
  have hg (i : ι) : g (aN i) = ∑ j, c i j • bN j :=
    aN.constr_basis N _ i
  refine ⟨g, ?_⟩
  apply (cancel_mono ((ModuleCat.extendScalarsComp
    (IntermediateField.inclusion hF).toRingHom N.subtype).hom.app B)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app]
  apply ModuleCat.hom_ext
  apply (a.baseChange Ω).ext (σ := RingHom.id Ω)
  intro i
  let v := m ((a.baseChange Ω) i)
  have hv : v = ∑ j, (b.baseChange Ω).repr v j • (b.baseChange Ω) j :=
    ((b.baseChange Ω).sum_repr v).symm
  have hleft :
      (ModuleCat.extendScalarsComp
        (IntermediateField.inclusion hF).toRingHom N.subtype).hom.app B v =
      ∑ j, (b.baseChange Ω).repr v j •
        ((1 : Ω) ⊗ₜ[N] ((1 : N) ⊗ₜ[F] b j)) := by
    calc
      _ = (ModuleCat.extendScalarsComp.{u} (R₁ := F) (R₂ := N) (R₃ := Ω)
          (IntermediateField.inclusion hF).toRingHom N.subtype).hom.app B
            (∑ j, (b.baseChange Ω).repr v j • (b.baseChange Ω) j) :=
        congrArg _ hv
      _ = _ := by
        change ((ModuleCat.extendScalarsComp
            (IntermediateField.inclusion hF).toRingHom N.subtype).hom.app B).hom _ = _
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [map_smul]
        congr 1
        erw [Module.Basis.baseChange_apply Ω b j]
        exact ModuleCat.extendScalarsComp_hom_app_one_tmul
          (IntermediateField.inclusion hF).toRingHom N.subtype B (b j)
  change (ModuleCat.extendScalarsComp
      (IntermediateField.inclusion hF).toRingHom N.subtype).hom.app B v =
    (ModuleCat.extendScalars.{u, u, u} (R := N) (S := Ω) N.subtype).map g
      ((ModuleCat.extendScalarsComp
        (IntermediateField.inclusion hE).toRingHom N.subtype).hom.app A
        ((a.baseChange Ω) i))
  rw [hleft]
  have hright :
      (ModuleCat.extendScalars.{u, u, u} (R := N) (S := Ω) N.subtype).map g
        ((ModuleCat.extendScalarsComp.{u} (R₁ := E) (R₂ := N) (R₃ := Ω)
          (IntermediateField.inclusion hE).toRingHom N.subtype).hom.app A
          ((a.baseChange Ω) i)) = (1 : Ω) ⊗ₜ[N] g (aN i) := by
    have ha := ModuleCat.extendScalarsComp_hom_app_one_tmul
      (IntermediateField.inclusion hE).toRingHom N.subtype A (a i)
    erw [Module.Basis.baseChange_apply, ha, ModuleCat.ExtendScalars.map_tmul]
    erw [show aN i = (1 : N) ⊗ₜ[E] a i from Module.Basis.baseChange_apply N a i]
  rw [hright]
  erw [hg]
  simp only [TensorProduct.tmul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  dsimp only [bN]
  erw [Module.Basis.baseChange_apply]
  change (c i j : Ω) • ((1 : Ω) ⊗ₜ[N] ((1 : N) ⊗ₜ[F] b j)) =
    (1 : Ω) ⊗ₜ[N] ((c i j) • ((1 : N) ⊗ₜ[F] b j))
  rw [TensorProduct.tmul_smul]
  rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def normalizedTower
    {k : Type v} {Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]
    {E N : IntermediateField k Ω} (h : E ≤ N) :
    ModuleCat.extendScalars.{u, u, u} (R := E) (S := Ω) E.subtype ≅
      ModuleCat.extendScalars.{u, u, u} (R := E) (S := N)
        (IntermediateField.inclusion h).toRingHom ⋙
        ModuleCat.extendScalars.{u, u, u} (R := N) (S := Ω) N.subtype := by
  exact ModuleCat.extendScalarsComp.{u} (R₁ := E) (R₂ := N) (R₃ := Ω)
    (IntermediateField.inclusion h).toRingHom N.subtype

attribute [local irreducible] normalizedTower

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def finiteFieldMap
    {k : Type v} {Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]
    {E F N : IntermediateField k Ω} (hE : E ≤ N) (hF : F ≤ N)
    (A : ModuleCat.{u} E) (B : ModuleCat.{u} F)
    (g : (ModuleCat.extendScalars.{u, u, u} (R := E) (S := N)
        (IntermediateField.inclusion hE).toRingHom).obj A ⟶
      (ModuleCat.extendScalars.{u, u, u} (R := F) (S := N)
        (IntermediateField.inclusion hF).toRingHom).obj B) :
    (ModuleCat.extendScalars.{u, u, u} (R := E) (S := Ω) E.subtype).obj A ⟶
      (ModuleCat.extendScalars.{u, u, u} (R := F) (S := Ω) F.subtype).obj B := by
  let U := ModuleCat.extendScalars.{u, u, u} (R := N) (S := Ω) N.subtype
  let e := normalizedTower hE
  let e' := normalizedTower hF
  let v : U.obj ((ModuleCat.extendScalars.{u, u, u}
      (IntermediateField.inclusion hE).toRingHom).obj A) ⟶
    U.obj ((ModuleCat.extendScalars.{u, u, u}
      (IntermediateField.inclusion hF).toRingHom).obj B) := U.map g
  exact e.hom.app A ≫ v ≫ e'.inv.app B

attribute [local irreducible] finiteFieldMap

set_option backward.isDefEq.respectTransparency.types false in
private theorem family_map_descend
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω]
    (E F : Padic.FiniteCoefficientFields l Ω)
    (A : ℤ → ModuleCat.{u} E.val) (B : ℤ → ModuleCat.{u} F.val)
    (hA : ∀ i : ℤ, FiniteDimensional E.val (A i))
    (hB : ∀ i : ℤ, FiniteDimensional F.val (B i))
    (s : Finset ℤ) (hs : ∀ i : ℤ, i ∉ s → Limits.IsZero (A i))
    (m : ∀ i : ℤ, (ModuleCat.extendScalars.{u, u, u} (R := E.val) (S := Ω) E.val.subtype).obj
        (A i) ⟶
      (ModuleCat.extendScalars.{u, u, u} (R := F.val) (S := Ω) F.val.subtype).obj (B i)) :
    ∃ (N : Padic.FiniteCoefficientFields l Ω) (hE : E ≤ N) (hF : F ≤ N)
      (g : ∀ i : ℤ, (ModuleCat.extendScalars.{u, u, u} (R := E.val) (S := N.val)
        (IntermediateField.inclusion (E := E.val) (F := N.val) hE).toRingHom).obj
          (A i) ⟶
        (ModuleCat.extendScalars.{u, u, u} (R := F.val) (S := N.val)
        (IntermediateField.inclusion (E := F.val) (F := N.val) hF).toRingHom).obj (B i)),
      ∀ i : ℤ, m i = finiteFieldMap (k := Padic l) (Ω := Ω) (E := E.val)
        (F := F.val) (N := N.val) hE hF (A i) (B i) (g i) := by
  classical
  let := hA
  let := hB
  let a (i : ℤ) : Module.Basis (Fin (Module.finrank E.val (A i))) E.val (A i) :=
    Module.finBasis E.val (A i)
  let b (i : ℤ) : Module.Basis (Fin (Module.finrank F.val (B i))) F.val (B i) :=
    Module.finBasis F.val (B i)
  let I := Σ i : s, Fin (Module.finrank E.val (A i)) × Fin (Module.finrank F.val (B i))
  let c (j : I) : Ω :=
    ((b j.1).baseChange Ω).repr (m j.1 (((a j.1).baseChange Ω) j.2.1)) j.2.2
  obtain ⟨N, hE, hF, hN⟩ :=
    finiteCoefficientFields_finset l Ω E F (Finset.univ.image c)
  have hc (i : ℤ) (hi : i ∈ s) : ∀ j k,
      ((b i).baseChange Ω).repr (m i (((a i).baseChange Ω) j)) k ∈ N.val := by
    intro j k
    exact hN _ (Finset.mem_image.mpr ⟨⟨⟨i, hi⟩, j, k⟩, Finset.mem_univ _, rfl⟩)
  have hex (i : ℤ) : ∃ g :
      (ModuleCat.extendScalars.{u, u, u} (R := E.val) (S := N.val)
        (IntermediateField.inclusion (E := E.val) (F := N.val) hE).toRingHom).obj (A i) ⟶
      (ModuleCat.extendScalars.{u, u, u} (R := F.val) (S := N.val)
        (IntermediateField.inclusion (E := F.val) (F := N.val) hF).toRingHom).obj (B i),
      m i = finiteFieldMap (k := Padic l) (Ω := Ω) (E := E.val)
        (F := F.val) (N := N.val) hE hF (A i) (B i) g := by
    by_cases hi : i ∈ s
    · unfold finiteFieldMap normalizedTower
      exact basis_map_descend E.val F.val N.val hE hF (A i) (B i) (a i) (b i) (m i)
        (hc i hi)
    · refine ⟨0, ?_⟩
      exact ((ModuleCat.extendScalars.{u, u, u} (R := E.val) (S := Ω)
        E.val.subtype).map_isZero (hs i hi)).eq_of_src _ _
  exact ⟨N, hE, hF, fun i ↦ (hex i).choose, fun i ↦ (hex i).choose_spec⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem homology_descent_lift
    {K L M Ω : Type u} [Field K] [Field L] [Field M] [Field Ω]
    (a : K →+* M) (b : L →+* M) (c : M →+* Ω)
    (A : DerivedCategory (ModuleCat.{u} K)) (B : DerivedCategory (ModuleCat.{u} L))
    (f : (fieldDerivedScalarExtension (c.comp a)).obj A ⟶
      (fieldDerivedScalarExtension (c.comp b)).obj B)
    (t : ∀ i : ℤ,
      (ModuleCat.extendScalars.{u, u, u} a).obj ((homologyFunctor (ModuleCat.{u} K) i).obj A) ⟶
        (ModuleCat.extendScalars.{u, u, u} b).obj ((homologyFunctor (ModuleCat.{u} L) i).obj B))
    (ht : ∀ i : ℤ,
      (fieldDerivedHomologyIso (c.comp a) i).inv.app A ≫
          (homologyFunctor (ModuleCat.{u} Ω) i).map f ≫
          (fieldDerivedHomologyIso (c.comp b) i).hom.app B =
        (ModuleCat.extendScalarsComp.{u} a c).hom.app _ ≫
          (ModuleCat.extendScalars.{u, u, u} c).map (t i) ≫
          (ModuleCat.extendScalarsComp.{u} b c).inv.app _) :
    ∃ g : (fieldDerivedScalarExtension a).obj A ⟶ (fieldDerivedScalarExtension b).obj B,
      f = (fieldScalarTower a c).inv.app A ≫
        (fieldDerivedScalarExtension c).map g ≫ (fieldScalarTower b c).hom.app B := by
  let q (i : ℤ) := (fieldDerivedHomologyIso a i).hom.app A ≫
    t i ≫ (fieldDerivedHomologyIso b i).inv.app B
  obtain ⟨g, hg⟩ := ((field_complex_cohomology_splitting M).2.2.1
    ((fieldDerivedScalarExtension a).obj A)
    ((fieldDerivedScalarExtension b).obj B)).surjective q
  refine ⟨g, ?_⟩
  apply ((field_complex_cohomology_splitting Ω).2.2.1 _ _).injective
  funext i
  have hi := congrFun hg i
  dsimp only at hi
  have ha := congrArg Iso.hom (fieldDerivedHomologyIso_tower a c i A)
  have hb := congrArg Iso.hom (fieldDerivedHomologyIso_tower b c i B)
  dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv] at ha hb
  have hn := (fieldDerivedHomologyIso c i).hom.naturality g
  dsimp only [Functor.comp_map] at hn
  have hf := congrArg
    (fun z ↦ (fieldDerivedHomologyIso (c.comp a) i).hom.app A ≫ z) (ht i)
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp] at hf
  apply (cancel_epi ((homologyFunctor (ModuleCat.{u} Ω) i).map
    ((fieldScalarTower a c).hom.app A))).mp
  apply (cancel_mono ((fieldDerivedHomologyIso (c.comp b) i).hom.app B)).mp
  dsimp only
  simp only [Functor.map_comp, Category.assoc]
  have hcancel := ((homologyFunctor (ModuleCat.{u} Ω) i).mapIso
    ((fieldScalarTower a c).app A)).hom_inv_id
  dsimp only [Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv] at hcancel
  rw [reassoc_of% hcancel]
  rw [hf]
  simp only [Category.assoc]
  rw [reassoc_of% ha]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [hb, reassoc_of% hn, hi]
  dsimp only [q]
  simp only [Functor.map_comp, Category.assoc]
  have hcancelB := ((ModuleCat.extendScalars.{u, u, u} c).mapIso
    ((fieldDerivedHomologyIso b i).app B)).inv_hom_id
  dsimp only [Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv] at hcancelB
  rw [reassoc_of% hcancelB]

set_option backward.isDefEq.respectTransparency.types false in
/-- A morphism after extension to the algebraic closure descends to a common finite
coefficient field, with the canonical tensor-tower comparisons.

Source: blueprint order 1509, the common-stage Hom construction in
`def-weil-point-fd-qlbar-category`, realizing `def-weil-finite-coefficient-point`.
(blueprint: lem-weil-point-fd-morphism-descent).

Proof: Over each of E and F choose complements to boundaries in cycles and to cycles
in the terms of a representing complex. The complements identify the derived object
with its cohomology complex with zero differential: the other two summands form a
contractible complex. Finite support and finite dimension give finitely many finite
bases. Exact scalar extension carries these models and their contracting homotopies
to the closure. A morphism there is consequently uniquely a finite family of matrices
between the extended cohomology spaces. Every entry is algebraic over the base field.
Adjoin these finitely many entries and the two original finite coefficient fields;
their compositum N is finite over the base field. Regard the same matrices as maps
over N, and conjugate by the cohomology-model isomorphisms extended from E and F.
This gives g between the two scalar-extended derived objects over N. Extending g to
the closure recovers the original matrices. The tower comparisons are induced by
the termwise tensor associators, so conjugation by their inverses and forwards maps
g to precisely the given morphism. Empty cohomology support gives the zero map at
the compositum of E and F; equal fields and zero-dimensional spaces require no
additional choice of entries. -/
theorem pointFd_morphism_descent
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω]
    (E F : Padic.FiniteCoefficientFields l Ω)
    (A : DerivedCategory (ModuleCat.{u} E.val))
    (B : DerivedCategory (ModuleCat.{u} F.val))
    (hA : pointFiniteDimensional E.val A) (hB : pointFiniteDimensional F.val B)
    (f : (fieldDerivedScalarExtension (K := E.val) (L := Ω) E.val.subtype).obj A ⟶
      (fieldDerivedScalarExtension (K := F.val) (L := Ω) F.val.subtype).obj B) :
    ∃ (N : Padic.FiniteCoefficientFields l Ω) (hE : E ≤ N) (hF : F ≤ N)
      (g : (fieldDerivedScalarExtension
          (IntermediateField.inclusion (E := E.val) (F := N.val) hE).toRingHom).obj A ⟶
        (fieldDerivedScalarExtension
          (IntermediateField.inclusion (E := F.val) (F := N.val) hF).toRingHom).obj B),
      f = (fieldScalarTower
          (IntermediateField.inclusion (E := E.val) (F := N.val) hE).toRingHom
          N.val.subtype).inv.app A ≫
        (fieldDerivedScalarExtension (K := N.val) (L := Ω) N.val.subtype).map g ≫
        (fieldScalarTower
          (IntermediateField.inclusion (E := F.val) (F := N.val) hF).toRingHom
          N.val.subtype).hom.app B := by
  classical
  obtain ⟨⟨s, hs⟩, hfdA⟩ := hA
  obtain ⟨_, hfdB⟩ := hB
  let m (i : ℤ) := (fieldDerivedHomologyIso (K := E.val) (L := Ω) E.val.subtype i).inv.app A ≫
    (homologyFunctor (ModuleCat.{u} Ω) i).map f ≫
    (fieldDerivedHomologyIso (K := F.val) (L := Ω) F.val.subtype i).hom.app B
  obtain ⟨N, hE, hF, t, ht⟩ := family_map_descend l Ω E F
    (fun i ↦ (homologyFunctor (ModuleCat.{u} E.val) i).obj A)
    (fun i ↦ (homologyFunctor (ModuleCat.{u} F.val) i).obj B)
    hfdA hfdB s hs m
  obtain ⟨g, hg⟩ := homology_descent_lift
    (IntermediateField.inclusion (E := E.val) (F := N.val) hE).toRingHom
    (IntermediateField.inclusion (E := F.val) (F := N.val) hF).toRingHom N.val.subtype A B f t (by
        with_unfolding_all exact ht)
  exact ⟨N, hE, hF, g, hg⟩

end DerivedCategory
