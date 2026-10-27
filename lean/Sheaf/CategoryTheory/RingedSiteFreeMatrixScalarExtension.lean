/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Data.Matrix.Mul
import Sheaf.CategoryTheory.SheafTensor

/-! # Global matrices and scalar extension of finite free internal sheaf modules

Source: Stacks Project, Modules on Sites, Tag 03EK, section-tensor-product;
Hemo–Richarz–Scholbach, Example 3.1, p. 6 (context).
(blueprint: lem-sfb-ringed-site-free-matrix-scalar-extension).

The existing finite biproducts of the regular internal module give free modules, including
rank zero. All tensor formulas use the lax tensor comparison into the sheaf tensor,
followed by the relative coequalizer projection.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

attribute [instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

namespace CategoryTheory.InternalAbelianSheafModule

/-- The size bound permits the existing small-model construction.
Source: the site's size hypothesis
(blueprint: lem-sfb-ringed-site-free-matrix-scalar-extension). -/
noncomputable instance freeMatrixEssentiallySmall
    {C : Type v} [Category.{w} C] [UnivLE.{max v w, u}] : EssentiallySmall.{u} C := by
  have : UnivLE.{v, u} := UnivLE.trans.{v, max v w, u}
  have : UnivLE.{w, u} := UnivLE.trans.{w, max v w, u}
  exact essentiallySmall_of_small_of_locallySmall C

variable {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
  [UnivLE.{max v w, u}] [HasSheafify J AddCommGrpCat.{u}]
  [(J.W (A := AddCommGrpCat.{u})).IsMonoidal]

/-- Left tensor preserves the coequalizers defining scalar extension.
Source: sk-def-sfb-sheaf-tensor, closedness and colimit preservation
(blueprint: lem-sfb-ringed-site-free-matrix-scalar-extension). -/
noncomputable instance freeMatrixTensorLeft (X : Sheaf J AddCommGrpCat.{u}) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft X) :=
  (sfbSheafTensor_properties (A := AddCommGrpCat.{u}) J).2.2 X |>.1

/-- Right tensor preserves the coequalizers defining scalar extension.
Source: sk-def-sfb-sheaf-tensor, closedness and colimit preservation
(blueprint: lem-sfb-ringed-site-free-matrix-scalar-extension). -/
noncomputable instance freeMatrixTensorRight (X : Sheaf J AddCommGrpCat.{u}) :
    PreservesColimitsOfSize.{0, 0} (tensorRight X) :=
  (sfbSheafTensor_properties (A := AddCommGrpCat.{u}) J).2.2 X |>.2.1

/-- The local pure tensor maps into the internal relative coequalizer. This does not
identify sections of a sheaf tensor with tensors of section rings.
Source: Tag 03EK and def-sfb-modobj-extension
(blueprint: lem-sfb-ringed-site-free-matrix-scalar-extension). -/
noncomputable def ringedSiteExtensionTmul
    {R S : Sheaf J AddCommGrpCat.{u}} [MonObj R] [IsCommMonObj R] [MonObj S]
    (ψ : R ⟶ S) [IsMonHom ψ] (M : Mod (Sheaf J AddCommGrpCat.{u}) R)
    (U : Cᵒᵖ) (b : S.obj.obj U) (a : M.X.obj.obj U) :
    ((Mod.extendScalars ψ).obj M).X.obj.obj U :=
  ((Mod.extendπ ψ M).hom.app U)
    (((Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) S M.X).app U)
      (b ⊗ₜ[ℤ] a))

/-- Normalized coordinates and the additive global-matrix description. The biproduct-projection
formula fixes coordinates, and the basis-entry formula fixes the matrix equivalence.
Source: Tag 03EK, explicit global-basis calculation
(blueprint: lem-sfb-ringed-site-free-matrix-scalar-extension). -/
structure RingedSiteFreeMatrices (R : Sheaf J AddCommGrpCat.{u}) [MonObj R]
    [IsCommMonObj R] (one : C) (hOne : IsTerminal one) where
  /-- Coordinate tuples are the sections of the finite direct sum. -/
  coordinates : ∀ (n : ℕ) (U : Cᵒᵖ),
    (Mod.finiteFree R n).X.obj.obj U ≃+
      (Fin n → (sectionRingSheaf J R).obj.obj U)
  /-- The coordinates are the canonical biproduct projections. -/
  coordinates_projection : ∀ (n : ℕ) (U : Cᵒᵖ)
      (a : (Mod.finiteFree R n).X.obj.obj U) (i : Fin n),
    coordinates n U a i =
      ((biproduct.π (fun (_ : Fin n) ↦ Mod.regular R) i).hom.hom.app U) a
  /-- Additive bijection from module arrows to global-section matrices. -/
  matrix : ∀ (m n : ℕ),
    (Mod.finiteFree R n ⟶ Mod.finiteFree R m) ≃+
      Matrix (Fin m) (Fin n) ((sectionRingSheaf J R).obj.obj (.op one))
  /-- Entries are precisely global components of images of standard basis sections. -/
  matrix_basis : ∀ (m n : ℕ)
      (f : Mod.finiteFree R n ⟶ Mod.finiteFree R m)
      (i : Fin m) (j : Fin n),
    matrix m n f i j = coordinates m (.op one)
      ((f.hom.hom.app (.op one))
        ((coordinates n (.op one)).symm (Pi.single j 1))) i
  /-- The section formula restricts global matrix entries along the unique map to one. -/
  matrix_sections : ∀ (m n : ℕ)
      (f : Mod.finiteFree R n ⟶ Mod.finiteFree R m)
      (U : Cᵒᵖ) (a : (Mod.finiteFree R n).X.obj.obj U) (i : Fin m),
    coordinates m U ((f.hom.hom.app U) a) i =
      ∑ j : Fin n, ((sectionRingSheaf J R).obj.map (hOne.from U.unop).op)
        (matrix m n f i j) * coordinates n U a j
  /-- Composition corresponds to matrix multiplication, in the specified order. -/
  matrix_comp : ∀ (k m n : ℕ)
      (f : Mod.finiteFree R n ⟶ Mod.finiteFree R m)
      (g : Mod.finiteFree R m ⟶ Mod.finiteFree R k),
    matrix k n (f ≫ g) = matrix k m g * matrix m n f
  /-- Identity arrows correspond to identity matrices, also at rank zero. -/
  matrix_id : ∀ n : ℕ, matrix n n (𝟙 (Mod.finiteFree R n)) = 1
  /-- Both additive groups have a single zero element if either rank is zero. -/
  zero_ranks : ∀ (m n : ℕ), m = 0 ∨ n = 0 →
    Subsingleton (Mod.finiteFree R n ⟶ Mod.finiteFree R m) ∧
      Subsingleton (Matrix (Fin m) (Fin n) ((sectionRingSheaf J R).obj.obj (.op one)))

private lemma hom_sum_apply
    {R : Sheaf J AddCommGrpCat.{u}} [MonObj R]
    {M N : Mod (Sheaf J AddCommGrpCat.{u}) R}
    {I : Type*} (s : Finset I) (f : I → (M ⟶ N))
    (U : Cᵒᵖ) (a : M.X.obj.obj U) :
    (∑ i ∈ s, f i).hom.hom.app U a = ∑ i ∈ s, (f i).hom.hom.app U a :=
  map_sum
    ({ toFun := fun f ↦ f.hom.hom.app U a
       map_zero' := rfl
       map_add' := fun _ _ ↦ rfl } : (M ⟶ N) →+ N.X.obj.obj U) f s

omit [HasSheafify J AddCommGrpCat.{u}] in
@[simp] private lemma hom_comp_apply
    {R : Sheaf J AddCommGrpCat.{u}} [MonObj R]
    {M N P : Mod (Sheaf J AddCommGrpCat.{u}) R}
    (f : M ⟶ N) (g : N ⟶ P) (U : Cᵒᵖ) (a : M.X.obj.obj U) :
    (f ≫ g).hom.hom.app U a = g.hom.hom.app U (f.hom.hom.app U a) := rfl

omit [HasSheafify J AddCommGrpCat.{u}] in
@[simp] private lemma hom_id_apply
    {R : Sheaf J AddCommGrpCat.{u}} [MonObj R]
    (M : Mod (Sheaf J AddCommGrpCat.{u}) R) (U : Cᵒᵖ) (a : M.X.obj.obj U) :
    (𝟙 M : M ⟶ M).hom.hom.app U a = a := rfl

@[simp] private lemma hom_zero_apply
    {R : Sheaf J AddCommGrpCat.{u}} [MonObj R]
    (M N : Mod (Sheaf J AddCommGrpCat.{u}) R) (U : Cᵒᵖ) (a : M.X.obj.obj U) :
    (0 : M ⟶ N).hom.hom.app U a = 0 := rfl

private noncomputable def coords
    (R : Sheaf J AddCommGrpCat.{u}) [MonObj R] [IsCommMonObj R]
    (n : ℕ) (U : Cᵒᵖ) :
    (Mod.finiteFree R n).X.obj.obj U ≃+
      (Fin n → (sectionRingSheaf J R).obj.obj U) where
  toFun a i := (biproduct.π (fun _ : Fin n ↦ Mod.regular R) i).hom.hom.app U a
  invFun b := ∑ i, (biproduct.ι (fun _ : Fin n ↦ Mod.regular R) i).hom.hom.app U (b i)
  map_add' a b := by ext i; exact map_add _ a b
  left_inv a := by
    with_unfolding_all
      have h := congrArg (fun f : Mod.finiteFree R n ⟶ Mod.finiteFree R n ↦
        f.hom.hom.app U a) (biproduct.total (f := fun _ : Fin n ↦ Mod.regular R))
      simpa only [hom_sum_apply, hom_comp_apply, hom_id_apply] using h
  right_inv b := by
    with_unfolding_all
      funext j
      dsimp only
      rw [map_sum]
      change (∑ i, ((biproduct.ι (fun _ : Fin n ↦ Mod.regular R) i ≫
        biproduct.π _ j).hom.hom.app U) (b i)) = b j
      classical
      simp only [biproduct.ι_π]
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij
        simp [hij]
      · simp

private lemma regular_linear
    (R : Sheaf J AddCommGrpCat.{u}) [MonObj R] [IsCommMonObj R]
    (f : Mod.regular R ⟶ Mod.regular R) (U : Cᵒᵖ)
    (a b : (sectionRingSheaf J R).obj.obj U) :
    f.hom.hom.app U (a * b) = a * @id ((sectionRingSheaf J R).obj.obj U) (f.hom.hom.app U b) := by
  with_unfolding_all
    exact (((sectionModuleFunctor J R).map f).val.app U).hom.map_smul a b

private lemma regular_eval
    (one : C) (hOne : IsTerminal one)
    (R : Sheaf J AddCommGrpCat.{u}) [MonObj R] [IsCommMonObj R]
    (f : Mod.regular R ⟶ Mod.regular R) (U : Cᵒᵖ)
    (a : (sectionRingSheaf J R).obj.obj U) :
    @id ((sectionRingSheaf J R).obj.obj U) (f.hom.hom.app U a) =
      ((sectionRingSheaf J R).obj.map (hOne.from U.unop).op)
        (@id ((sectionRingSheaf J R).obj.obj (.op one)) (f.hom.hom.app (.op one)
          (1 : (sectionRingSheaf J R).obj.obj (.op one)))) * a := by
  with_unfolding_all
    have h := ConcreteCategory.congr_hom (f.hom.hom.naturality (hOne.from U.unop).op)
      (1 : (sectionRingSheaf J R).obj.obj (.op one))
    change f.hom.hom.app U
      (((sectionRingSheaf J R).obj.map (hOne.from U.unop).op) 1) =
      ((sectionRingSheaf J R).obj.map (hOne.from U.unop).op)
        (@id ((sectionRingSheaf J R).obj.obj (.op one)) (f.hom.hom.app (.op one)
          (1 : (sectionRingSheaf J R).obj.obj (.op one)))) at h
    rw [map_one] at h
    have hl := regular_linear J R f U a 1
    rw [mul_one, h, mul_comm] at hl
    exact hl

private noncomputable def regularFromSection
    (one : C) (hOne : IsTerminal one)
    (R : Sheaf J AddCommGrpCat.{u}) [MonObj R] [IsCommMonObj R]
    (t : (sectionRingSheaf J R).obj.obj (.op one)) :
    Mod.regular R ⟶ Mod.regular R := by
  let A := (sectionRingSheaf J R).obj
  let P := (sectionModuleFunctor J R).obj (Mod.regular R)
  let l (U : Cᵒᵖ) : P.val.obj U ⟶ P.val.obj U :=
    ModuleCat.ofHom (X := P.val.obj U) (Y := P.val.obj U)
      { toFun := fun a ↦ @id (A.obj U) a * A.map (hOne.from U.unop).op t
        map_add' := by
          intro a b
          with_unfolding_all
            exact add_mul (@id (A.obj U) a) (@id (A.obj U) b) _
        map_smul' := by
          intro r a
          with_unfolding_all
            exact mul_assoc (@id (A.obj U) r) (@id (A.obj U) a) _ }
  apply (sectionModuleFunctor_fullyFaithful J R).preimage
  refine ⟨{ app := l, naturality := ?_ }⟩
  intro U V f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change A.map f a * A.map (hOne.from V.unop).op t =
    A.map f (@id (A.obj U) a * A.map (hOne.from U.unop).op t)
  rw [map_mul, ← CommRingCat.comp_apply, ← A.map_comp]
  rw [show (hOne.from V.unop).op = (hOne.from U.unop).op ≫ f by
    apply Quiver.Hom.unop_inj
    exact hOne.hom_ext _ _]
  rfl

private lemma regularFromSection_apply
    (one : C) (hOne : IsTerminal one)
    (R : Sheaf J AddCommGrpCat.{u}) [MonObj R] [IsCommMonObj R]
    (t : (sectionRingSheaf J R).obj.obj (.op one)) (U : Cᵒᵖ)
    (a : (sectionRingSheaf J R).obj.obj U) :
    (regularFromSection J one hOne R t).hom.hom.app U a =
      a * (sectionRingSheaf J R).obj.map (hOne.from U.unop).op t := by
  rfl

private lemma regularFromSection_one
    (one : C) (hOne : IsTerminal one)
    (R : Sheaf J AddCommGrpCat.{u}) [MonObj R] [IsCommMonObj R]
    (t : (sectionRingSheaf J R).obj.obj (.op one)) :
    (regularFromSection J one hOne R t).hom.hom.app (.op one)
      (1 : (sectionRingSheaf J R).obj.obj (.op one)) = t := by
  with_unfolding_all
    rw [regularFromSection_apply, one_mul]
    have h : hOne.from one = 𝟙 one := hOne.hom_ext _ _
    rw [h, op_id, Functor.map_id]
    rfl

private lemma regular_ext
    (one : C) (hOne : IsTerminal one)
    (R : Sheaf J AddCommGrpCat.{u}) [MonObj R] [IsCommMonObj R]
    {f g : Mod.regular R ⟶ Mod.regular R}
    (h : f.hom.hom.app (.op one) (1 : (sectionRingSheaf J R).obj.obj (.op one)) =
      g.hom.hom.app (.op one) (1 : (sectionRingSheaf J R).obj.obj (.op one))) : f = g := by
  apply Mod.hom_ext
  ext U a
  with_unfolding_all
    exact (regular_eval J one hOne R f U a).trans
      ((congrArg (fun t ↦ (sectionRingSheaf J R).obj.map (hOne.from U.unop).op t *
        @id ((sectionRingSheaf J R).obj.obj U) a) h).trans
        (regular_eval J one hOne R g U a).symm)

private lemma coords_single
    (R : Sheaf J AddCommGrpCat.{u}) [MonObj R] [IsCommMonObj R]
    (n : ℕ) (U : Cᵒᵖ) (j : Fin n) (a : (sectionRingSheaf J R).obj.obj U) :
    (coords J R n U).symm (Pi.single j a) =
      (biproduct.ι (fun _ : Fin n ↦ Mod.regular R) j).hom.hom.app U a := by
  classical
  with_unfolding_all
    change (∑ i, (biproduct.ι (fun _ : Fin n ↦ Mod.regular R) i).hom.hom.app U
      ((Pi.single j a : Fin n → (sectionRingSheaf J R).obj.obj U) i)) = _
    simp only [Pi.single_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [hij]
    · simp

private noncomputable def matrices
    (one : C) (hOne : IsTerminal one)
    (R : Sheaf J AddCommGrpCat.{u}) [MonObj R] [IsCommMonObj R]
    (m n : ℕ) :
    (Mod.finiteFree R n ⟶ Mod.finiteFree R m) ≃+
      Matrix (Fin m) (Fin n) ((sectionRingSheaf J R).obj.obj (.op one)) where
  toFun f i j := @id ((sectionRingSheaf J R).obj.obj (.op one))
    ((biproduct.ι (fun _ : Fin n ↦ Mod.regular R) j ≫ f ≫
    biproduct.π (fun _ : Fin m ↦ Mod.regular R) i).hom.hom.app (.op one)
      (1 : (sectionRingSheaf J R).obj.obj (.op one)))
  invFun t := biproduct.matrix fun j i ↦ regularFromSection J one hOne R (t i j)
  map_add' f g := by
    ext i j
    simp only [Preadditive.comp_add, Preadditive.add_comp]
    rfl
  left_inv f := by
    apply biproduct.hom_ext'
    intro j
    apply biproduct.hom_ext
    intro i
    apply regular_ext J one hOne R
    simp only [biproduct.ι_matrix, biproduct.lift_π, regularFromSection_one,
      Category.assoc, id_eq]
  right_inv t := by
    with_unfolding_all
      ext i j
      change (biproduct.ι (fun _ : Fin n ↦ Mod.regular R) j ≫
        (biproduct.matrix fun j i ↦ regularFromSection J one hOne R (t i j)) ≫
          biproduct.π (fun _ : Fin m ↦ Mod.regular R) i).hom.hom.app (.op one)
            (1 : (sectionRingSheaf J R).obj.obj (.op one)) = _
      rw [biproduct.ι_matrix_assoc, biproduct.lift_π, regularFromSection_one]

private lemma matrices_sections
    (one : C) (hOne : IsTerminal one)
    (R : Sheaf J AddCommGrpCat.{u}) [MonObj R] [IsCommMonObj R]
    (m n : ℕ) (f : Mod.finiteFree R n ⟶ Mod.finiteFree R m)
    (U : Cᵒᵖ) (a : (Mod.finiteFree R n).X.obj.obj U) (i : Fin m) :
    coords J R m U (f.hom.hom.app U a) i =
      ∑ j : Fin n, ((sectionRingSheaf J R).obj.map (hOne.from U.unop).op)
        (matrices J one hOne R m n f i j) * coords J R n U a j := by
  with_unfolding_all
    have ha := (coords J R n U).symm_apply_apply a
    change (∑ j, (biproduct.ι (fun _ : Fin n ↦ Mod.regular R) j).hom.hom.app U
      (coords J R n U a j)) = a at ha
    conv_lhs => rw [← ha]
    change (biproduct.π (fun _ : Fin m ↦ Mod.regular R) i).hom.hom.app U
      (f.hom.hom.app U (∑ j, _)) = _
    rw [map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    change (biproduct.ι (fun _ : Fin n ↦ Mod.regular R) j ≫ f ≫
      biproduct.π (fun _ : Fin m ↦ Mod.regular R) i).hom.hom.app U _ = _
    exact regular_eval J one hOne R _ U _

private lemma matrices_basis
    (one : C) (hOne : IsTerminal one)
    (R : Sheaf J AddCommGrpCat.{u}) [MonObj R] [IsCommMonObj R]
    (m n : ℕ) (f : Mod.finiteFree R n ⟶ Mod.finiteFree R m)
    (i : Fin m) (j : Fin n) :
    matrices J one hOne R m n f i j = coords J R m (.op one)
      (f.hom.hom.app (.op one) ((coords J R n (.op one)).symm (Pi.single j 1))) i := by
  with_unfolding_all
    rw [coords_single]
    rfl

private lemma matrices_comp
    (one : C) (hOne : IsTerminal one)
    (R : Sheaf J AddCommGrpCat.{u}) [MonObj R] [IsCommMonObj R]
    (k m n : ℕ) (f : Mod.finiteFree R n ⟶ Mod.finiteFree R m)
    (g : Mod.finiteFree R m ⟶ Mod.finiteFree R k) :
    matrices J one hOne R k n (f ≫ g) =
      matrices J one hOne R k m g * matrices J one hOne R m n f := by
  ext i j
  rw [matrices_basis]
  change coords J R k (.op one)
    (g.hom.hom.app (.op one) (f.hom.hom.app (.op one) _)) i = _
  rw [matrices_sections J one hOne R]
  have h : hOne.from one = 𝟙 one := hOne.hom_ext _ _
  simp only [h, op_id, Functor.map_id, CommRingCat.id_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro l _
  rw [matrices_basis J one hOne R m n f]

private lemma matrices_id
    (one : C) (hOne : IsTerminal one)
    (R : Sheaf J AddCommGrpCat.{u}) [MonObj R] [IsCommMonObj R]
    (n : ℕ) : matrices J one hOne R n n (𝟙 _) = 1 := by
  classical
  with_unfolding_all
    ext i j
    change ((biproduct.ι (fun _ : Fin n ↦ Mod.regular R) j ≫ 𝟙 _ ≫
      biproduct.π _ i).hom.hom.app (.op one))
      (1 : (sectionRingSheaf J R).obj.obj (.op one)) = _
    by_cases h : j = i
    · subst j
      simp
    · simp [biproduct.ι_π_ne _ h, Ne.symm h]

private lemma free_zero
    (R : Sheaf J AddCommGrpCat.{u}) [MonObj R] [IsCommMonObj R] :
    IsZero (Mod.finiteFree R 0) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply biproduct.hom_ext
  intro i
  exact Fin.elim0 i

private noncomputable def matrixData
    (one : C) (hOne : IsTerminal one)
    (R : Sheaf J AddCommGrpCat.{u}) [MonObj R] [IsCommMonObj R] :
    RingedSiteFreeMatrices J R one hOne where
  coordinates := coords J R
  coordinates_projection := fun _ _ _ _ ↦ rfl
  matrix := matrices J one hOne R
  matrix_basis := matrices_basis J one hOne R
  matrix_sections := matrices_sections J one hOne R
  matrix_comp := matrices_comp J one hOne R
  matrix_id := matrices_id J one hOne R
  zero_ranks m n h := by
    rcases h with rfl | rfl
    · exact ⟨⟨fun f g ↦ (free_zero J R).eq_of_tgt f g⟩, inferInstance⟩
    · exact ⟨⟨fun f g ↦ (free_zero J R).eq_of_src f g⟩, inferInstance⟩

private noncomputable def regularIso
    {R S : Sheaf J AddCommGrpCat.{u}} [MonObj R] [IsCommMonObj R] [MonObj S]
    (ψ : R ⟶ S) [IsMonHom ψ] :
    (Mod.extendScalars ψ).obj (Mod.regular R) ≅ Mod.regular S :=
  Mod.isoMk
    { hom := Bimod.RightUnitorBimod.hom (Bimod.ofMonHom ψ)
      inv := Bimod.RightUnitorBimod.inv (Bimod.ofMonHom ψ)
      hom_inv_id := Bimod.RightUnitorBimod.hom_inv_id (Bimod.ofMonHom ψ)
      inv_hom_id := Bimod.RightUnitorBimod.inv_hom_id (Bimod.ofMonHom ψ) }
    (Bimod.RightUnitorBimod.hom_left_act_hom' (Bimod.ofMonHom ψ))

private lemma regularIso_π
    {R S : Sheaf J AddCommGrpCat.{u}} [MonObj R] [IsCommMonObj R] [MonObj S]
    (ψ : R ⟶ S) [IsMonHom ψ] :
    Mod.extendπ ψ (Mod.regular R) ≫ (regularIso J ψ).hom.hom =
      S ◁ ψ ≫ MonObj.mul (X := S) := by
  apply coequalizer.π_desc

private lemma regularIso_unit
    {R S : Sheaf J AddCommGrpCat.{u}} [MonObj R] [IsCommMonObj R] [MonObj S]
    (ψ : R ⟶ S) [IsMonHom ψ] :
    Mod.extendUnitHom ψ (Mod.regular R) ≫ (regularIso J ψ).hom.hom = ψ := by
  rw [Mod.extendUnitHom]
  simp only [Category.assoc]
  rw [regularIso_π]
  exact MonObj.leftUnitor_inv_one_whiskerRight_whiskerLeft_mul ψ

private noncomputable def freeIso
    {R S : Sheaf J AddCommGrpCat.{u}} [MonObj R] [IsCommMonObj R]
    [MonObj S] [IsCommMonObj S] (ψ : R ⟶ S) [IsMonHom ψ] (n : ℕ) :
    (Mod.extendScalars ψ).obj (Mod.finiteFree R n) ≅ Mod.finiteFree S n :=
  (Mod.extendScalars ψ).mapBiproduct (fun _ : Fin n ↦ Mod.regular R) ≪≫
    biproduct.mapIso (fun _ ↦ regularIso J ψ)

private lemma freeIso_π
    {R S : Sheaf J AddCommGrpCat.{u}} [MonObj R] [IsCommMonObj R]
    [MonObj S] [IsCommMonObj S] (ψ : R ⟶ S) [IsMonHom ψ] (n : ℕ) (i : Fin n) :
    (freeIso J ψ n).hom ≫ biproduct.π (fun _ : Fin n ↦ Mod.regular S) i =
      (Mod.extendScalars ψ).map (biproduct.π (fun _ : Fin n ↦ Mod.regular R) i) ≫
        (regularIso J ψ).hom := by
  simp [freeIso]

omit [HasSheafify J AddCommGrpCat.{u}] in
private lemma tensor_generators_map
    {F F' G G' : Sheaf J AddCommGrpCat.{u}} (f : F ⟶ F') (g : G ⟶ G')
    (U : Cᵒᵖ) (a : F.obj.obj U) (b : G.obj.obj U) :
    (f ⊗ₘ g).hom.app U
      ((Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) F G).app U
        (a ⊗ₜ[ℤ] b)) =
      (Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) F' G').app U
        ((f.hom.app U a) ⊗ₜ[ℤ] (g.hom.app U b)) := by
  with_unfolding_all
    exact (congrArg (fun k ↦ k.app U (a ⊗ₜ[ℤ] b))
      (Functor.LaxMonoidal.μ_natural (sheafToPresheaf J AddCommGrpCat.{u}) f g)).symm

private lemma extension_tmul_map
    {R S : Sheaf J AddCommGrpCat.{u}} [MonObj R] [IsCommMonObj R] [MonObj S]
    (ψ : R ⟶ S) [IsMonHom ψ]
    {M N : Mod (Sheaf J AddCommGrpCat.{u}) R} (f : M ⟶ N)
    (U : Cᵒᵖ) (b : S.obj.obj U) (a : M.X.obj.obj U) :
    ((Mod.extendScalars ψ).map f).hom.hom.app U
      (ringedSiteExtensionTmul J ψ M U b a) =
      ringedSiteExtensionTmul J ψ N U b (f.hom.hom.app U a) := by
  have h := congrArg (fun k ↦ k.hom.app U
    ((Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) S M.X).app U
      (b ⊗ₜ[ℤ] a))) (Mod.extendπ_extendScalarsMap ψ f)
  change _ = (Mod.extendπ ψ N).hom.app U
    ((S ◁ f.hom).hom.app U _) at h
  rw [show S ◁ f.hom = 𝟙 S ⊗ₘ f.hom by simp, tensor_generators_map] at h
  exact h

private lemma regularIso_tmul
    {R S : Sheaf J AddCommGrpCat.{u}} [MonObj R] [IsCommMonObj R]
    [MonObj S] [IsCommMonObj S] (ψ : R ⟶ S) [IsMonHom ψ]
    (U : Cᵒᵖ) (b : (sectionRingSheaf J S).obj.obj U)
    (a : (sectionRingSheaf J R).obj.obj U) :
    (regularIso J ψ).hom.hom.hom.app U
      (ringedSiteExtensionTmul J ψ (Mod.regular R) U b a) =
      b * @id ((sectionRingSheaf J S).obj.obj U) (ψ.hom.app U a) := by
  with_unfolding_all
    have h := congrArg (fun k ↦ k.hom.app U
      ((Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) S R).app U
        (b ⊗ₜ[ℤ] a))) (regularIso_π J ψ)
    change _ = (MonObj.mul (X := S)).hom.app U ((S ◁ ψ).hom.app U _) at h
    rw [show S ◁ ψ = 𝟙 S ⊗ₘ ψ by simp, tensor_generators_map] at h
    exact h

private lemma freeIso_tmul
    {R S : Sheaf J AddCommGrpCat.{u}} [MonObj R] [IsCommMonObj R]
    [MonObj S] [IsCommMonObj S] (ψ : R ⟶ S) [IsMonHom ψ]
    (n : ℕ) (U : Cᵒᵖ) (b : (sectionRingSheaf J S).obj.obj U)
    (a : (Mod.finiteFree R n).X.obj.obj U) (j : Fin n) :
    coords J S n U ((freeIso J ψ n).hom.hom.hom.app U
      (ringedSiteExtensionTmul J ψ (Mod.finiteFree R n) U b a)) j =
      b * @id ((sectionRingSheaf J S).obj.obj U) (ψ.hom.app U (coords J R n U a j)) := by
  change ((freeIso J ψ n).hom ≫ biproduct.π _ j).hom.hom.app U _ = _
  rw [freeIso_π, hom_comp_apply, extension_tmul_map, regularIso_tmul]
  rfl

private lemma extension_unit_natural
    {R S : Sheaf J AddCommGrpCat.{u}} [MonObj R] [IsCommMonObj R] [MonObj S]
    (ψ : R ⟶ S) [IsMonHom ψ]
    {M N : Mod (Sheaf J AddCommGrpCat.{u}) R} (f : M ⟶ N) :
    Mod.extendUnitHom ψ M ≫ ((Mod.extendScalars ψ).map f).hom =
      f.hom ≫ Mod.extendUnitHom ψ N := by
  have h := (Mod.extendRestrictAdjunction ψ).unit.naturality f
  exact (congrArg Mod.Hom.hom h).symm

private lemma freeIso_unit
    {R S : Sheaf J AddCommGrpCat.{u}} [MonObj R] [IsCommMonObj R]
    [MonObj S] [IsCommMonObj S] (ψ : R ⟶ S) [IsMonHom ψ]
    (n : ℕ) (U : Cᵒᵖ) (a : (Mod.finiteFree R n).X.obj.obj U) (j : Fin n) :
    coords J S n U ((freeIso J ψ n).hom.hom.hom.app U
      ((Mod.extendUnitHom ψ (Mod.finiteFree R n)).hom.app U a)) j =
      ψ.hom.app U (coords J R n U a j) := by
  have h := congrArg Mod.Hom.hom (freeIso_π J ψ n j)
  change (freeIso J ψ n).hom.hom ≫ (biproduct.π (fun _ : Fin n ↦ Mod.regular S) j).hom = _ at h
  have hh : Mod.extendUnitHom ψ (Mod.finiteFree R n) ≫
      (freeIso J ψ n).hom.hom ≫ (biproduct.π (fun _ : Fin n ↦ Mod.regular S) j).hom =
      (biproduct.π (fun _ : Fin n ↦ Mod.regular R) j).hom ≫ ψ := by
    rw [h, Mod.comp_hom', ← Category.assoc, extension_unit_natural,
      Category.assoc, regularIso_unit]
  exact congrArg (fun k ↦ k.hom.app U a) hh

private lemma section_map_one
    {R S : Sheaf J AddCommGrpCat.{u}} [MonObj R] [IsCommMonObj R]
    [MonObj S] [IsCommMonObj S] (ψ : R ⟶ S) [IsMonHom ψ] (U : Cᵒᵖ) :
    ψ.hom.app U (1 : (sectionRingSheaf J R).obj.obj U) =
      (1 : (sectionRingSheaf J S).obj.obj U) := by
  with_unfolding_all
    let f : Mon.mk R ⟶ Mon.mk S := ⟨ψ⟩
    let g := ((Monoidal.monFunctorCategoryEquivalence Cᵒᵖ AddCommGrpCat.{u}).functor.map
      ((sheafToPresheaf J AddCommGrpCat.{u}).mapMon.map f)).app U
    exact (monToRing.map g).hom.map_one

private lemma freeIso_inv
    {R S : Sheaf J AddCommGrpCat.{u}} [MonObj R] [IsCommMonObj R]
    [MonObj S] [IsCommMonObj S] (ψ : R ⟶ S) [IsMonHom ψ]
    (n : ℕ) (U : Cᵒᵖ) (b : Fin n → (sectionRingSheaf J S).obj.obj U) :
    (freeIso J ψ n).inv.hom.hom.app U ((coords J S n U).symm b) =
      ∑ j : Fin n, ringedSiteExtensionTmul J ψ (Mod.finiteFree R n) U
        (b j) ((coords J R n U).symm (Pi.single j 1)) := by
  classical
  with_unfolding_all
    have hi : Function.Injective ((freeIso J ψ n).hom.hom.hom.app U) := by
      intro x y h
      have hh := congrArg ((freeIso J ψ n).inv.hom.hom.app U) h
      have he (x : ((Mod.extendScalars ψ).obj (Mod.finiteFree R n)).X.obj.obj U) :
          (freeIso J ψ n).inv.hom.hom.app U
            ((freeIso J ψ n).hom.hom.hom.app U x) = x :=
        congrArg (fun f : (Mod.extendScalars ψ).obj (Mod.finiteFree R n) ⟶
            (Mod.extendScalars ψ).obj (Mod.finiteFree R n) ↦ f.hom.hom.app U x)
          (freeIso J ψ n).hom_inv_id
      exact (he x).symm.trans (hh.trans (he y))
    apply hi
    have he (x : (Mod.finiteFree S n).X.obj.obj U) :
        (freeIso J ψ n).hom.hom.hom.app U
          ((freeIso J ψ n).inv.hom.hom.app U x) = x :=
      congrArg (fun f : Mod.finiteFree S n ⟶ Mod.finiteFree S n ↦ f.hom.hom.app U x)
        (freeIso J ψ n).inv_hom_id
    rw [he, map_sum]
    apply (coords J S n U).injective
    rw [(coords J S n U).apply_symm_apply, map_sum]
    ext i
    simp only [Finset.sum_apply, freeIso_tmul, AddEquiv.apply_symm_apply]
    rw [Finset.sum_eq_single i]
    · simp [section_map_one]
    · intro j _ hji
      simp [Pi.single_eq_of_ne (Ne.symm hji)]
    · simp

private lemma freeIso_basis
    {R S : Sheaf J AddCommGrpCat.{u}} [MonObj R] [IsCommMonObj R]
    [MonObj S] [IsCommMonObj S] (ψ : R ⟶ S) [IsMonHom ψ]
    (n : ℕ) (U : Cᵒᵖ) (j : Fin n) :
    (freeIso J ψ n).inv.hom.hom.app U
      ((coords J S n U).symm (Pi.single j 1)) =
      (Mod.extendUnitHom ψ (Mod.finiteFree R n)).hom.app U
        ((coords J R n U).symm (Pi.single j 1)) := by
  classical
  with_unfolding_all
    have he (x : (Mod.finiteFree S n).X.obj.obj U) :
        (freeIso J ψ n).hom.hom.hom.app U
          ((freeIso J ψ n).inv.hom.hom.app U x) = x :=
      congrArg (fun f : Mod.finiteFree S n ⟶ Mod.finiteFree S n ↦ f.hom.hom.app U x)
        (freeIso J ψ n).inv_hom_id
    have hh : (freeIso J ψ n).hom.hom.hom.app U
        ((Mod.extendUnitHom ψ (Mod.finiteFree R n)).hom.app U
          ((coords J R n U).symm (Pi.single j 1))) =
        (coords J S n U).symm (Pi.single j 1) := by
      apply (coords J S n U).injective
      ext i
      rw [freeIso_unit, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
      by_cases h : j = i
      · subst i
        simp [section_map_one]
      · simp [Pi.single_eq_of_ne (Ne.symm h)]
    have h := congrArg ((freeIso J ψ n).inv.hom.hom.app U) hh
    have hh' (x : ((Mod.extendScalars ψ).obj (Mod.finiteFree R n)).X.obj.obj U) :
        (freeIso J ψ n).inv.hom.hom.app U
          ((freeIso J ψ n).hom.hom.hom.app U x) = x :=
      congrArg (fun f : (Mod.extendScalars ψ).obj (Mod.finiteFree R n) ⟶
          (Mod.extendScalars ψ).obj (Mod.finiteFree R n) ↦ f.hom.hom.app U x)
        (freeIso J ψ n).hom_inv_id
    rw [hh'] at h
    exact h.symm

private lemma freeIso_matrix
    (one : C) (hOne : IsTerminal one)
    {R S : Sheaf J AddCommGrpCat.{u}} [MonObj R] [IsCommMonObj R]
    [MonObj S] [IsCommMonObj S] (ψ : R ⟶ S) [IsMonHom ψ]
    (m n : ℕ) (f : Mod.finiteFree R n ⟶ Mod.finiteFree R m) :
    matrices J one hOne S m n
      ((freeIso J ψ n).inv ≫ (Mod.extendScalars ψ).map f ≫ (freeIso J ψ m).hom) =
      (matrices J one hOne R m n f).map (ψ.hom.app (.op one)) := by
  ext i j
  rw [matrices_basis]
  change coords J S m (.op one)
    ((freeIso J ψ m).hom.hom.hom.app (.op one)
      (((Mod.extendScalars ψ).map f).hom.hom.app (.op one)
        ((freeIso J ψ n).inv.hom.hom.app (.op one) _))) i = _
  rw [freeIso_basis]
  have h := congrArg (fun k ↦ k.hom.app (.op one)
      ((coords J R n (.op one)).symm (Pi.single j 1)))
    (extension_unit_natural J ψ f)
  change ((Mod.extendScalars ψ).map f).hom.hom.app (.op one)
      ((Mod.extendUnitHom ψ (Mod.finiteFree R n)).hom.app (.op one) _) =
    (Mod.extendUnitHom ψ (Mod.finiteFree R m)).hom.app (.op one)
      (f.hom.hom.app (.op one) _) at h
  rw [h, freeIso_unit]
  rw [Matrix.map_apply, matrices_basis]

/-- Global-section matrices and ordinary internal scalar extension, with every map
normalized on local sections, standard bases, and the coefficient unit.

Source: Stacks Project, Tag 03EK, section-tensor-product, explicit finite-basis and
balanced-map calculation; Hemo–Richarz–Scholbach Example 3.1, p. 6, is context.
(blueprint: lem-sfb-ringed-site-free-matrix-scalar-extension).

Proof following the DAG:
1. The sectionModuleEquivalence of def-weil-pbc-internal-abelian-sheaf-module-equivalence
keeps underlying section groups and restrictions. Finite tuples glue coordinatewise,
so finite biproducts of regular internal modules have these tuples as their sections.
The coordinate inclusions and projections, and a = sum a_j e_j, give its direct-sum
universal property (sk-def-sfb-module-objects), including the empty tuple.
2. Evaluate a module arrow on global e_j. Naturality along U to one and linearity
force the displayed section formula. Conversely that formula is linear and natural,
and evaluates to the original entries. The two constructions are inverse and additive.
3. Evaluation on e_j gives matrix(g f) = matrix(g) matrix(f), and the identity matrix.
4. By sk-def-sfb-sheaf-tensor and def-weil-pbc-sheafification, the local biadditive map
(b,a) to (b ψ(a_j)) extends to an abelian-sheaf tensor map. The balancing equation
b ψ(r) ψ(a_j) = b ψ(r a_j) factors it through the coequalizer of
sk-def-sfb-change-of-scalars; the first-factor action makes this map S-linear.
5. The inverse sends (b_j) to sum q(b_j tensor e_j). Its first composite is the identity
by summing the coordinates, and it is S-linear and natural on sections.
6. On local tensors its second composite is sum q(b ψ(a_j) tensor e_j) =
sum q(b tensor a_j e_j) = q(b tensor a). Maps out of sheafification are determined
on local pure tensors, then the coequalizer projection cancels. This proves the iso
without asserting that all tensor sections are global sums of pure tensors.
7. The morphism formula of def-sfb-modobj-extension sends q(b tensor a) to
q(b tensor f(a)). Evaluating on e_j and applying the iso gives ψ(t_ij).
The unit of def-sfb-modobj-extend-restrict-adjunction inserts 1 tensor a, hence
becomes (ψ(a_j)) on sections, in particular ψ itself in rank one.
8. At zero rank, tuples, matrices and sums are empty. The free module and its scalar
extension are zero; either zero rank makes both Hom and matrix groups singleton.
The same calculations work for zero coefficient rings, with no flatness assumption.
-/
theorem ringedSiteFreeMatrixScalarExtension
    (one : C) (hOne : IsTerminal one)
    {R S : Sheaf J AddCommGrpCat.{u}} [MonObj R] [IsCommMonObj R]
    [MonObj S] [IsCommMonObj S] (ψ : R ⟶ S) [IsMonHom ψ] :
    ∃ (dR : RingedSiteFreeMatrices J R one hOne)
      (dS : RingedSiteFreeMatrices J S one hOne)
      (θ : ∀ n : ℕ, (Mod.extendScalars ψ).obj (Mod.finiteFree R n) ≅
        Mod.finiteFree S n),
      (∀ (n : ℕ) (U : Cᵒᵖ) (b : (sectionRingSheaf J S).obj.obj U)
          (a : (Mod.finiteFree R n).X.obj.obj U) (j : Fin n),
        dS.coordinates n U (((θ n).hom.hom.hom.app U)
          (ringedSiteExtensionTmul J ψ (Mod.finiteFree R n) U b a)) j =
          b * @id ((sectionRingSheaf J S).obj.obj U)
            ((ψ.hom.app U) (dR.coordinates n U a j))) ∧
      (∀ (n : ℕ) (U : Cᵒᵖ) (b : Fin n → (sectionRingSheaf J S).obj.obj U),
        (((θ n).inv.hom.hom.app U) ((dS.coordinates n U).symm b)) =
          ∑ j : Fin n, ringedSiteExtensionTmul J ψ (Mod.finiteFree R n) U
            (b j) ((dR.coordinates n U).symm (Pi.single j 1))) ∧
      (∀ (m n : ℕ) (f : Mod.finiteFree R n ⟶ Mod.finiteFree R m),
        dS.matrix m n ((θ n).inv ≫ (Mod.extendScalars ψ).map f ≫ (θ m).hom) =
          (dR.matrix m n f).map (ψ.hom.app (.op one))) ∧
      (∀ (n : ℕ) (U : Cᵒᵖ) (a : (Mod.finiteFree R n).X.obj.obj U)
          (j : Fin n),
        dS.coordinates n U (((θ n).hom.hom.hom.app U)
          (((Mod.extendUnitHom ψ (Mod.finiteFree R n)).hom.app U) a)) j =
          (ψ.hom.app U) (dR.coordinates n U a j)) ∧
      IsZero (Mod.finiteFree R 0) ∧
      IsZero (Mod.finiteFree S 0) ∧
      IsZero ((Mod.extendScalars ψ).obj (Mod.finiteFree R 0)) := by
  refine ⟨matrixData J one hOne R, matrixData J one hOne S, freeIso J ψ,
    freeIso_tmul J ψ, freeIso_inv J ψ, freeIso_matrix J one hOne ψ,
    freeIso_unit J ψ, free_zero J R, free_zero J S, ?_⟩
  exact (free_zero J S).of_iso (freeIso J ψ 0)

end CategoryTheory.InternalAbelianSheafModule
