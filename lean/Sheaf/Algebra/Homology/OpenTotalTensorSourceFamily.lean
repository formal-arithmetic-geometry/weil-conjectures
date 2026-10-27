module

public import Sheaf.Algebra.Homology.OpenTotalTensorCoefficientNormalization
import Sheaf.CategoryTheory.SliceNormalizedTensorTransport
import Sheaf.SecSmoothPurity.ModuleTensorGenerators

/-! # Strict coefficient source diagram

Source: Stacks Project, Modules on Sites, Tag 0E8I, and Cohomology on Sites,
Tag 0GL1; agent coefficient refinement
(blueprint: lem-sf-open-total-source-coefficient-family).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


attribute [local irreducible] SheafOfModules.monoidalCategory

universe c v r
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open SheafOfModules.LocalizedStrictTensor
namespace SheafOfModules.OpenTotalTensorCoefficient

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r}) (V : C)
  [HasSheafify (J.over V) AddCommGrpCat.{max c v r}]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

private theorem tensor_second (M N N' : Modules.{c, v, r} R) (a : N ⟶ N')
    (W : Cᵒᵖ) (x : M.val.obj W) (y : N.val.obj W) :
    ((curriedTensor (Modules.{c, v, r} R)).obj M |>.map a).val.app W
      (LocalizedStrictTensor.pure.{c, v, r} R M N W x y) =
      LocalizedStrictTensor.pure.{c, v, r} R M N' W x (a.val.app W y) := by
  have h := CategoryTheory.CochainPullback.moduleTmul_map (𝟙 M) a W x y
  rw [id_tensorHom] at h
  exact h

omit [HasSheafify (J.over V) AddCommGrpCat.{max c v r}]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
/-- Scalar extension of the fixed source total complex forms a strict diagram.
Source: Stacks Modules on Sites, Tags 03CY, 03EK and 03EL; agent coefficient
refinement of step 6 of the interchange argument.
(blueprint: lem-sf-open-total-source-coefficient-family).

Proof: use the normalized isomorphism from tensor with the underlying algebra
module to scalar extension followed by restriction. Compose algebraModules with
the flipped curried tensor functor and apply the resulting functors and natural
transformations degreewise to the fixed source total complex M. Naturality gives
chain maps; functoriality gives their identity and composition laws. The normalized
isomorphisms commute with the differential and give complex isomorphisms.
Conjugate the diagram maps by these isomorphisms; cancellation proves the strict
laws. On a pure tensor the middle map sends z tensor s to z tensor h(s), and the
normalization identifies these with actual scalar-extension generators. Insert
z=[x]_f tensor y. No target projection comparison is used. -/
theorem sourceCoefficientFamily_exists
    (Q : Complex.{max c v, v, r} (R.over V)) (F : Complex.{c, v, r} R) :
    ∃ D : StrictFamily.{c, v, r} R (fun A ↦ source.{c, v, r} R V A Q F),
      ∀ {A B : Under R} (a : A ⟶ B)
        (p q n : ℤ) (h : p + q = n) (W : C) (f : W ⟶ V)
        (x : (Q.X p).val.obj (op (Over.mk f))) (y : (F.X q).val.obj (op W))
        (s : A.right.obj.obj (op W)),
        (((D.map a).f n).val.app (op W))
            (sourceSection.{c, v, r} R V A Q F p q n h W f x y s) =
          sourceSection.{c, v, r} R V B Q F p q n h W f x y
            (a.right.hom.app (op W) s) := by
  classical
  obtain ⟨t, ht⟩ := SliceTensorGenerator.tensorTransport_exists.{c, v, r} R
  let M := extendedTotal.{c, v, r} R V Q F
  let K := algebraModules.{c, v, r} R ⋙ (curriedTensor (Modules.{c, v, r} R)).flip
  let : ∀ A, (K.obj A).PreservesZeroMorphisms := fun A ↦
    inferInstanceAs (tensorRight (algebraModule.{c, v, r} R A)).PreservesZeroMorphisms
  let Y := fun A : Under R ↦ ((K.obj A).mapHomologicalComplex (.up ℤ)).obj M
  let j : ∀ A : Under R, Y A ≅ (forget.{c, v, r} A.hom).obj (source.{c, v, r} R V A Q F) := fun A ↦
    HomologicalComplex.Hom.isoOfComponents (fun n ↦ (t A).app (M.X n))
      (fun n k _ ↦ ((t A).hom.naturality (M.d n k)).symm)
  let u := fun {A B : Under R} (a : A ⟶ B) ↦
    (NatTrans.mapHomologicalComplex (K.map a) (.up ℤ)).app M
  have uid : ∀ A, u (𝟙 A) = 𝟙 _ := by
    intro A
    dsimp only [u]
    rw [K.map_id, NatTrans.mapHomologicalComplex_id]
    rfl
  have ucomp : ∀ {A B D : Under R} (a : A ⟶ B) (b : B ⟶ D),
      u (a ≫ b) = u a ≫ u b := by
    intro A B D a b
    dsimp only [u]
    rw [K.map_comp, NatTrans.mapHomologicalComplex_comp]
    rfl
  let D : StrictFamily.{c, v, r} R (fun A ↦ source.{c, v, r} R V A Q F) :=
    { map := fun {A B} a ↦ (j A).inv ≫ u a ≫ (j B).hom
      map_id := fun A ↦ by
        change (j A).inv ≫ u (𝟙 A) ≫ (j A).hom = 𝟙 _
        rw [uid]
        exact (congrArg (fun f ↦ (j A).inv ≫ f) (Category.id_comp (j A).hom)).trans
          (j A).inv_hom_id
      map_comp := fun a b ↦ by
        simp only [ucomp, Category.assoc, Iso.hom_inv_id_assoc] }
  refine ⟨D, ?_⟩
  intro A B a p q n h W f x y s
  let z := totalSection.{c, v, r} R ((extension.{c, v, r} R V).obj Q) F p q n h (op W)
    (extensionSection.{c, v, r} R V (Q.X p) W f x) y
  have hval : ∀ A (b : A.right.obj.obj (op W)),
      (((j A).hom.f n).val.app (op W))
        (LocalizedStrictTensor.pure.{c, v, r} R (M.X n) _ (op W) z b) =
        sourceSection.{c, v, r} R V A Q F p q n h W f x y b := fun A b ↦ ht A (M.X n) (op W) z b
  have hinv : (((j A).inv.f n).val.app (op W))
      (sourceSection.{c, v, r} R V A Q F p q n h W f x y s) =
      LocalizedStrictTensor.pure.{c, v, r} R (M.X n) _ (op W) z s := by
    rw [← hval A s]
    exact congrArg (fun k ↦ (k.f n).val.app (op W)
      (LocalizedStrictTensor.pure.{c, v, r} R (M.X n) _ (op W) z s))
      (j A).hom_inv_id
  change (((j B).hom.f n).val.app (op W))
    (((u a).f n).val.app (op W)
      ((((j A).inv.f n).val.app (op W)) (sourceSection.{c, v, r} R V A Q F p q n h W f x y s))) = _
  rw [hinv]
  have hu := tensor_second.{c, v, r} R (M.X n) _ _ ((algebraModules.{c, v, r} R).map a) (op W) z s
  change (((u a).f n).val.app (op W))
      (LocalizedStrictTensor.pure.{c, v, r} R (M.X n) _ (op W) z s) =
    LocalizedStrictTensor.pure.{c, v, r} R (M.X n) _ (op W) z (a.right.hom.app (op W) s) at hu
  rw [hu, hval]


end SheafOfModules.OpenTotalTensorCoefficient
