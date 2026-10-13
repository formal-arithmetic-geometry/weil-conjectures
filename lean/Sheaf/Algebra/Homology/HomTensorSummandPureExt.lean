/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.Algebra.Homology.HomTensorDegreewise
import Sheaf.Algebra.Homology.HomTensorLocalizedExt

/-!
# Pure-tensor extensionality for one internal Hom

Source: Stacks Project, Modules on Sites, Section 03EK and Lemma 03EO.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})

set_option hygiene false in
set_option quotPrecheck false in
local notation "Mod" => SheafOfModules.{max u v}
  ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)

private def constantGradedComplex (A : Mod) : CochainComplex Mod ℤ where
  X _ := A
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := Limits.zero_comp

set_option synthInstance.maxSize 256 in
/-- Maps into the internal Hom from a tensor are determined on localized pure tensors.
Source: Stacks Project, Modules on Sites, Section 03EK and Lemma 03EO.
(blueprint: lem-sc-hom-tensor-summand-pure-ext).

Proof: Put A and B in every degree of two zero-differential complexes K and L.
The coproduct universal property gives a codiagonal π from the degree-zero
term of their tensor total complex to A tensor B; its composite with every
summand inclusion is the identity. Precompose the argument of a and b with
π, obtaining maps into internal Hom from this total term. Apply the existing
localized tensor extensionality theorem: on every pure tensor in every
summand the codiagonal identity reduces its hypothesis to the hypothesis
here. Finally precompose the arguments with the (0,0) summand inclusion.
Functoriality of internal Hom and π after this inclusion being the identity
recover a=b. The construction works for zero modules and an empty site;
it does not assert global generation of sections of the sheaf tensor. -/
theorem homTensorSummandPure_ext (A B N X : Mod) :
    letI := SheafOfModules.monoidalCategory R
    ∀ (a b : X ⟶ SheafOfModules.homObj (R := R) (A ⊗ B) N),
    (∀ (U : Cᵒᵖ) (s : X.val.obj U) (W : (Over U.unop)ᵒᵖ)
      (x : A.val.obj (op W.unop.left)) (y : B.val.obj (op W.unop.left)),
      (((a.val.app U).hom s).app W).hom
        (((homTensorSectionMap R A B).app (op W.unop.left)).hom
          (x ⊗ₜ[R.obj.obj (op W.unop.left)] y)) =
      (((b.val.app U).hom s).app W).hom
        (((homTensorSectionMap R A B).app (op W.unop.left)).hom
          (x ⊗ₜ[R.obj.obj (op W.unop.left)] y))) → a = b := by
  let := SheafOfModules.monoidalCategory R
  intro a b hab
  let K := constantGradedComplex R A
  let L := constantGradedComplex R B
  let π : (CochainComplex.mapBifunctor K L (curriedTensor Mod)).X 0 ⟶ A ⊗ B :=
    HomologicalComplex.mapBifunctorDesc (K₁ := K) (K₂ := L)
      (F := curriedTensor Mod) (c := .up ℤ) (fun _ _ _ => 𝟙 (A ⊗ B))
  have hπ (i j : ℤ) (hij : i + j = 0) :
      CochainComplex.ιMapBifunctor K L (curriedTensor Mod) i j 0 hij ≫ π =
        𝟙 (A ⊗ B) := HomologicalComplex.ι_mapBifunctorDesc _ _ _ _
  have heq : a ≫ SheafOfModules.homObjMap (R := R) π (𝟙 N) =
      b ≫ SheafOfModules.homObjMap (R := R) π (𝟙 N) := by
    apply homTensorLocalized_ext R K L N X 0
    intro U s W i j hij x y
    have hz := congrArg (fun f : A ⊗ B ⟶ A ⊗ B =>
      (f.val.app (op W.unop.left)).hom
        (((homTensorSectionMap R A B).app (op W.unop.left)).hom
          (x ⊗ₜ[R.obj.obj (op W.unop.left)] y))) (hπ i j hij)
    change (π.val.app (op W.unop.left)).hom
      (((CochainComplex.ιMapBifunctor K L (curriedTensor Mod)
        i j 0 hij).val.app (op W.unop.left)).hom
          (((homTensorSectionMap R A B).app (op W.unop.left)).hom
            (x ⊗ₜ[R.obj.obj (op W.unop.left)] y))) = _ at hz
    change (((a.val.app U).hom s).app W).hom
      ((π.val.app (op W.unop.left)).hom
        (((CochainComplex.ιMapBifunctor K L (curriedTensor Mod)
          i j 0 hij).val.app (op W.unop.left)).hom
            (((homTensorSectionMap R A B).app (op W.unop.left)).hom
              (x ⊗ₜ[R.obj.obj (op W.unop.left)] y)))) =
      (((b.val.app U).hom s).app W).hom
        ((π.val.app (op W.unop.left)).hom
          (((CochainComplex.ιMapBifunctor K L (curriedTensor Mod)
            i j 0 hij).val.app (op W.unop.left)).hom
              (((homTensorSectionMap R A B).app (op W.unop.left)).hom
                (x ⊗ₜ[R.obj.obj (op W.unop.left)] y))))
    rw [hz]
    exact hab U s W x y
  have hh := congrArg
    (fun f => f ≫ SheafOfModules.homObjMap (R := R)
      (CochainComplex.ιMapBifunctor K L (curriedTensor Mod) 0 0 0 (by omega)) (𝟙 N)) heq
  simpa only [Category.assoc, SheafOfModules.homObjMap_comp_homObjMap,
    hπ, Category.id_comp, SheafOfModules.homObjMap_id, Category.comp_id] using hh

end CategoryTheory
