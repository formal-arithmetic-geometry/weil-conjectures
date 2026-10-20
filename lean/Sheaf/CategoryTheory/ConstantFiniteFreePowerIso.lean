/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M8
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs

import Sheaf.CategoryTheory.ConstantFiniteFreeSectionBasis
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Finite-basis coordinates for constant scalar extension

Source: Stacks 03EK and the finite-dual-basis calculation in step 6 of
`lem-pur-compact-support-roos-cofinality`.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe uC vC r

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

namespace CategoryTheory

private noncomputable def basisTensorEquiv
    {R S M : Type r} [CommRing R] [AddCommGroup S] [Module R S]
    [AddCommGroup M] [Module R M] (n : ℕ) (b : Module.Basis (Fin n) R S) :
    S ⊗[R] M ≃ₗ[R] (Fin n → M) :=
  (b.equivFun.rTensor M).trans
    ((TensorProduct.comm R (Fin n → R) M).trans
      (TensorProduct.piScalarRight R R M (Fin n)))
private theorem basisTensorEquiv_tmul
    {R S M : Type r} [CommRing R] [AddCommGroup S] [Module R S]
    [AddCommGroup M] [Module R M] (n : ℕ) (b : Module.Basis (Fin n) R S)
    (s : S) (m : M) (i : Fin n) :
    basisTensorEquiv n b (s ⊗ₜ[R] m) i = b.equivFun s i • m := by
  simp [basisTensorEquiv]

section

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}} (α : R ⟶ S)

variable (n : ℕ)
  (b : ∀ U : Cᵒᵖ,
    @Module.Basis (Fin n) (R.obj.obj U) (S.obj.obj U) _ _
      (Module.compHom _ (α.hom.app U).hom))
  (hb : ∀ (U V : Cᵒᵖ) (f : U ⟶ V) (s : S.obj.obj U) (i : Fin n),
    let : Module (R.obj.obj U) (S.obj.obj U) := Module.compHom _ (α.hom.app U).hom
    letI : Module (R.obj.obj V) (S.obj.obj V) := Module.compHom _ (α.hom.app V).hom
    (b V).equivFun (S.obj.map f s) i =
      R.obj.map f ((b U).equivFun s i))

private noncomputable def tensorCoordinate
    (n : ℕ)
    (b : ∀ U : Cᵒᵖ, @Module.Basis (Fin n) (R.obj.obj U) (S.obj.obj U) _ _
      (Module.compHom _ (α.hom.app U).hom))
    (hb : ∀ (U V : Cᵒᵖ) (f : U ⟶ V) (s : S.obj.obj U) (i : Fin n),
      let : Module (R.obj.obj U) (S.obj.obj U) := Module.compHom _ (α.hom.app U).hom
      letI : Module (R.obj.obj V) (S.obj.obj V) := Module.compHom _ (α.hom.app V).hom
      (b V).equivFun (S.obj.map f s) i = R.obj.map f ((b U).equivFun s i))
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (i : Fin n) :
    (SheafOfModules.changeOfRingsPresheafOfUniverses α M).presheaf ⟶ M.val.presheaf := by
  letI (U : Cᵒᵖ) : Module (R.obj.obj U) (S.obj.obj U) :=
    Module.compHom _ (α.hom.app U).hom
  refine { app := fun U ↦ ?_, naturality := ?_ }
  · exact AddCommGrpCat.ofHom
      { toFun := fun z ↦ basisTensorEquiv n (b U) z i
        map_zero' := by simp
        map_add' := by intro x y; simp }
  · intro U V f
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simpa using congrArg₂ (· + ·) hz hw
    | tmul s m =>
      change basisTensorEquiv n (b V)
          (SheafOfModules.changeOfRingsMapOfUniverses α M f
            (s ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] m)) i =
        M.val.map f (basisTensorEquiv n (b U) (s ⊗ₜ[R.obj.obj U] m) i)
      rw [SheafOfModules.changeOfRingsMap_tmulOfUniverses]
      rw [basisTensorEquiv_tmul, basisTensorEquiv_tmul, M.val.map_smul, hb]
      rfl

private noncomputable def tensorProductHom
    (n : ℕ) (b : ∀ U : Cᵒᵖ, @Module.Basis (Fin n) (R.obj.obj U) (S.obj.obj U) _ _
      (Module.compHom _ (α.hom.app U).hom))
    (hb : ∀ (U V : Cᵒᵖ) (f : U ⟶ V) (s : S.obj.obj U) (i : Fin n),
      let : Module (R.obj.obj U) (S.obj.obj U) := Module.compHom _ (α.hom.app U).hom
      letI : Module (R.obj.obj V) (S.obj.obj V) := Module.compHom _ (α.hom.app V).hom
      (b V).equivFun (S.obj.map f s) i = R.obj.map f ((b U).equivFun s i))
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (SheafOfModules.changeOfRingsPresheafOfUniverses α M).presheaf ⟶
      ∏ᶜ (fun _ : Fin n ↦ M.val.presheaf) :=
  Pi.lift (fun i ↦ tensorCoordinate α n b hb M i)

private noncomputable def tensorProductInvApp
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) :
    (∏ᶜ (fun _ : Fin n ↦ M.val.presheaf)).obj U ⟶
      (SheafOfModules.changeOfRingsPresheafOfUniverses α M).presheaf.obj U := by
  let : Module (R.obj.obj U) (S.obj.obj U) := Module.compHom _ (α.hom.app U).hom
  exact AddCommGrpCat.ofHom
    { toFun := fun z ↦ (basisTensorEquiv (M := M.val.obj U) n (b U)).symm
        (fun i ↦ (Pi.π (fun _ : Fin n ↦ M.val.presheaf) i).app U z)
      map_zero' := by
        have hz : (fun i ↦ (Pi.π (fun _ : Fin n ↦ M.val.presheaf) i).app U 0) =
            (0 : Fin n → M.val.obj U) := by
          funext i
          exact ((Pi.π (fun _ : Fin n ↦ M.val.presheaf) i).app U).hom.map_zero
        rw [hz]
        exact map_zero _
      map_add' := by
        intro x y
        have ha :
            (fun i ↦ (Pi.π (fun _ : Fin n ↦ M.val.presheaf) i).app U (x + y)) =
              (fun i ↦ (Pi.π (fun _ : Fin n ↦ M.val.presheaf) i).app U x) +
              (fun i ↦ (Pi.π (fun _ : Fin n ↦ M.val.presheaf) i).app U y) := by
          funext i
          exact ((Pi.π (fun _ : Fin n ↦ M.val.presheaf) i).app U).hom.map_add x y
        rw [ha]
        exact map_add _ _ _ }

private noncomputable def tensorProductIso
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (SheafOfModules.changeOfRingsPresheafOfUniverses α M).presheaf ≅
      ∏ᶜ (fun _ : Fin n ↦ M.val.presheaf) := by
  have (U : Cᵒᵖ) : IsIso ((tensorProductHom α n b hb M).app U) := by
    refine ⟨⟨tensorProductInvApp α n b M U, ?_, ?_⟩⟩
    · ext z
      let : Module (R.obj.obj U) (S.obj.obj U) := Module.compHom _ (α.hom.app U).hom
      change (basisTensorEquiv (M := M.val.obj U) n (b U)).symm
        (fun i ↦ (Pi.π (fun _ : Fin n ↦ M.val.presheaf) i).app U
          ((tensorProductHom α n b hb M).app U z)) = z
      have hcoord (i : Fin n) :
          (Pi.π (fun _ : Fin n ↦ M.val.presheaf) i).app U
            ((tensorProductHom α n b hb M).app U z) =
              basisTensorEquiv (M := M.val.obj U) n (b U) z i := by
        exact ConcreteCategory.congr_hom
          (NatTrans.congr_app (Pi.lift_π (fun i ↦ tensorCoordinate α n b hb M i) i) U) z
      simp only [hcoord, LinearEquiv.symm_apply_apply]
    · apply (isLimitOfPreserves ((evaluation Cᵒᵖ AddCommGrpCat).obj U)
        (limit.isLimit (Discrete.functor (fun _ : Fin n ↦ M.val.presheaf)))).hom_ext
      intro i
      change (tensorProductInvApp α n b M U ≫ (tensorProductHom α n b hb M).app U) ≫
        (Pi.π (fun _ : Fin n ↦ M.val.presheaf) i.as).app U = _
      rw [Category.assoc, ← NatTrans.comp_app, tensorProductHom, Pi.lift_π]
      ext z
      let : Module (R.obj.obj U) (S.obj.obj U) := Module.compHom _ (α.hom.app U).hom
      change basisTensorEquiv (M := M.val.obj U) n (b U)
        ((basisTensorEquiv (M := M.val.obj U) n (b U)).symm _) i.as = _
      exact congrFun ((basisTensorEquiv (M := M.val.obj U) n (b U)).apply_symm_apply _) i.as
  letI : IsIso (tensorProductHom α n b hb M) := NatIso.isIso_of_isIso_app _
  exact asIso (tensorProductHom α n b hb M)

private noncomputable def tensorProductPresheafMap
    {M N : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : M ⟶ N) :
    (SheafOfModules.changeOfRingsPresheafOfUniverses α M).presheaf ⟶
      (SheafOfModules.changeOfRingsPresheafOfUniverses α N).presheaf :=
  (PresheafOfModules.toPresheaf _).map
    { app := fun U ↦ (ModuleCat.extendScalars (α.hom.app U).hom).map (f.val.app U)
      naturality := SheafOfModules.changeOfRingsHom_naturalityOfUniverses α M f }

private theorem tensorProductIso_naturality
    {M N : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : M ⟶ N) :
    tensorProductPresheafMap α f ≫ (tensorProductIso α n b hb N).hom =
      (tensorProductIso α n b hb M).hom ≫
        Limits.Pi.map (f := fun _ : Fin n ↦ M.val.presheaf)
          (g := fun _ : Fin n ↦ N.val.presheaf)
          (fun _ ↦ (PresheafOfModules.toPresheaf _).map f.val) := by
  change tensorProductPresheafMap α f ≫ tensorProductHom α n b hb N =
    tensorProductHom α n b hb M ≫ _
  apply Pi.hom_ext
  intro i
  simp only [tensorProductHom, Category.assoc, Pi.map_π, Pi.lift_π, Pi.lift_π_assoc]
  ext U z
  let : Module (R.obj.obj U) (S.obj.obj U) := Module.compHom _ (α.hom.app U).hom
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simpa using congrArg₂ (· + ·) hz hw
  | tmul s m =>
    change basisTensorEquiv (M := N.val.obj U) n (b U)
      ((ModuleCat.extendScalars (α.hom.app U).hom).map (f.val.app U)
        (s ⊗ₜ[R.obj.obj U] m)) i =
      (f.val.app U) (basisTensorEquiv (M := M.val.obj U) n (b U)
        (s ⊗ₜ[R.obj.obj U] m) i)
    erw [ModuleCat.ExtendScalars.map_tmul]
    rw [basisTensorEquiv_tmul, basisTensorEquiv_tmul]
    exact ((f.val.app U).hom.map_smul _ _).symm

omit [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}] in
private theorem power_isSheaf
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    Presheaf.IsSheaf J (∏ᶜ (fun _ : Fin n ↦ M.val.presheaf)) := by
  exact Sheaf.isSheaf_of_isLimit
    (Discrete.functor (fun _ : Fin n ↦ (SheafOfModules.toSheaf _).obj M))
    (limit.cone _) (limit.isLimit _)

private noncomputable def sheafifiedTensorIso
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (SheafOfModules.changeOfRingsOfUniverses α M).val.presheaf ≅
      ∏ᶜ (fun _ : Fin n ↦ M.val.presheaf) :=
  (sheafification J AddCommGrpCat).mapIso (tensorProductIso α n b hb M) ≪≫
    (isoSheafify J (power_isSheaf n M)).symm

private theorem sheafifiedTensorIso_naturality
    {M N : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : M ⟶ N) :
    (PresheafOfModules.toPresheaf _).map
        (SheafOfModules.changeOfRingsHomOfUniverses α M f).val ≫
        (sheafifiedTensorIso α n b hb N).hom =
      (sheafifiedTensorIso α n b hb M).hom ≫
        Limits.Pi.map (f := fun _ : Fin n ↦ M.val.presheaf)
          (g := fun _ : Fin n ↦ N.val.presheaf)
          (fun _ ↦ (PresheafOfModules.toPresheaf _).map f.val) := by
  change sheafifyMap J (tensorProductPresheafMap α f) ≫
    sheafifyMap J (tensorProductIso α n b hb N).hom ≫ _ =
    (sheafifyMap J (tensorProductIso α n b hb M).hom ≫ _) ≫ _
  rw [← Category.assoc, ← sheafifyMap_comp, tensorProductIso_naturality,
    sheafifyMap_comp, Category.assoc, Category.assoc]
  congr 1
  apply (cancel_mono (isoSheafify J (power_isSheaf n N)).hom).mp
  simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change sheafifyMap J _ = (isoSheafify J (power_isSheaf n M)).inv ≫ _ ≫ _
  apply (cancel_epi (isoSheafify J (power_isSheaf n M)).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  exact (toSheafify_naturality J
    (Limits.Pi.map (f := fun _ : Fin n ↦ M.val.presheaf)
      (g := fun _ : Fin n ↦ N.val.presheaf)
      (fun _ ↦ (PresheafOfModules.toPresheaf _).map f.val))).symm


end


/-- After forgetting to abelian presheaves, finite-free constant scalar extension is
naturally a finite power. This statement contains no product-preservation assertion.

Source: Stacks 03EK, tensor sheafification; the finite-dual-basis calculation of
step 6 of `lem-pur-compact-support-roos-cofinality`.
(blueprint: lem-pur-constant-finite-free-power-iso)

Proof: Choose a finite A-basis b_i of B with its coordinate A-linear maps lambda_i.
The associated constant module sheaves inherit the inverse maps
b -> (lambda_i(b)) and (a_i) -> sum_i a_i b_i. These maps are first defined on
constant presheaves, where the basis expansion and the coordinate identities are
the original identities of A-modules; applying associated sheafification preserves
them. The resulting sheaf maps identify the sheafified B, as an A-module, with a
finite power of the sheafified A. This does not identify sections of a constant
sheaf with constant elements.

For a module sheaf M, extend these maps through the balanced tensor universal
property: a local pure tensor b tensor m is sent to (lambda_i(b) m)_i, with inverse
(m_i) -> sum_i b_i tensor m_i. The sheaf coordinate maps here are linear over the
sheafified A, so balancing holds. The two composites are identities by the basis
expansion and the coordinate identities, checked locally on pure tensors and
then descended through module sheafification. The finite power of M is already
a sheaf, and sheafification preserves finite products, so the result identifies
the actual specified scalar-extension object, including its sheafification.

Both maps commute with restrictions and every morphism M -> N, since such a
morphism commutes with scalar multiplication and finite sums. They therefore form
a natural isomorphism of underlying abelian presheaf functors. The object and map
equalities in the hypotheses transport this isomorphism to F. The categorical
limit of the constant diagram on Fin n is the corresponding finite power, which
gives the displayed codomain. If A is the zero ring then B and all its modules
are zero: use n=0. For nonzero A choose any finite basis; rank zero likewise gives
the zero-module case. No exactness or preservation of infinite products is used. -/
theorem constantFiniteFree_underlyingPowerIso
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [HasSheafify J CommRingCat.{max uC vC r}]
    [J.HasSheafCompose (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})]
    [HasSheafify J AddCommGrpCat.{max uC vC r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
    (A B : CommRingCat.{max uC vC r}) [Algebra A B] [Module.Free A B]
    [Module.Finite A B]
    (F : SheafOfModules.{max uC vC r}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          ((constantSheaf J CommRingCat).obj A)) ⥤
      SheafOfModules.{max uC vC r}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          ((constantSheaf J CommRingCat).obj B)))
    (hobj : ∀ M, F.obj M = SheafOfModules.changeOfRingsOfUniverses
      ((constantSheaf J CommRingCat).map (CommRingCat.ofHom (algebraMap A B))) M)
    (hmap : ∀ M N (f : M ⟶ N), HEq (F.map f)
      (SheafOfModules.changeOfRingsHomOfUniverses
        ((constantSheaf J CommRingCat).map (CommRingCat.ofHom (algebraMap A B))) M f)) :
    ∃ n : ℕ, Nonempty
      (F ⋙ SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _ ≅
        (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _) ⋙
          Functor.const (Discrete (Fin n)) ⋙ lim) := by
  let R := (constantSheaf J CommRingCat).obj A
  let S := (constantSheaf J CommRingCat).obj B
  let α : R ⟶ S :=
    (constantSheaf J CommRingCat).map (CommRingCat.ofHom (algebraMap A B))
  obtain ⟨n, b, hb⟩ := constantFiniteFree_sectionBasis.{uC, vC, r} J A B
  let U := SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj
  have hF {M N} (f : M ⟶ N) :
      F.map f ≫ (eqToIso (hobj N)).hom =
        (eqToIso (hobj M)).hom ≫ SheafOfModules.changeOfRingsHomOfUniverses α M f := by
    apply (cancel_mono (eqToIso (hobj N)).inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact (conj_eqToHom_iff_heq _ _ (hobj M) (hobj N)).2 (hmap M N f)
  refine ⟨n, ⟨NatIso.ofComponents (fun M ↦ ?_) ?_⟩⟩
  · exact U.mapIso (eqToIso (hobj M)) ≪≫ sheafifiedTensorIso α n b hb M ≪≫
      Pi.isoLimit ((Functor.const (Discrete (Fin n))).obj M.val.presheaf)
  · intro M N f
    dsimp only [Iso.trans_hom]
    simp only [Category.assoc]
    change U.map (F.map f) ≫ U.map (eqToIso (hobj N)).hom ≫ _ =
      U.map (eqToIso (hobj M)).hom ≫ _
    rw [← Category.assoc, ← U.map_comp, hF, U.map_comp, Category.assoc]
    have hn := sheafifiedTensorIso_naturality α n b hb f
    change U.map (SheafOfModules.changeOfRingsHomOfUniverses α M f) ≫
      (sheafifiedTensorIso α n b hb N).hom = _ at hn
    rw [reassoc_of% hn]
    congr 1
    congr 1
    apply limit.hom_ext
    rintro ⟨i⟩
    change
      Limits.Pi.map (f := fun _ : Fin n ↦ M.val.presheaf)
          (g := fun _ : Fin n ↦ N.val.presheaf)
          (fun _ ↦ (PresheafOfModules.toPresheaf _).map f.val) ≫
        (Pi.isoLimit ((Functor.const (Discrete (Fin n))).obj N.val.presheaf)).hom ≫
          limit.π ((Functor.const (Discrete (Fin n))).obj N.val.presheaf) ⟨i⟩ =
      (Pi.isoLimit ((Functor.const (Discrete (Fin n))).obj M.val.presheaf)).hom ≫
        limMap ((Functor.const (Discrete (Fin n))).map
          ((PresheafOfModules.toPresheaf _).map f.val)) ≫
          limit.π ((Functor.const (Discrete (Fin n))).obj N.val.presheaf) ⟨i⟩
    rw [Pi.isoLimit_hom_π]
    conv_rhs => erw [limMap_π]
    rw [Pi.isoLimit_hom_π_assoc]
    exact Pi.map_π _ _

end CategoryTheory
