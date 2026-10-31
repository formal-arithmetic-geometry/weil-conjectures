/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
import all WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement

/-! Ordinary tensor transport for a prescribed section/scalar realization.

Source: Stacks, Modules on Sites, Tag 03EK. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.OpenTensorNormalization

namespace TensorOrdinary
variable {A : Type (u + 1)} [CommRing A] {X : Scheme.{u}}
  {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
  {i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
  (e : FiniteRealization A X R i)

private def sections (M : FiniteModules A X) (W : X.ProEtᵒᵖ) :
    (e.equivalence.functor.obj M).val.obj W ≃+ M.obj.obj W :=
  { toFun := (e.underlying.hom.app M).hom.app W
    invFun := (e.underlying.inv.app M).hom.app W
    left_inv := fun x ↦ ConcreteCategory.congr_hom (congr_app
      (congrArg (sheafToPresheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).map
        (e.underlying.hom_inv_id_app M)) W) x
    right_inv := fun x ↦ ConcreteCategory.congr_hom (congr_app
      (congrArg (sheafToPresheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).map
        (e.underlying.inv_hom_id_app M)) W) x
    map_add' := map_add _ }

private theorem sections_scalar (M : FiniteModules A X) (W : X.ProEtᵒᵖ)
    (a : A) (x : (e.equivalence.functor.obj M).val.obj W) :
    sections e M W (i.app W a • x) = a • sections e M W x := e.scalar M W a x

private theorem sections_inv_scalar (M : FiniteModules A X) (W : X.ProEtᵒᵖ)
    (a : A) (x : M.obj.obj W) :
    (sections e M W).symm (a • x) = i.app W a • (sections e M W).symm x := by
  apply (sections e M W).injective
  rw [AddEquiv.apply_symm_apply, sections_scalar, AddEquiv.apply_symm_apply]

private theorem sections_restrict (M : FiniteModules A X) {W V : X.ProEtᵒᵖ}
    (f : W ⟶ V) (x : (e.equivalence.functor.obj M).val.obj W) :
    sections e M V ((e.equivalence.functor.obj M).val.map f x) =
      M.obj.map f (sections e M W x) :=
  ConcreteCategory.congr_hom ((e.underlying.hom.app M).hom.naturality f) x

private theorem sections_inv_restrict (M : FiniteModules A X) {W V : X.ProEtᵒᵖ}
    (f : W ⟶ V) (x : M.obj.obj W) :
    (sections e M V).symm (M.obj.map f x) =
      (e.equivalence.functor.obj M).val.map f ((sections e M W).symm x) := by
  apply (sections e M V).injective
  rw [AddEquiv.apply_symm_apply, sections_restrict, AddEquiv.apply_symm_apply]

private theorem sections_map {M N : FiniteModules A X} (f : M ⟶ N)
    (W : X.ProEtᵒᵖ) (x : (e.equivalence.functor.obj M).val.obj W) :
    sections e N W ((e.equivalence.functor.map f).val.app W x) =
      f.hom.app W (sections e M W x) :=
  ConcreteCategory.congr_hom (congr_app
    (congrArg (sheafToPresheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).map
      (e.underlying.hom.naturality f)) W) x

private theorem fixed_lift (M N H : FiniteModules A X)
    (b : ∀ W : X.ProEtᵒᵖ, M.obj.obj W →ₗ[A] N.obj.obj W →ₗ[A] H.obj.obj W)
    (hb : ∀ {W V : X.ProEtᵒᵖ} (f : W ⟶ V) (x : M.obj.obj W) (y : N.obj.obj W),
      b V (M.obj.map f x) (N.obj.map f y) = H.obj.map f (b W x y)) :
    ∃ f : M ⊗ N ⟶ H, ∀ W x y,
      f.hom.app W (finitePure M N W x y) = b W x y := by
  let J := ProEt.topology X
  let q : M.obj ⊗ N.obj ⟶ H.obj :=
    { app := fun W ↦ ModuleCat.ofHom (TensorProduct.lift (b W))
      naturality := by
        intro W V f
        apply ModuleCat.MonoidalCategory.tensor_ext
        intro x y
        exact hb f x y }
  let a := ((sheafificationAdjunction J (ModuleCat.{u + 1} A)).homEquiv
    (M.obj ⊗ N.obj) H).symm q
  refine ⟨(sfbSheafTensor_comparison J M N).hom ≫ a, ?_⟩
  intro W x y
  have h := ((sheafificationAdjunction J (ModuleCat.{u + 1} A)).homEquiv
    (M.obj ⊗ N.obj) H).apply_symm_apply q
  rw [Adjunction.homEquiv_unit] at h
  have hh := ConcreteCategory.congr_hom (congr_app h W) (x ⊗ₜ[A] y)
  change a.hom.app W ((sfbSheafTensor_comparison J M N).hom.hom.app W
    ((sfbSheafTensor_comparison J M N).inv.hom.app W
      ((toSheafify J (M.obj ⊗ N.obj)).app W (x ⊗ₜ[A] y)))) = _
  have hi := ConcreteCategory.congr_hom (congr_app
    (congrArg (fun f ↦ f.hom) (sfbSheafTensor_comparison J M N).inv_hom_id) W)
      ((toSheafify J (M.obj ⊗ N.obj)).app W (x ⊗ₜ[A] y))
  change (sfbSheafTensor_comparison J M N).hom.hom.app W
    ((sfbSheafTensor_comparison J M N).inv.hom.app W _) = _ at hi
  rw [hi]
  exact hh

private def backPair (M N : FiniteModules A X) (W : X.ProEtᵒᵖ)
    (x : (e.equivalence.functor.obj M).val.obj W)
    (y : (e.equivalence.functor.obj N).val.obj W) :
    (e.equivalence.functor.obj (M ⊗ N)).val.obj W :=
  (sections e (M ⊗ N) W).symm
    (finitePure M N W (sections e M W x) (sections e N W y))

private theorem backPair_restrict (M N : FiniteModules A X) {W V : X.ProEtᵒᵖ}
    (f : W ⟶ V) (x : (e.equivalence.functor.obj M).val.obj W)
    (y : (e.equivalence.functor.obj N).val.obj W) :
    backPair e M N V ((e.equivalence.functor.obj M).val.map f x)
      ((e.equivalence.functor.obj N).val.map f y) =
    (e.equivalence.functor.obj (M ⊗ N)).val.map f (backPair e M N W x y) := by
  unfold backPair
  rw [sections_restrict, sections_restrict]
  rw [show finitePure M N V (M.obj.map f (sections e M W x))
      (N.obj.map f (sections e N W y)) =
      (M ⊗ N).obj.map f (finitePure M N W (sections e M W x)
        (sections e N W y)) from
    CategoryTheory.ConstantScalarRestriction.fixedPure_naturality
      (ProEt.topology X) A M N f _ _]
  exact sections_inv_restrict e _ f _

private theorem backPair_const_left (M N : FiniteModules A X) (W : X.ProEtᵒᵖ)
    (a : A) (x : (e.equivalence.functor.obj M).val.obj W)
    (y : (e.equivalence.functor.obj N).val.obj W) :
    backPair e M N W (i.app W a • x) y = i.app W a • backPair e M N W x y := by
  unfold backPair
  rw [sections_scalar]
  rw [show finitePure M N W (a • sections e M W x) (sections e N W y) =
      a • finitePure M N W (sections e M W x) (sections e N W y) from
    (CategoryTheory.ConstantScalarRestriction.fixedPairing
      (ProEt.topology X) A M N W).map_smul₂ a _ _]
  exact sections_inv_scalar e _ W a _

private theorem backPair_const_right (M N : FiniteModules A X) (W : X.ProEtᵒᵖ)
    (a : A) (x : (e.equivalence.functor.obj M).val.obj W)
    (y : (e.equivalence.functor.obj N).val.obj W) :
    backPair e M N W x (i.app W a • y) = i.app W a • backPair e M N W x y := by
  unfold backPair
  rw [sections_scalar]
  rw [show finitePure M N W (sections e M W x) (a • sections e N W y) =
      a • finitePure M N W (sections e M W x) (sections e N W y) from
    (CategoryTheory.ConstantScalarRestriction.fixedPairing
      (ProEt.topology X) A M N W _).map_smul a _]
  exact sections_inv_scalar e _ W a _

private theorem local_smul
    [Presheaf.IsLocallySurjective (ProEt.topology X) i]
    (M N H : Mod R)
    (b : ∀ W : X.ProEtᵒᵖ, M.val.obj W → N.val.obj W → H.val.obj W)
    (hb : ∀ {W V : X.ProEtᵒᵖ} (f : W ⟶ V) (x : M.val.obj W) (y : N.val.obj W),
      b V (M.val.map f x) (N.val.map f y) = H.val.map f (b W x y))
    (hc : ∀ W a x y, b W (i.app W a • x) y = i.app W a • b W x y)
    (W : X.ProEtᵒᵖ) (r : R.obj.obj W) (x : M.val.obj W) (y : N.val.obj W) :
    b W (r • x) y = r • b W x y := by
  apply H.isSheaf.isSeparated _ (Presheaf.imageSieve i r)
    (Presheaf.imageSieve_mem (ProEt.topology X) i r)
  rintro V f ⟨a, ha⟩
  change H.val.map f.op (b W (r • x) y) = H.val.map f.op (r • b W x y)
  rw [← hb, H.val.map_smul, M.val.map_smul]
  change b (op V) (R.obj.map f.op r • M.val.map f.op x) (N.val.map f.op y) =
    R.obj.map f.op r • H.val.map f.op (b W x y)
  rw [← ha, ← hb]
  exact hc _ a _ _

private def backBilin [Presheaf.IsLocallySurjective (ProEt.topology X) i]
    (M N : FiniteModules A X) (W : X.ProEtᵒᵖ) :
    (e.equivalence.functor.obj M).val.obj W →ₗ[R.obj.obj W]
      (e.equivalence.functor.obj N).val.obj W →ₗ[R.obj.obj W]
        (e.equivalence.functor.obj (M ⊗ N)).val.obj W :=
  LinearMap.mk₂ _ (backPair e M N W)
    (by
      intro x x' y
      unfold backPair
      rw [map_add]
      rw [show finitePure M N W (sections e M W x + sections e M W x')
          (sections e N W y) = _ from
        (CategoryTheory.ConstantScalarRestriction.fixedPairing
          (ProEt.topology X) A M N W).map_add₂ _ _ _]
      exact map_add _ _ _)
    (by
      intro r x y
      exact local_smul _ _ _ (backPair e M N) (backPair_restrict e M N)
        (backPair_const_left e M N) W r x y)
    (by
      intro x y y'
      unfold backPair
      rw [map_add]
      rw [show finitePure M N W (sections e M W x)
          (sections e N W y + sections e N W y') = _ from
        (CategoryTheory.ConstantScalarRestriction.fixedPairing
          (ProEt.topology X) A M N W _).map_add _ _]
      exact map_add _ _ _)
    (by
      intro r x y
      exact local_smul _ _ _ (fun V y x ↦ backPair e M N V x y)
        (fun f y x ↦ backPair_restrict e M N f x y)
        (fun V a y x ↦ backPair_const_right e M N V a x y) W r y x)

private theorem back_exists [Presheaf.IsLocallySurjective (ProEt.topology X) i]
    (M N : FiniteModules A X) :
    ∃ f : e.equivalence.functor.obj M ⊗ e.equivalence.functor.obj N ⟶
        e.equivalence.functor.obj (M ⊗ N),
      ∀ W x y, f.val.app W (pure R _ _ W x y) = backPair e M N W x y := by
  obtain ⟨f, hf, _⟩ := CochainScalarConstruction.cochain_tensor_bilinear_universal R
    (e.equivalence.functor.obj M) (e.equivalence.functor.obj N)
    (e.equivalence.functor.obj (M ⊗ N)) (backBilin e M N) (backPair_restrict e M N)
  exact ⟨f, hf⟩

private def frontPair (M N H : FiniteModules A X)
    (c : e.equivalence.functor.obj H ≅
      e.equivalence.functor.obj M ⊗ e.equivalence.functor.obj N)
    (W : X.ProEtᵒᵖ) : M.obj.obj W →ₗ[A] N.obj.obj W →ₗ[A] H.obj.obj W :=
  LinearMap.mk₂ A
    (fun x y ↦ sections e H W (c.inv.val.app W
      (CochainScalarConstruction.pure R _ _ W
        ((sections e M W).symm x) ((sections e N W).symm y))))
    (by
      intro x x' y
      rw [map_add]
      erw [CochainScalarConstruction.pure_add_left R]
      rw [map_add, map_add])
    (by
      intro a x y
      rw [sections_inv_scalar]
      erw [CochainScalarConstruction.pure_smul_left R]
      rw [(c.inv.val.app W).hom.map_smul, sections_scalar])
    (by
      intro x y y'
      rw [map_add]
      erw [CochainScalarConstruction.pure_add_right R]
      rw [map_add, map_add])
    (by
      intro a x y
      rw [sections_inv_scalar]
      erw [CochainScalarConstruction.pure_smul_right R]
      rw [(c.inv.val.app W).hom.map_smul, sections_scalar])

private theorem frontPair_restrict (M N H : FiniteModules A X)
    (c : e.equivalence.functor.obj H ≅
      e.equivalence.functor.obj M ⊗ e.equivalence.functor.obj N)
    {W V : X.ProEtᵒᵖ} (f : W ⟶ V) (x : M.obj.obj W) (y : N.obj.obj W) :
    frontPair e M N H c V (M.obj.map f x) (N.obj.map f y) =
      H.obj.map f (frontPair e M N H c W x y) := by
  change sections e H V (c.inv.val.app V
    (CochainScalarConstruction.pure R _ _ V
      ((sections e M V).symm (M.obj.map f x))
      ((sections e N V).symm (N.obj.map f y)))) = _
  rw [sections_inv_restrict, sections_inv_restrict]
  erw [← CochainScalarConstruction.pure_restrict R]
  erw [PresheafOfModules.naturality_apply c.inv.val f]
  exact sections_restrict e H f _

private theorem front_exists (M N : FiniteModules A X) :
    ∃ f : e.equivalence.functor.obj (M ⊗ N) ⟶
        e.equivalence.functor.obj M ⊗ e.equivalence.functor.obj N,
      ∀ W x y, f.val.app W ((sections e (M ⊗ N) W).symm
        (finitePure M N W x y)) =
      pure R _ _ W ((sections e M W).symm x) ((sections e N W).symm y) := by
  let H := e.equivalence.inverse.obj
    (e.equivalence.functor.obj M ⊗ e.equivalence.functor.obj N)
  let c : e.equivalence.functor.obj H ≅
      e.equivalence.functor.obj M ⊗ e.equivalence.functor.obj N :=
    e.equivalence.counitIso.app _
  obtain ⟨q, hq⟩ := fixed_lift M N H (frontPair e M N H c)
    (frontPair_restrict e M N H c)
  refine ⟨e.equivalence.functor.map q ≫ c.hom, ?_⟩
  intro W x y
  have h := sections_map e q W ((sections e (M ⊗ N) W).symm
    (finitePure M N W x y))
  rw [AddEquiv.apply_symm_apply, hq] at h
  have hh := congrArg (sections e H W).symm h
  rw [AddEquiv.symm_apply_apply] at hh
  change (e.equivalence.functor.map q).val.app W _ =
    (sections e H W).symm (sections e H W
      (c.inv.val.app W (CochainScalarConstruction.pure R _ _ W
        ((sections e M W).symm x) ((sections e N W).symm y)))) at hh
  rw [AddEquiv.symm_apply_apply] at hh
  change c.hom.val.app W ((e.equivalence.functor.map q).val.app W _) = _
  rw [hh]
  exact congrArg (fun k ↦ k.val.app W (pure R _ _ W
    ((sections e M W).symm x) ((sections e N W).symm y))) c.inv_hom_id

private theorem realized_tensor_ext (M N H : FiniteModules A X)
    (f g : e.equivalence.functor.obj (M ⊗ N) ⟶ e.equivalence.functor.obj H)
    (h : ∀ W x y, f.val.app W ((sections e (M ⊗ N) W).symm
        (finitePure M N W x y)) =
      g.val.app W ((sections e (M ⊗ N) W).symm (finitePure M N W x y))) : f = g := by
  have hh : e.equivalence.functor.preimage f = e.equivalence.functor.preimage g := by
    apply CategoryTheory.ConstantScalarRestriction.fixedTensor_ext (ProEt.topology X) A
    intro W x y
    have hf := sections_map e (e.equivalence.functor.preimage f) W
      ((sections e (M ⊗ N) W).symm (finitePure M N W x y))
    have hg := sections_map e (e.equivalence.functor.preimage g) W
      ((sections e (M ⊗ N) W).symm (finitePure M N W x y))
    rw [e.equivalence.functor.map_preimage, AddEquiv.apply_symm_apply] at hf hg
    exact hf.symm.trans ((congrArg (sections e H W) (h W x y)).trans hg)
  simpa only [Functor.map_preimage] using congrArg e.equivalence.functor.map hh

private theorem ordinary_obj_exists
    [Presheaf.IsLocallySurjective (ProEt.topology X) i] (M N : FiniteModules A X) :
    ∃ c : e.equivalence.functor.obj (M ⊗ N) ≅
        e.equivalence.functor.obj M ⊗ e.equivalence.functor.obj N,
      ∀ W x y, c.hom.val.app W ((sections e (M ⊗ N) W).symm
        (finitePure M N W x y)) =
      pure R _ _ W ((sections e M W).symm x) ((sections e N W).symm y) := by
  obtain ⟨f, hf⟩ := front_exists e M N
  obtain ⟨g, hg⟩ := back_exists e M N
  refine ⟨{ hom := f, inv := g, hom_inv_id := ?_, inv_hom_id := ?_ }, hf⟩
  · apply realized_tensor_ext e M N (M ⊗ N)
    intro W x y
    change g.val.app W (f.val.app W _) = _
    rw [hf, hg]
    simp only [backPair, AddEquiv.apply_symm_apply]
    rfl
  · apply CochainScalarConstruction.pure_hom_ext R
    intro W x y
    change f.val.app W (g.val.app W (pure R _ _ W x y)) = _
    rw [hg]
    change f.val.app W ((sections e (M ⊗ N) W).symm
      (finitePure M N W (sections e M W x) (sections e N W y))) = _
    rw [hf]
    simp only [AddEquiv.symm_apply_apply]
    rfl

private theorem fixed_pure_map {M M' N N' : FiniteModules A X}
    (f : M ⟶ M') (g : N ⟶ N') (W : X.ProEtᵒᵖ)
    (x : M.obj.obj W) (y : N.obj.obj W) :
    (f ⊗ₘ g).hom.app W (finitePure M N W x y) =
      finitePure M' N' W (f.hom.app W x) (g.hom.app W y) := by
  exact (ConcreteCategory.congr_hom (congr_app
    (Functor.LaxMonoidal.μ_natural (sheafToPresheaf (ProEt.topology X)
      (ModuleCat.{u + 1} A)) f g) W) (x ⊗ₜ[A] y)).symm

private theorem sections_inv_map {M N : FiniteModules A X} (f : M ⟶ N)
    (W : X.ProEtᵒᵖ) (x : M.obj.obj W) :
    (e.equivalence.functor.map f).val.app W ((sections e M W).symm x) =
      (sections e N W).symm (f.hom.app W x) := by
  apply (sections e N W).injective
  rw [sections_map, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

private theorem realized_tensor_ext_any (M N : FiniteModules A X) (H : Mod R)
    (f g : e.equivalence.functor.obj (M ⊗ N) ⟶ H)
    (h : ∀ W x y, f.val.app W ((sections e (M ⊗ N) W).symm
        (finitePure M N W x y)) =
      g.val.app W ((sections e (M ⊗ N) W).symm (finitePure M N W x y))) : f = g := by
  let c := e.equivalence.counitIso.app H
  apply (cancel_mono c.inv).mp
  apply realized_tensor_ext e M N
  intro W x y
  exact congrArg (c.inv.val.app W) (h W x y)

private theorem ordinary_natural
    (c : ∀ M N : FiniteModules A X, e.equivalence.functor.obj (M ⊗ N) ≅
      e.equivalence.functor.obj M ⊗ e.equivalence.functor.obj N)
    (hp : ∀ M N W x y, (c M N).hom.val.app W
        ((sections e (M ⊗ N) W).symm (finitePure M N W x y)) =
      pure R _ _ W ((sections e M W).symm x) ((sections e N W).symm y))
    {M M' N N' : FiniteModules A X} (f : M ⟶ M') (g : N ⟶ N') :
    e.equivalence.functor.map (f ⊗ₘ g) ≫ (c M' N').hom =
      (c M N).hom ≫ (e.equivalence.functor.map f ⊗ₘ e.equivalence.functor.map g) := by
  apply realized_tensor_ext_any e M N
  intro W x y
  change (c M' N').hom.val.app W ((e.equivalence.functor.map (f ⊗ₘ g)).val.app W
      ((sections e (M ⊗ N) W).symm (finitePure M N W x y))) =
    (e.equivalence.functor.map f ⊗ₘ e.equivalence.functor.map g).val.app W
      ((c M N).hom.val.app W ((sections e (M ⊗ N) W).symm
        (finitePure M N W x y)))
  rw [sections_inv_map, fixed_pure_map, hp, hp]
  change pure R _ _ W ((sections e M' W).symm (f.hom.app W x))
      ((sections e N' W).symm (g.hom.app W y)) =
    (e.equivalence.functor.map f ⊗ₘ e.equivalence.functor.map g).val.app W
      (CochainScalarConstruction.pure R _ _ W _ _)
  erw [CochainScalarConstruction.pure_map R]
  rw [sections_inv_map, sections_inv_map]
  rfl

end TensorOrdinary

/-- The ordinary tensor comparison for the prescribed section/scalar realization.

Source: Stacks, Modules on Sites, Tag 03EK (the Hom--Bilin characterization).
(blueprint: lem-sf-finite-tensor-ordinary-comparison-helper).

Proof: use the supplied underlying isomorphism to identify sections and their
restrictions, constant scalar actions and morphisms. The fixed tensor represents
restriction-compatible A-bilinear pairings by the sectionwise tensor universal
property and the sheafification adjunction. Transport its pure pairing to the
realized objects. For any section r of R, its image sieve under i covers; there r
lifts to a constant scalar, so the transported pairing is R-linear locally.
Separatedness proves R-linearity globally in both variables. The ringed tensor
universal property gives the backward comparison. For the forward comparison,
choose the inverse-equivalence image of the ringed tensor, transport its pure
pairing to fixed sheaves, and use the fixed tensor universal property. Apply F
and the counit to the resulting map. The two composites fix pure pairs; the
two tensor extensionality principles prove that they are identities. Finally,
both naturality paths agree on pure pairs, using naturality of the underlying
isomorphism and of each pure pairing. No monoidal structure on F is assumed. -/
theorem finite_tensor_ordinary_comparison_exists
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj)
    [Presheaf.IsLocallySurjective (ProEt.topology X) i]
    (e : FiniteRealization A X R i) :
    ∃ c : ∀ M N : FiniteModules A X,
        e.equivalence.functor.obj (M ⊗ N) ≅
          ((tensor R).obj (e.equivalence.functor.obj M)).obj (e.equivalence.functor.obj N),
      (∀ M M' N N' (f : M ⟶ M') (g : N ⟶ N'),
        e.equivalence.functor.map (f ⊗ₘ g) ≫
            (c M' N').hom = (c M N).hom ≫
              (e.equivalence.functor.map f ⊗ₘ e.equivalence.functor.map g)) ∧
      (∀ M N W x y, (c M N).hom.val.app W
          ((e.underlying.inv.app (M ⊗ N)).hom.app W
            (finitePure M N W x y)) =
        pure R (e.equivalence.functor.obj M) (e.equivalence.functor.obj N) W
          ((e.underlying.inv.app M).hom.app W x)
          ((e.underlying.inv.app N).hom.app W y)) := by
  choose c hp using TensorOrdinary.ordinary_obj_exists e
  refine ⟨c, ?_, hp⟩
  intro M M' N N' f g
  exact TensorOrdinary.ordinary_natural e c hp f g

end SheafOfModules.OpenTensorNormalization
