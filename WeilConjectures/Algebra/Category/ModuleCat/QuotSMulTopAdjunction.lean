/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.Algebra.Category.ModuleCat.QuotSMulTop
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat

/-!
# Reduction modulo an ideal is left adjoint to restriction of scalars

For an ideal `I` of a commutative ring `R`, the reduction functor `M ↦ M / I M`
(`ModuleCat.quotSMulTop`) from `R`-modules to `R ⧸ I`-modules is left adjoint to restriction
of scalars along `R ⟶ R ⧸ I`: an `R ⧸ I`-linear map `M / I M ⟶ N` is the same as an `R`-linear
map `M ⟶ N`, since `I` acts by zero on `N`. Hence it is isomorphic to extension of scalars.

## Main definitions

- `ModuleCat.quotSMulTopAdj I`: the adjunction `quotSMulTop I ⊣ restrictScalars (mk I)`.
- `ModuleCat.extendScalarsIsoQuotSMulTop I`: extension of scalars along `R ⟶ R ⧸ I` is
  reduction modulo `I`.
-/

@[expose] public section

universe v u

open CategoryTheory

open scoped Pointwise

namespace ModuleCat

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The `R`-linear map `M ⟶ N` underlying an `R ⧸ I`-linear map `M / I M ⟶ N`. -/
noncomputable def quotSMulTopHomEquivToFun {M : ModuleCat.{v} R} {N : ModuleCat.{v} (R ⧸ I)}
    (f : (quotSMulTop I).obj M ⟶ N) : M ⟶ (restrictScalars (Ideal.Quotient.mk I)).obj N :=
  ofHom (Y := (restrictScalars (Ideal.Quotient.mk I)).obj N)
    { toFun m := f (Submodule.Quotient.mk m)
      map_add' a b := by
        rw [Submodule.Quotient.mk_add, map_add]
      map_smul' r m := by
        change f (Submodule.Quotient.mk (r • m)) = Ideal.Quotient.mk I r • _
        rw [← Module.Quotient.mk_smul_mk, map_smul] }

/-- The `R ⧸ I`-linear map `M / I M ⟶ N` induced by an `R`-linear map `M ⟶ N`. -/
noncomputable def quotSMulTopHomEquivInvFun {M : ModuleCat.{v} R} {N : ModuleCat.{v} (R ⧸ I)}
    (g : M ⟶ (restrictScalars (Ideal.Quotient.mk I)).obj N) : (quotSMulTop I).obj M ⟶ N :=
  ofHom
    { toFun := Submodule.liftQ (I • ⊤) g.hom (by
        rw [Submodule.smul_le]
        intro r hr m _
        rw [LinearMap.mem_ker, map_smul]
        change Ideal.Quotient.mk I r • _ = (0 : N)
        rw [Ideal.Quotient.eq_zero_iff_mem.2 hr, zero_smul])
      map_add' := map_add _
      map_smul' c x := by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
        obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        rw [Module.Quotient.mk_smul_mk]
        exact g.hom.map_smul r m }

/-- **Reduction modulo `I` is left adjoint to restriction of scalars along `R ⟶ R ⧸ I`.** -/
noncomputable def quotSMulTopAdj :
    quotSMulTop.{v} I ⊣ restrictScalars.{v} (Ideal.Quotient.mk I) :=
  Adjunction.mkOfHomEquiv
    { homEquiv M N :=
        { toFun := quotSMulTopHomEquivToFun I
          invFun := quotSMulTopHomEquivInvFun I
          left_inv f := by
            refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
            obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
            simp [quotSMulTopHomEquivInvFun, quotSMulTopHomEquivToFun]
          right_inv g := by
            refine ModuleCat.hom_ext (LinearMap.ext fun m ↦ ?_)
            simp [quotSMulTopHomEquivInvFun, quotSMulTopHomEquivToFun] }
      homEquiv_naturality_left_symm f g := by
        refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
        obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        simp [quotSMulTopHomEquivInvFun]
      homEquiv_naturality_right f g := ModuleCat.hom_ext (LinearMap.ext fun m ↦ rfl) }

/-- Extension of scalars along `R ⟶ R ⧸ I` is reduction modulo `I`, both being left adjoint to
restriction of scalars. -/
noncomputable def extendScalarsIsoQuotSMulTop :
    extendScalars.{u, u, u} (Ideal.Quotient.mk I) ≅ quotSMulTop.{u} I :=
  (extendRestrictScalarsAdj (Ideal.Quotient.mk I)).leftAdjointUniq (quotSMulTopAdj I)

instance : (quotSMulTop.{u} I).IsLeftAdjoint :=
  (quotSMulTopAdj I).isLeftAdjoint

/-- **The reduction of a flat module is flat.** If `M` is a flat `R`-module, then `M / I M` is a
flat `R ⧸ I`-module, being the base change `(R ⧸ I) ⊗_R M`. -/
lemma flat_quotSMulTop_obj {M : ModuleCat.{u} R} (hM : ObjectProperty.flat M) :
    ObjectProperty.flat ((quotSMulTop I).obj M) := by
  rw [flat_iff_flat] at hM ⊢
  exact Module.Flat.of_linearEquiv (LinearEquiv.extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective (TensorProduct.quotTensorEquivQuotSMul M I)).symm

end ModuleCat
