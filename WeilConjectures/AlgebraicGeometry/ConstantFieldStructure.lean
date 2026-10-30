/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantFieldGeometricFiber
public import WeilConjectures.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.RingTheory.ConstantField

/-!
# The constant field of a smooth irreducible affine scheme

Let `V` be a smooth irreducible affine scheme of finite type over a finite field `k₀`, and let
`A = Γ(V, 𝒪_V)`, an integrally closed domain of finite type over `k₀`. Its *constant field*, the
integral closure `k'` of `k₀` in `A` (`Algebra.TensorProduct.ConstantField`), is a finite field,
and `V` is a smooth geometrically connected scheme over `k'` through
`V ≅ Spec A ⟶ Spec k'`, compatibly with its structure over `k₀`
(`AlgebraicGeometry.exists_constantField_structure`): `A ⊗[k'] L` is a domain for every
separable extension `L / k'` (`Algebra.TensorProduct.isDomain_constantField`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped TensorProduct

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀]

/-- A morphism `f : X ⟶ Spec R` from an affine scheme factors through `X ≅ Spec Γ(X, ⊤)` as
`Spec` of the ring map `R ≅ Γ(Spec R, ⊤) ⟶ Γ(X, ⊤)`. -/
lemma Scheme.toSpecΓ_comp_specMap_ΓSpecIso_inv_comp_appTop {X : Scheme.{u}} {R : CommRingCat.{u}}
    (f : X ⟶ Spec R) :
    X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ f.appTop) = f := by
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]

/-- **The constant field structure.** A smooth irreducible affine scheme `V` of finite type over a
finite field `k₀` is a smooth, geometrically connected scheme of finite type over a finite
extension `k'` of `k₀` (its constant field), compatibly with the structure over `k₀`. -/
theorem exists_constantField_structure (V : Scheme.{u}) [V.Over (Spec (.of k₀))] [IsAffine V]
    [IrreducibleSpace V] [Smooth (V ↘ Spec (.of k₀))] [LocallyOfFiniteType (V ↘ Spec (.of k₀))] :
    ∃ (k' : Type u) (_ : Field k') (_ : Finite k') (_ : Algebra k₀ k') (c : V ⟶ Spec (.of k')),
      c ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ k')) = V ↘ Spec (.of k₀) ∧
      LocallyOfFiniteType c ∧ Smooth c ∧ GeometricallyConnected c := by
  set f := V ↘ Spec (.of k₀)
  set A := Γ(V, ⊤)
  let : Algebra k₀ A := ((Scheme.ΓSpecIso (.of k₀)).inv ≫ f.appTop).hom.toAlgebra
  have hf : V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ A)) = f :=
    Scheme.toSpecΓ_comp_specMap_ΓSpecIso_inv_comp_appTop f
  -- `V` is integral and normal, `Γ(V, ⊤)` is smooth of finite type over `k₀`
  have := IsRegular.of_smooth f
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian f
  have := IsRegular.isIntegral V
  have : Nonempty (⊤ : V.Opens) := ⟨⟨Nonempty.some inferInstance, trivial⟩⟩
  have : IsDomain A := inferInstance
  have : IsIntegrallyClosed A :=
    Scheme.isIntegrallyClosed_of_isIntegrallyClosed_stalk
      (fun x ↦ IsRegular.isIntegrallyClosed_stalk x) ⊤
  have hP {P : MorphismProperty Scheme.{u}} [P.RespectsIso] {R : CommRingCat.{u}}
      (φ : R ⟶ Γ(V, ⊤)) : P (V.toSpecΓ ≫ Spec.map φ) ↔ P (Spec.map φ) :=
    MorphismProperty.cancel_left_of_respectsIso P _ _
  have hfin : Algebra.FiniteType k₀ A := by
    have h : LocallyOfFiniteType (V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ A))) :=
      hf ▸ inferInstance
    rw [hP (P := @LocallyOfFiniteType), HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
      at h
    exact h
  have hsm : Algebra.Smooth k₀ A := by
    have h : Smooth (V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ A))) :=
      hf ▸ inferInstance
    rw [hP (P := @Smooth), HasRingHomProperty.Spec_iff (P := @Smooth)] at h
    exact h
  set k' := Algebra.TensorProduct.ConstantField k₀ A
  have : Finite k' := Algebra.TensorProduct.finite_constantField
  have : Algebra.FiniteType k' A := Algebra.FiniteType.of_restrictScalars_finiteType k₀ k' A
  have : Module.Finite k₀ k' := Module.Finite.of_finite
  have : Algebra.IsSeparable k₀ k' := inferInstance
  have : Algebra.FormallyUnramified k₀ k' := .of_isSeparable k₀ k'
  have : Algebra.FormallySmooth k' A := Algebra.FormallySmooth.of_restrictScalars k₀ k' A
  have : Algebra.FinitePresentation k' A := Algebra.FinitePresentation.of_finiteType.1 inferInstance
  set c := V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap k' A))
  refine ⟨k', inferInstance, inferInstance, inferInstance, c, ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq]
    exact hf
  · rw [hP (P := @LocallyOfFiniteType), HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.2 inferInstance
  · rw [hP (P := @Smooth), HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact ⟨inferInstance, inferInstance⟩
  · let : V.Over (Spec (.of k')) := ⟨c⟩
    refine (GeometricallyConnected.iff_connectedSpace_finite_separable k' V).2
      fun K _ _ _ _ ↦ ?_
    have := Algebra.TensorProduct.isDomain_constantField (k := k₀) (A := A) K
    let e : pullback c (Spec.map (CommRingCat.ofHom (algebraMap k' K))) ≅
        Spec (.of (A ⊗[k'] K)) :=
      asIso (pullback.map c _ (Spec.map (CommRingCat.ofHom (algebraMap k' A))) _ V.toSpecΓ (𝟙 _)
        (𝟙 _) (by simp [c]) (by simp)) ≪≫ pullbackSpecIso k' A K
    exact (Scheme.homeoOfIso e).symm.surjective.connectedSpace (Scheme.homeoOfIso e).symm.continuous

end AlgebraicGeometry
