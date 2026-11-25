/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
import WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryClosedTensorModels
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorLift

/-! # Tensor transport for a fixed native product-Hom comparison

## References

* Stacks Project, Tags 06YS, 08J9 and 0A97.
-/

@[expose] public section
set_option autoImplicit false
universe u a b
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

private theorem homComparison_of_uncurry
    {A B : Type a} [Category.{b} A] [Category.{b} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (W : CoefficientClosedStructure HA) (S : CoefficientClosedStructure HB)
    (U : A ⥤ B) (τ : W.tensor ⋙ U ≅ U.prod U ⋙ S.tensor)
    (η : HA ⋙ U ≅ U.op.prod U ⋙ HB)
    (huncurry : ∀ (T K L : A) (f : T ⟶ HA.obj (op K, L)),
      (S.transpose (U.obj T) (U.obj K) (U.obj L)).symm
          (U.map f ≫ (η.app (op K, L)).hom) =
        (τ.app (T, K)).inv ≫ U.map ((W.transpose T K L).symm f)) :
    ∀ K L, (η.app (op K, L)).hom = nativeHomComparison W S U τ K L := by
  intro K L
  let e := S.transpose (U.obj (HA.obj (op K, L))) (U.obj K) (U.obj L)
  have hi : (W.transpose (HA.obj (op K, L)) K L).symm (𝟙 _) = W.evaluation K L :=
    (W.adjunction K).homEquiv_symm_id L
  have h := huncurry (HA.obj (op K, L)) K L (𝟙 _)
  rw [U.map_id, Category.id_comp, hi] at h
  exact e.symm.injective (h.trans (e.symm_apply_apply _).symm)

private theorem tensorCoherence_of_unit
    {A B : Type a} [Category.{b} A] [Category.{b} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (W : CoefficientClosedStructure HA) (S : CoefficientClosedStructure HB)
    (γ : @SymmetricCategory _ _ W.monoidal) (β : @SymmetricCategory _ _ S.monoidal)
    (U : A ⥤ B) (τ : W.tensor ⋙ U ≅ U.prod U ⋙ S.tensor)
    (c : RingedForgetTensorTransposition.TensorCoherence W.monoidal S.monoidal γ β U τ)
    (ε : U.obj W.monoidal.tensorUnit ≅ S.monoidal.tensorUnit) (hunit : c.unit = ε) :
    NativeTensorCoherence W S U τ ε := by
  subst ε
  exact ⟨c.associativity, fun K ↦ (c.left_unit K).symm,
    fun K ↦ (c.right_unit K).symm⟩

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- Transport the ringed-site derived tensor to the specified row-sign Hom models.
This step constructs the tensor and its normalized adjunction; it asserts neither
an evaluation square nor biduality compatibility. -/
theorem native_tensor_transport
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    (M : NativeClosedHomModels k₀ l X)
    (η : M.weilHom ⋙ nativeForget k₀ l X ≅
      (nativeForget k₀ l X).op.prod (nativeForget k₀ l X) ⋙ M.ordinaryHom)
    (_hη : NativeHomRepresentativeCompatibility (ihomBifunctor k₀ l X)
      (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      M.weilHom M.ordinaryHom M.weilRepresentatives M.ordinaryRepresentatives
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) η) :
    ∃ C : NativeClosedComparison k₀ l X,
      C.homModels = M ∧ HEq C.homComparison η ∧
      (∀ K L, (C.homComparison.app (op K, L)).hom =
        nativeHomComparison C.weilClosed C.ordinaryClosed (nativeForget k₀ l X)
          C.tensorComparison K L) ∧
      NativeTensorCoherence C.weilClosed C.ordinaryClosed (nativeForget k₀ l X)
        C.tensorComparison C.unitComparison ∧
      NativeSymmetryCompatibility C.weilClosed C.ordinaryClosed C.weilSymmetry
        C.ordinarySymmetry (nativeForget k₀ l X) C.tensorComparison := by
  obtain ⟨S, β, hmonoidal, hS⟩ := native_ordinary_closed_tensor_models l
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber M.ordinaryHom M.ordinaryRepresentatives
  obtain ⟨W, γ, δ, ε, τ, c, hunit, huncurry⟩ :=
    native_weil_tensor_lift k₀ l X M η _hη S β hmonoidal hS
  let C : NativeClosedComparison k₀ l X := {
    homModels := M
    weilClosed := W
    ordinaryClosed := S
    weilUnit := δ
    ordinaryUnit := ε
    weilSymmetry := γ
    ordinarySymmetry := β
    ordinaryTensorModels := hS
    tensorComparison := τ
    homComparison := η }
  exact ⟨C, rfl, HEq.rfl, homComparison_of_uncurry W S (nativeForget k₀ l X) τ η huncurry,
    tensorCoherence_of_unit W S γ β (nativeForget k₀ l X) τ c C.unitComparison hunit,
    c.symmetry⟩

end AlgebraicGeometry.ProEtaleWeilSheaf
