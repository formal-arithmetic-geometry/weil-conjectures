/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilRowHomComparison
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorTransport
import WeilConjectures.WeilSheaf.Native.NativeClosedTransposition
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Forgetting Frobenius on native derived categories

## Implementation details

Abelian Weil sheaves are identified with modules on the ringed site obtained by closing a small
pro-étale site under the integer iterates of the semilinear geometric Frobenius. Forgetting is
the ringed pullback; it is exact and has the exact orbit-sum induction as left adjoint, so it
preserves both K-flat flat-term and K-injective resolutions. The tensor and Hom comparisons are
then computed on K-flat, respectively K-injective, representatives, where the normalized
adjunction uncurries `φ` to `x ⊗ y ↦ φ(x)(y)`; forgetting preserves this formula, which
identifies the derived Hom comparison with `nativeHomComparison`.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf
variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- Forgetting Frobenius on the native derived category is exact, conservative,
commutes with cohomology, restricts to bounded constructible objects, and preserves
the closed symmetric derived tensor, evaluation, and transposed evaluation. -/
theorem native_closed_forgetful
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))] :
    (nativeForget k₀ l X).IsTriangulated ∧
    (nativeForget k₀ l X).ReflectsIsomorphisms ∧
    (∀ n : ℤ, Nonempty (nativeForget k₀ l X ⋙ DerivedCategory.homologyFunctor _ n ≅
      DerivedCategory.homologyFunctor _ n ⋙
        Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X))) ∧
    (∀ K : WeilComplex k₀ l X,
      DerivedCategory.TStructure.t.bounded ((nativeForget k₀ l X).obj K.obj) ∧
      ∀ n : ℤ, ProEtale.IsAdicConstructibleSheaf
        ((DerivedCategory.homologyFunctor _ n).obj ((nativeForget k₀ l X).obj K.obj))) ∧
    (∃ C : NativeClosedComparison k₀ l X, C.Compatible) := by
  let U := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)
  refine ⟨inferInstance, ?_, (fun n ↦ ⟨(U.mapDerivedCategoryHomologyFunctorIso n).symm⟩),
    ?_, ?_⟩
  · constructor
    intro A B f hf
    have : IsIso (U.mapDerivedCategory.map f) := hf
    rw [DerivedCategory.isIso_iff]
    intro n
    have h : IsIso ((DerivedCategory.homologyFunctor _ n ⋙ U).map f) :=
      (NatIso.isIso_map_iff (U.mapDerivedCategoryHomologyFunctorIso n) f).mpr
        (show IsIso ((DerivedCategory.homologyFunctor _ n).map
          (U.mapDerivedCategory.map f)) from inferInstance)
    have : IsIso (U.map ((DerivedCategory.homologyFunctor _ n).map f)) := h
    exact isIso_of_reflects_iso ((DerivedCategory.homologyFunctor _ n).map f) U
  · intro K
    refine ⟨U.bounded_mapDerivedCategory_obj K.property.1, fun n ↦ ?_⟩
    exact (ProEtale.adicConstructibleSheaf l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).prop_of_iso
        ((U.mapDerivedCategoryHomologyFunctorIso n).app K.obj) (K.property.2 n)
  · obtain ⟨m⟩ := native_two_injective_hom_model (k₀ := k₀) (l := l) (X := X)
    obtain ⟨M, η, _, _, _, hrep⟩ := native_row_hom_comparison k₀ l X m
    obtain ⟨C, hM, hη, hcan, hcoh, hsym⟩ := native_tensor_transport k₀ l X M η hrep
    subst M
    have heq : C.homComparison = η := eq_of_heq hη
    subst η
    refine ⟨C, hcan, hrep, hcoh, hsym, ?_, ?_, ?_⟩
    · exact nativeComparison_evaluation _ _ _ _ _ hcan
    · exact nativeBidual_natural _ _
    · exact nativeComparison_bidual _ _ _ _ _ hcan _ _ hsym

end AlgebraicGeometry.ProEtaleWeilSheaf
