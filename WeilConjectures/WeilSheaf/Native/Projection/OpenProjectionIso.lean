/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationCoherence
public import WeilConjectures.WeilSheaf.Native.Open.NativeOpenDerivedTensor
public import WeilConjectures.WeilSheaf.ExtensionByZeroDerived
public import WeilConjectures.CategoryTheory.Adjunction.FullyFaithfulCounitLocal

/-! # The canonical open projection isomorphism -/

@[expose] public noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] [Z.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  (j : U ⟶ Z) [j.IsOver (Spec (CommRingCat.of k₀))] [IsOpenImmersion j]

/-- The open projection comparison is invertible: the tensor of an extension by zero with
any complex lies in the essential image of the fully faithful extension by zero. -/
theorem isIso_nativeOpenProjectionMap
    (M : DerivedCategory (ProEtaleWeilSheaf k₀ l U))
    (N : DerivedCategory (ProEtaleWeilSheaf k₀ l Z)) :
    IsIso ((((derivedExtensionByZeroUpperStarAdjunction k₀ l j).projectionMap
      (nativeOpenPull k₀ l j) (nativeCurriedTensor k₀ l U) (nativeCurriedTensor k₀ l Z)
      (Functor.curryCompIsoOfIso (nativePullTensor k₀ l j)).inv).app M).app N) := by
  obtain ⟨s, d, _, _⟩ := native_open_derived_tensor k₀ l j
  exact (derivedExtensionByZeroUpperStarAdjunction k₀ l j).isIso_projectionMap_app_app_of_iso
    (nativeOpenPull k₀ l j) (nativeCurriedTensor k₀ l U) (nativeCurriedTensor k₀ l Z)
    (Functor.curryCompIsoOfIso (nativePullTensor k₀ l j)).inv M N
    ((nativeDerivedTensor k₀ l U).obj (M, (nativeOpenPull k₀ l j).obj N))
    (d.gamma.app (M, N))

/-- Extension by zero satisfies the projection formula, with inverse given by the canonical
unit transpose for the native pullback/tensor comparison. -/
def nativeOpenProjectionIso : nativeOpenDerivedLeft k₀ l j ≅ nativeOpenDerivedRight k₀ l j := by
  let q := (derivedExtensionByZeroUpperStarAdjunction k₀ l j).projectionMap
    (nativeOpenPull k₀ l j) (nativeCurriedTensor k₀ l U) (nativeCurriedTensor k₀ l Z)
    (Functor.curryCompIsoOfIso (nativePullTensor k₀ l j)).inv
  have h (MN : DerivedCategory (ProEtaleWeilSheaf k₀ l U) ×
      DerivedCategory (ProEtaleWeilSheaf k₀ l Z)) : IsIso ((q.app MN.1).app MN.2) :=
    isIso_nativeOpenProjectionMap k₀ l j MN.1 MN.2
  refine (NatIso.ofComponents (fun MN ↦ @asIso _ _ _ _ ((q.app MN.1).app MN.2) (h MN))
    ?_).symm
  rintro ⟨M, N⟩ ⟨M', N'⟩ ⟨a, b⟩
  exact Functor.naturality_curry_postcompose₂ q (𝟭 _) (𝟭 _) a b

/-- The inverse of the open projection isomorphism is the canonical unit transpose. -/
lemma nativeOpenProjectionIso_inverse_unit
    (M : DerivedCategory (ProEtaleWeilSheaf k₀ l U))
    (N : DerivedCategory (ProEtaleWeilSheaf k₀ l Z)) :
    (derivedExtensionByZeroUpperStarAdjunction k₀ l j).homEquiv _ _
      ((nativeOpenProjectionIso k₀ l j).inv.app (M, N)) =
      (nativeDerivedTensor k₀ l U).map
        (Prod.mkHom ((derivedExtensionByZeroUpperStarAdjunction k₀ l j).unit.app M) (𝟙 _)) ≫
        (nativePullTensor k₀ l j).inv.app ((nativeOpenExtension k₀ l j).obj M, N) := by
  change (derivedExtensionByZeroUpperStarAdjunction k₀ l j).homEquiv _ _
    ((((derivedExtensionByZeroUpperStarAdjunction k₀ l j).projectionMap
      (nativeOpenPull k₀ l j) (nativeCurriedTensor k₀ l U) (nativeCurriedTensor k₀ l Z)
      (Functor.curryCompIsoOfIso (nativePullTensor k₀ l j)).inv).app M).app N) = _
  rw [Adjunction.projectionMap_app_app, Equiv.apply_symm_apply]
  simp [Adjunction.projectionMapTranspose, nativeCurriedTensor, Functor.curryCompIsoOfIso]

end AlgebraicGeometry.ProEtaleWeilSheaf
