/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.NativePullTensor
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
public import WeilConjectures.CategoryTheory.Functor.CurryComparison
public import WeilConjectures.WeilSheaf.Native.Open.NativeOpenDerivedTensor
public import WeilConjectures.WeilSheaf.ExtensionByZeroDerived
public import WeilConjectures.CategoryTheory.Adjunction.FullyFaithfulCounitLocal

/-! # The canonical open projection isomorphism -/

@[expose] public noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace CategoryTheory.Functor

/-- Naturality of a left-adjoint projection map in uncurried form. -/
lemma naturality_curry_leftProjection
    {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D} {G : D ⥤ C}
    {T : C × C ⥤ C} {S : D × D ⥤ D}
    (q : (postcompose₂.obj F).obj
        ((((whiskeringLeft₂ C).obj (𝟭 C)).obj G).obj (curry.obj T)) ⟶
      (((whiskeringLeft₂ D).obj F).obj (𝟭 D)).obj (curry.obj S))
    {M M' : C} {N N' : D} (a : M ⟶ M') (b : N ⟶ N') :
    F.map (T.map (Prod.mkHom a (G.map b))) ≫ (q.app M').app N' =
      (q.app M).app N ≫ S.map (Prod.mkHom (F.map a) b) := by
  have h₁ := NatTrans.congr_app (q.naturality a) N
  have h₂ := (q.app M').naturality b
  dsimp at h₁ h₂
  have e₁ : Prod.mkHom a (G.map b) =
      Prod.mkHom a (𝟙 _) ≫ Prod.mkHom (𝟙 _) (G.map b) := by ext <;> simp
  have e₂ : Prod.mkHom (F.map a) b =
      Prod.mkHom (F.map a) (𝟙 _) ≫ Prod.mkHom (𝟙 _) b := by ext <;> simp
  rw [e₁, e₂, T.map_comp, F.map_comp, S.map_comp, Category.assoc,
    h₂, ← Category.assoc, h₁, Category.assoc]

end CategoryTheory.Functor

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
      (nativeOpenPull k₀ l j) (Functor.curry.obj (nativeDerivedTensor k₀ l U))
      (Functor.curry.obj (nativeDerivedTensor k₀ l Z))
      (Functor.curryCompIsoOfIso (nativePullTensor k₀ l j)).inv).app M).app N) := by
  obtain ⟨s, d, _, _⟩ := native_open_derived_tensor k₀ l j
  -- the essential-image witness, normalized without unfolding the derived tensor
  have e := d.gamma.app (M, N)
  dsimp only [nativeOpenDerivedLeft, nativeOpenDerivedRight, nativeOpenExtension, nativeOpenPull,
    Functor.comp_obj, Functor.prod_obj, Functor.id_obj] at e
  refine (derivedExtensionByZeroUpperStarAdjunction k₀ l j).isIso_projectionMap_app_app_of_iso
    (nativeOpenPull k₀ l j) (Functor.curry.obj (nativeDerivedTensor k₀ l U))
    (Functor.curry.obj (nativeDerivedTensor k₀ l Z))
    (Functor.curryCompIsoOfIso (nativePullTensor k₀ l j)).inv M N
    ((nativeDerivedTensor k₀ l U).obj (M, (nativeOpenPull k₀ l j).obj N)) ?_
  dsimp only [Functor.curry_obj_obj_obj, nativeOpenExtension, nativeOpenPull]
  exact e

/-- Extension by zero satisfies the projection formula, with inverse given by the canonical
unit transpose for the native pullback/tensor comparison. -/
def nativeOpenProjectionIso : nativeOpenDerivedLeft k₀ l j ≅ nativeOpenDerivedRight k₀ l j := by
  let q := (derivedExtensionByZeroUpperStarAdjunction k₀ l j).projectionMap
    (nativeOpenPull k₀ l j) (Functor.curry.obj (nativeDerivedTensor k₀ l U))
    (Functor.curry.obj (nativeDerivedTensor k₀ l Z))
    (Functor.curryCompIsoOfIso (nativePullTensor k₀ l j)).inv
  have h (MN : DerivedCategory (ProEtaleWeilSheaf k₀ l U) ×
      DerivedCategory (ProEtaleWeilSheaf k₀ l Z)) : IsIso ((q.app MN.1).app MN.2) :=
    isIso_nativeOpenProjectionMap k₀ l j MN.1 MN.2
  refine (NatIso.ofComponents (fun MN ↦ @asIso _ _ _ _ ((q.app MN.1).app MN.2) (h MN))
    ?_).symm
  rintro ⟨M, N⟩ ⟨M', N'⟩ ⟨a, b⟩
  exact Functor.naturality_curry_leftProjection q a b

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
      (nativeOpenPull k₀ l j) (Functor.curry.obj (nativeDerivedTensor k₀ l U))
      (Functor.curry.obj (nativeDerivedTensor k₀ l Z))
      (Functor.curryCompIsoOfIso (nativePullTensor k₀ l j)).inv).app M).app N) = _
  rw [Adjunction.projectionMap_app_app, Equiv.apply_symm_apply,
    Adjunction.projectionMapTranspose_app_app]
  -- componentwise, without `simp` on the derived tensor
  dsimp only [Functor.curry_obj_map_app, Functor.curryCompIsoOfIso, NatIso.ofComponents_inv_app,
    Iso.app_inv, nativeOpenExtension, nativeOpenPull]
  try rfl

end AlgebraicGeometry.ProEtaleWeilSheaf
