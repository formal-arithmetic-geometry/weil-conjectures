/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedFibreLinearCurrent.CondensedFibreLinearOperationsStatement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralLisseDerivedAux
import WeilConjectures.AlgebraicGeometry.Pullback.PullbackFiniteConstantLocalModel

/-! # Positive tensor powers of native lisse Weil modules

Source: latest blueprint, sec-purity-real-sheaves/sk-p-real-semi/sk-p-real-semi.proof.md,
last paragraph: form the lisse Weil sheaf F tensor k.
(blueprint: def-wf-native-positive-weil-tensor-power).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.NativeL2

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (U₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]

/-- The n+1-fold tensor, with the induced inverse-pullback-tensorator Weil structure.
This is a recursive construction of actual module objects and their Weil isomorphisms.
Source: latest blueprint, sk-p-real-semi.proof.md, final paragraph
(blueprint: def-wf-native-positive-weil-tensor-power). -/
def positiveWeilTensorPower (M : WeilModule D l U₀) : ℕ → WeilModule D l U₀
  | 0 => M
  | n + 1 => CondensedFibreLinearCurrent.tensorWeil l (D.geometricFrobenius U₀)
    M (positiveWeilTensorPower M n)

end WeilConjectures.NativeL2

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}

private theorem free_tensor
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : Mod.IsFree (condensedRingObj Λ X) M)
    (hN : Mod.IsFree (condensedRingObj Λ X) N) :
    Mod.IsFree (condensedRingObj Λ X) (M ⊗ N) := by
  obtain ⟨k, ⟨eM⟩⟩ := hM
  obtain ⟨n, ⟨eN⟩⟩ := hN
  let F := tensorLeft M
  let e : F.obj (Mod.regular (condensedRingObj Λ X)) ≅
      Mod.finiteFree (condensedRingObj Λ X) k := (ρ_ M) ≪≫ eM
  exact ⟨n * k, ⟨F.mapIso eN ≪≫ F.mapBiproduct _ ≪≫
    biproduct.mapIso (fun _ ↦ e) ≪≫ Mod.finiteFreeFiniteFreeIso _ n k⟩⟩

private theorem free_pullback_comp {Y W : Scheme.{u}} (a : W ⟶ Y) (f : Y ⟶ X)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : Mod.IsFree (condensedRingObj Λ Y) ((CondensedRing.upperStar Λ f).obj M)) :
    Mod.IsFree (condensedRingObj Λ W) ((CondensedRing.upperStar Λ (a ≫ f)).obj M) :=
  (CondensedRing.IsFree.upperStar Λ a hM).of_iso
    ((CondensedRing.upperStarComp Λ a f).app M).symm

/-- Tensor products preserve the native finite locally free coefficient predicate. -/
private theorem isLisseCoefficientModule_tensor
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : IsLisseCoefficientModule Λ M) (hN : IsLisseCoefficientModule Λ N) :
    IsLisseCoefficientModule Λ (M ⊗ N) := by
  obtain ⟨𝒰, h𝒰⟩ := hM
  obtain ⟨𝒱, h𝒱⟩ := hN
  obtain ⟨𝒲, h𝒲⟩ := CondensedRing.exists_cover_forall_and
    (fun Y f ↦ Mod.IsFree (condensedRingObj Λ Y) ((CondensedRing.upperStar Λ f).obj M))
    (fun Y f ↦ Mod.IsFree (condensedRingObj Λ Y) ((CondensedRing.upperStar Λ f).obj N))
    (fun {_ _} a f h ↦ free_pullback_comp a f h)
    (fun {_ _} a f h ↦ free_pullback_comp a f h) 𝒰 𝒱 h𝒰 h𝒱
  exact ⟨𝒲, fun i ↦ (free_tensor (h𝒲 i).1 (h𝒲 i).2).of_iso
    (Functor.Monoidal.μIso (CondensedRing.upperStar Λ (𝒲.f i)) M N)⟩

private theorem lisse_finiteModel
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsLisseCoefficientModule Λ M) : HasFiniteConstantLocalModel Λ X M := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨r, ⟨e⟩⟩ := hU i
  have : PreservesFiniteLimits (upperStarFromPoint (U.X i)) := by
    unfold upperStarFromPoint pointUpperStar
    infer_instance
  let F := (upperStarFromPoint (U.X i)).mapMod Λ
  have : F.Additive := Functor.additive_of_preserves_binary_products _
  let en : F.obj (Mod.finiteFree Λ r) ≅
      Mod.finiteFree (condensedRingObj Λ (U.X i)) r :=
    F.mapBiproduct (fun _ : Fin r ↦ Mod.regular Λ) ≪≫
      biproduct.mapIso (fun _ ↦ Mod.isoMk (Iso.refl _) (by simp [Mod.act]))
  exact ⟨Mod.finiteFree Λ r, ⟨r, 0, 0, ⟨cokernelZeroIsoTarget.symm⟩⟩,
    ⟨e ≪≫ en.symm⟩⟩

private theorem lisse_stratified
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsLisseCoefficientModule Λ M) : IsFiniteConstantStratified Λ X M :=
  ⟨Scheme.Stratification.trivial X, fun _ ↦
    pullback_finiteConstantLocalModel Λ (𝟙 X) M (lisse_finiteModel M hM)⟩

/-- Finite locally free coefficients have a finite constant-model stratification. -/
private theorem isLisseCoefficientModule_constructible
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsLisseCoefficientModule Λ M) : IsConstantModelConstructible Λ X M := by
  classical
  unfold IsConstantModelConstructible
  split
  · exact lisse_stratified M hM
  · intro U _
    exact lisse_stratified _ ((isLocallyFree_iff _).mp
      (((isLocallyFree_iff M).mpr hM).upperStar Λ U.ι))

end AlgebraicGeometry.ProEtale

namespace WeilConjectures.NativeL2

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (U₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]

/-- On a common pro-etale trivialization, tensor products of free modules of ranks r and s
are free of rank r*s. Induction gives lissity; finite free local models give constructibility.
Source: latest blueprint, sk-p-real-semi.proof.md, final paragraph
(blueprint: def-wf-native-positive-weil-tensor-power). -/
theorem positiveWeilTensorPower_properties (M : WeilModule D l U₀)
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier) (n : ℕ) :
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj l)
        (positiveWeilTensorPower D l U₀ M n).carrier ∧
      IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
        (D.geometricFiber U₀).left (positiveWeilTensorPower D l U₀ M n).carrier := by
  have hLis : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l)
      (positiveWeilTensorPower D l U₀ M n).carrier := by
    induction n with
    | zero => exact hM
    | succ n hn => exact isLisseCoefficientModule_tensor hM hn
  exact ⟨hLis, isLisseCoefficientModule_constructible _ hLis⟩

end WeilConjectures.NativeL2
