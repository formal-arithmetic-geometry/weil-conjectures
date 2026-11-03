/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.Pure.NativePureSubobjects
import all WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartClosure
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Extensions
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-! # Mixed subobjects with native condensed coefficients

Source: latest blueprint, lem-a1-mixed-direct-summand, Subsheaves.
(blueprint: lem-zl-native-mixed-subobjects)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.NativeL2

/-- Mixedness is invariant under an isomorphism of actual Weil modules.
Source: latest blueprint, mixed finite-filtration definition.
(blueprint: lem-zl-native-mixed-subobjects)

Proof: retain every term, arrow and pure quotient of the filtration and compose
its last isomorphism with the prescribed isomorphism.
-/
theorem Mixed.of_iso
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    {M N : WeilModule D l X₀} (e : M ≅ N)
    (iota : PadicAlgCl l →+* ℂ) (w : ℝ) (hM : Mixed D l X₀ M iota w) :
    Mixed D l X₀ N iota w := by
  obtain ⟨n, G, φ, hc, hz, ⟨last⟩, hm, hp⟩ := hM
  exact ⟨n, G, φ, hc, hz, ⟨last ≪≫ e⟩, hm, hp⟩

private theorem inverseImage_kernels
    {C E : Type*} [Category* C] [Abelian C] [Category* E] [Abelian E]
    (P : ObjectProperty E) [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderKernels]
    (F : C ⥤ E) [F.Additive] [PreservesFiniteLimits F] :
    (P.inverseImage F).IsClosedUnderKernels := by
  constructor
  rintro _ ⟨f, k, hk, hX, hY⟩
  have h : (P.inverseImage F) (kernel f) :=
    P.prop_of_iso (PreservesKernel.iso F f).symm (P.prop_kernel (F.map f) hX hY)
  exact (P.inverseImage F).prop_of_iso ((kernelIsKernel f).conePointUniqueUpToIso hk) h

private theorem inverseImage_cokernels
    {C E : Type*} [Category* C] [Abelian C] [Category* E] [Abelian E]
    (P : ObjectProperty E) [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderCokernels]
    (F : C ⥤ E) [F.Additive] [PreservesFiniteColimits F] :
    (P.inverseImage F).IsClosedUnderCokernels := by
  constructor
  rintro _ ⟨f, k, hk, hX, hY⟩
  have h : (P.inverseImage F) (cokernel f) :=
    P.prop_of_iso (PreservesCokernel.iso F f).symm (P.prop_cokernel (F.map f) hX hY)
  exact (P.inverseImage F).prop_of_iso ((cokernelIsCokernel f).coconePointUniqueUpToIso hk) h

private theorem abelian_cokernel_comparison
    {C E : Type*} [Category* C] [Abelian C] [Category* E] [Abelian E]
    (F : C ⥤ E) [F.PreservesZeroMorphisms] [PreservesFiniteColimits F]
    {X Y : C} (f : X ⟶ Y) :
    Nonempty (F.obj (cokernel f) ≅ cokernel (F.map f)) :=
  ⟨PreservesCokernel.iso F f⟩

private theorem filtration_subobject
    {C : Type*} [Category* C] [Abelian C]
    (P Q : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    [Abelian P.FullSubcategory] [PreservesFiniteLimits P.ι] [PreservesFiniteColimits P.ι]
    [Q.IsClosedUnderSubobjects]
    {M N : C} (f : M ⟶ N) [Mono f] (hM : P M)
    (hN : ∃ (n : ℕ) (G : Fin (n + 1) → C)
      (φ : ∀ i : Fin n, G i.castSucc ⟶ G i.succ),
      (∀ i, P (G i)) ∧ IsZero (G 0) ∧ Nonempty (G (Fin.last n) ≅ N) ∧
      (∀ i, Mono (φ i)) ∧ ∀ i, Q (cokernel (φ i))) :
    ∃ (n : ℕ) (G : Fin (n + 1) → C)
      (φ : ∀ i : Fin n, G i.castSucc ⟶ G i.succ),
      (∀ i, P (G i)) ∧ IsZero (G 0) ∧ Nonempty (G (Fin.last n) ≅ M) ∧
      (∀ i, Mono (φ i)) ∧ ∀ i, Q (cokernel (φ i)) := by
  obtain ⟨n, G, φ, hc, hz, ⟨e⟩, hm, hp⟩ := hN
  let M' : P.FullSubcategory := ⟨M, hM⟩
  let N' : P.FullSubcategory := ⟨N, P.prop_of_iso e (hc (Fin.last n))⟩
  let G' : Fin (n + 1) → P.FullSubcategory := fun i ↦ ⟨G i, hc i⟩
  let φ' : ∀ i : Fin n, G' i.castSucc ⟶ G' i.succ := fun i ↦ P.homMk (φ i)
  have hφ' : ∀ i, Mono (φ' i) := fun i ↦ P.ι.mono_of_mono_map (hm i)
  have hfil : (Q.inverseImage P.ι).filtrationClosure N' := by
    apply ObjectProperty.filtrationClosure_iff.mpr
    refine ⟨n, G', φ', ?_, ⟨P.isoMk e⟩, hφ', ?_⟩
    · exact IsZero.of_full_of_faithful_of_isZero P.ι (G' 0) hz
    · intro i
      obtain ⟨eQ⟩ := abelian_cokernel_comparison P.ι (φ' i)
      exact Q.prop_of_iso eQ.symm (hp i)
  let f' : M' ⟶ N' := P.homMk f
  have hf : Mono f' := P.ι.mono_of_mono_map (show Mono f from inferInstance)
  have hfilM := (Q.inverseImage P.ι).filtrationClosure.prop_of_mono f' hfil
  obtain ⟨m, A, a, hA0, ⟨last⟩, ha, hq⟩ := ObjectProperty.filtrationClosure_iff.mp hfilM
  refine ⟨m, fun i ↦ (A i).obj, fun i ↦ P.ι.map (a i), fun i ↦ (A i).property,
    P.ι.map_isZero hA0, ⟨P.ι.mapIso last⟩, fun i ↦ ?_, fun i ↦ ?_⟩
  · let := ha i
    infer_instance
  · obtain ⟨eQ⟩ := abelian_cokernel_comparison P.ι (a i)
    exact Q.prop_of_iso eQ (hq i)

private theorem filtration_subobject_inverseImage
    {C E : Type*} [Category* C] [Abelian C] [Category* E] [Abelian E]
    (P₀ : ObjectProperty E) [P₀.IsClosedUnderIsomorphisms] [P₀.ContainsZero]
    [P₀.IsClosedUnderKernels] [P₀.IsClosedUnderCokernels] [P₀.IsClosedUnderExtensions]
    (V : C ⥤ E) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (Q : ObjectProperty C) [Q.IsClosedUnderSubobjects]
    {M N : C} (f : M ⟶ N) [Mono f] (hM : P₀ (V.obj M))
    (hN : ∃ (n : ℕ) (G : Fin (n + 1) → C)
      (φ : ∀ i : Fin n, G i.castSucc ⟶ G i.succ),
      (∀ i, P₀ (V.obj (G i))) ∧ IsZero (G 0) ∧ Nonempty (G (Fin.last n) ≅ N) ∧
      (∀ i, Mono (φ i)) ∧ ∀ i, Q (cokernel (φ i))) :
    ∃ (n : ℕ) (G : Fin (n + 1) → C)
      (φ : ∀ i : Fin n, G i.castSucc ⟶ G i.succ),
      (∀ i, P₀ (V.obj (G i))) ∧ IsZero (G 0) ∧ Nonempty (G (Fin.last n) ≅ M) ∧
      (∀ i, Mono (φ i)) ∧ ∀ i, Q (cokernel (φ i)) := by
  let P := P₀.inverseImage V
  let : P.IsClosedUnderKernels := inverseImage_kernels P₀ V
  let : P.IsClosedUnderCokernels := inverseImage_cokernels P₀ V
  obtain ⟨⟨hAb⟩, hlim, hcolim⟩ := heart_abelian P
  let := hAb
  let := hlim
  let := hcolim
  exact filtration_subobject P Q f hM hN

/-- Constructible native Weil subobjects inherit a mixed upper bound.
Source: latest blueprint, lem-a1-mixed-direct-summand, Subsheaves.
(blueprint: lem-zl-native-mixed-subobjects)

Proof: pass to the abelian full subcategory of constructible native Weil modules.
The ordinary coefficient heart is closed under kernels, cokernels and extensions;
the exact forgetful functor transfers these closures to Weil modules. Identify mixed
filtrations with the filtration closure of the property of being pure of some weight
at most w in this heart. Native purity is closed under subobjects, so intersecting a
filtration with a subobject again has pure successive quotients of the same weights.
The exact inclusion into all Weil modules identifies its kernels and cokernels with
the ordinary ones and returns precisely the required constructible filtration.
-/
theorem Mixed.of_constructible_mono
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    {M N : WeilModule D l X₀} (f : M ⟶ N) [Mono f]
    (hcM : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left M.carrier)
    (iota : PadicAlgCl l →+* ℂ) (w : ℝ) (hN : Mixed D l X₀ N iota w) :
    Mixed D l X₀ M iota w := by
  let T := (D.geometricFiber X₀).left
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace
    (pullback.snd X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian
    (pullback.snd X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
  have : IsNoetherian T := {}
  let Λ := Profinite.padicAlgClRingObj.{u} l
  let P₀ : ObjectProperty (NativeCondensedModule.Modules l T) :=
    IsConstantModelConstructible Λ T
  have cmp := (adicConstructibilityPredicateComparison l T Λ .algebraicClosure).1
  have : P₀.IsClosedUnderIsomorphisms := ⟨fun e h ↦ (cmp _).mp ((cmp _).mpr h |>.of_iso e)⟩
  have : P₀.ContainsZero := by
    obtain ⟨Z, hZ⟩ := (inferInstance : HasZeroObject (NativeCondensedModule.Modules l T)).zero
    exact ⟨⟨Z, hZ, (cmp _).mp (isConstructibleModuleObject_of_isZero _ hZ)⟩⟩
  obtain ⟨hk, hck, he, _, _, _, _⟩ :=
    (coefficientHeart_closure l (Profinite.padicAlgClCondensedRing l) (Or.inr rfl)).2 T
  let := hk
  let := hck
  let := he
  let V := Endofunctor.IsoAlgebra.forget
    (CondensedRing.upperStar Λ (D.geometricFrobenius X₀).hom)
  let Q : ObjectProperty (WeilModule D l X₀) := fun A ↦
    ∃ v : ℝ, v ≤ w ∧ Pure D l X₀ A iota v
  have : Q.IsClosedUnderSubobjects := ⟨fun g _ ⟨v, hv, hp⟩ ↦
    ⟨v, hv, Pure.of_mono D l X₀ g iota v hp⟩⟩
  exact filtration_subobject_inverseImage P₀ V Q f hcM hN

end WeilConjectures.NativeL2
