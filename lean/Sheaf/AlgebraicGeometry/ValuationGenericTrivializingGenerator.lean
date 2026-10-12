/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.ValuationProperCoherentSections
import Sheaf.AlgebraicGeometry.FlatInvertibleSectionsTorsionFree
import Sheaf.AlgebraicGeometry.FractionFieldSectionsBaseChange
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # A generic trivializing generator over a valuation ring

Source: Stacks Project, More on Morphisms, Tag 0EX8, general-case proof, first paragraph.
(blueprint: lem-sc-valuation-generic-trivializing-generator)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

/-- Global sections have an A-basis whose zero scheme has empty generic fibre.

Source: Stacks Project, More on Morphisms, Tag 0EX8, general-case proof through the
choice of a generator of H⁰(X,L).
(blueprint: lem-sc-valuation-generic-trivializing-generator)

Proof: Proper coherent cohomology makes H⁰(X,L) finitely presented over A. Flatness
of X/A and local freeness of L make multiplication by each nonzero element of A
injective on L and hence on its global sections. A finitely presented torsion-free
module over a valuation ring is finite free. Flat base change to K identifies its
scalar extension with H⁰(X_K,L_K). Triviality of L_K and the canonical global-function
isomorphism identify this last module with K, so the free module has rank one.
Choose an A-basis s. Its base change is a K-basis of H⁰(X_K,L_K); under a trivialization
it is a nonzero scalar in K. Multiplication by this scalar trivializes L_K, so its
zero ideal is the unit ideal. Zero schemes commute with pullback, giving the last
clause. No integrality assumption on the closed fibre is used here. -/
theorem exists_generic_trivializing_generator
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of A))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (L : X.Modules) [L.IsInvertible]
    (hglobal : IsIso (pullback.snd f (Spec.map
      (CommRingCat.ofHom (algebraMap A K)))).appTop)
    (htriv : Nonempty ((tensorPullback
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A K))))).obj L ≅
      SheafOfModules.unit _)) :
    ∃ s : Γ(L, ⊤),
      Function.Bijective (fun a : A ↦
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom a • s) ∧
      (Hom.zeroLocus (homOfGlobalSection L s)).comap
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A K)))) = ⊤ := by
  classical
  let r := ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom
  let R := ModuleCat.restrictScalars r
  let M := R.obj ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj L)
  have hfp := finitePresentation_moduleCohomology_zero_of_valuationRing f L
  let : EnoughInjectives (SheafOfModules (moduleRings X.toRingedSpace)) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let S := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let : PreservesFiniteLimits S := inferInstanceAs
    (PreservesFiniteLimits (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)))
  have : Module.FinitePresentation A (R.obj ((S.rightDerived 0).obj L)) := hfp
  let e0 := R.mapIso (S.rightDerivedZeroIsoSelf.app L)
  have : Module.FinitePresentation A M :=
    Module.FinitePresentation.of_equiv e0.toLinearEquiv
  have htors : Submodule.torsion A M = ⊥ := by
    apply le_antisymm _ bot_le
    rintro s ⟨⟨a, ha⟩, hs⟩
    change s = 0
    apply injective_smul_sections_of_flat A f L a (nonZeroDivisors.ne_zero ha)
    exact hs.trans (smul_zero _).symm
  have : Module.Flat A M :=
    (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout).2 htors
  have : Module.Free A M := Module.free_of_flat_of_isLocalRing
  let b := Module.finBasis A M
  let g := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A K)))
  let fK := pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A K)))
  let rK := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ fK.appTop).hom
  let MK := (ModuleCat.restrictScalars rK).obj
    ((SheafOfModules.evaluation _ (Opposite.op ⊤)).obj ((Modules.pullback g).obj L))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨e, he⟩ := exists_fractionField_sections_baseChange A K f L
  let bK : Module.Basis (Fin (Module.finrank A M)) K MK := (b.baseChange K).map e
  obtain ⟨adj⟩ := nonempty_tensorPullbackAdjunction g
  obtain ⟨t⟩ := htriv
  let tK : (Modules.pullback g).obj L ≅ SheafOfModules.unit _ :=
    ((adj.leftAdjointUniq (pullbackPushforwardAdjunction g)).app L).symm ≪≫ t
  have : IsIso fK.appTop := hglobal
  let qK := (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ fK.appTop
  have hq : Function.Bijective qK.hom := ConcreteCategory.bijective_of_isIso qK
  let EK := (ModuleCat.restrictScalars rK).mapIso
    ((SheafOfModules.evaluation _ (Opposite.op ⊤)).mapIso tK)
  let lK : K →ₗ[K] MK :=
    { toFun := fun k ↦ EK.inv (qK.hom k)
      map_add' := fun a b ↦ by simp
      map_smul' := fun a b ↦ by
        change EK.inv.hom (qK.hom (a * b)) = a • EK.inv.hom (qK.hom b)
        rw [← EK.inv.hom.map_smul]
        exact congrArg EK.inv.hom (map_mul qK.hom a b) }
  have hlK : Function.Bijective lK :=
    (ConcreteCategory.bijective_of_isIso EK.inv).comp hq
  have hdim : Module.finrank K MK = 1 :=
    (LinearEquiv.ofBijective lK hlK).finrank_eq.symm.trans (Module.finrank_self K)
  obtain ⟨uniq⟩ := bK.nonempty_unique_index_of_finrank_eq_one hdim
  let : Unique (Fin (Module.finrank A M)) := uniq
  let i : Fin (Module.finrank A M) := default
  let s : Γ(L, ⊤) := b i
  have hs : Function.Bijective (fun a : A ↦ r a • s) := by
    change Function.Bijective (fun a : A ↦ a • b i)
    constructor
    · intro a a' h
      have h' := congrArg (fun m ↦ b.repr m i) h
      simpa using h'
    · intro m
      refine ⟨b.repr m i, ?_⟩
      have h := b.sum_repr m
      simpa [s, i] using h
  have hbK : bK i ≠ 0 := bK.ne_zero i
  let c : Γ(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap A K))), ⊤) :=
    tK.hom.app ⊤ (bK i)
  have hc : c ≠ 0 := by
    intro h
    apply hbK
    exact (ConcreteCategory.bijective_of_isIso (tK.hom.app ⊤)).1 (h.trans (map_zero _).symm)
  obtain ⟨k, hk⟩ := hq.2 c
  have hk0 : k ≠ 0 := by
    intro h
    apply hc
    simpa [h] using hk.symm
  have hcu : IsUnit c := hk ▸ (isUnit_iff_ne_zero.mpr hk0).map qK.hom
  have hcgen : IsFreeGenerator (M := Modules.unit _) (U := ⊤) c := by
    simpa using (isFreeGenerator_one ⊤).units_smul hcu.unit
  have hgen : IsFreeGenerator (M := (Modules.pullback g).obj L) (U := ⊤) (bK i) := by
    have h := hcgen.app_hom tK.symm
    change IsFreeGenerator ((tK.hom ≫ tK.inv).app ⊤ (bK i)) at h
    simpa using h
  let eN : Γ((Modules.pullback g).obj L, ⊤) :=
    ((pullbackPushforwardAdjunction g).unit.app L).app ⊤ s
  have heN : bK i = eN := by
    change e ((b.baseChange K) i) = _
    simpa [s, eN] using he s
  rw [heN] at hgen
  let eM : Γ((Modules.pullback g).obj (Modules.unit X), ⊤) :=
    ((pullbackPushforwardAdjunction g).unit.app (Modules.unit X)).app ⊤ (1 : Γ(X, ⊤))
  have heM : IsFreeGenerator eM :=
    (isFreeGenerator_one ⊤).pullback_unit_app_top g
  let φ := (Modules.pullback g).map (homOfGlobalSection L s)
  have hφ : φ.app ⊤ eM = eN := by
    have h := congrArg (fun ψ : Modules.unit X ⟶
        (pushforward g).obj ((Modules.pullback g).obj L) ↦
          Hom.app ψ ⊤ (1 : Γ(X, ⊤)))
      ((pullbackPushforwardAdjunction g).unit.naturality (homOfGlobalSection L s))
    simp only [Functor.id_map, Functor.comp_map, Hom.comp_app, ConcreteCategory.comp_apply,
      pushforward_map_app] at h
    erw [homOfGlobalSection_app_one, presheaf_map_id_apply] at h
    exact h.symm
  have : SheafOfModules.IsInvertible.{u, u, u} (Modules.unit X) :=
    IsInvertible.sheafOfModules_isInvertible (MonoidalCategoryStruct.tensorUnit X.Modules)
  have : SheafOfModules.IsInvertible.{u, u, u} L :=
    IsInvertible.sheafOfModules_isInvertible L
  have : SheafOfModules.IsInvertible.{u, u, u} ((Modules.pullback g).obj (Modules.unit X)) :=
    .pullback inferInstance
  have : SheafOfModules.IsInvertible.{u, u, u} ((Modules.pullback g).obj L) :=
    .pullback inferInstance
  refine ⟨s, hs, ?_⟩
  rw [Hom.comap_zeroLocus]
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Hom.ideal_zeroLocus φ U (heM.map le_top) (hgen.map le_top) (b := 1)]
  · simp
  · rw [Hom.app_presheaf_map, hφ, one_smul]

end AlgebraicGeometry.Scheme.Modules
