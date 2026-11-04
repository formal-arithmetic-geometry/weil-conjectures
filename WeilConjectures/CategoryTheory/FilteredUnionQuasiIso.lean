/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.LinearAlgebra.FreeModule.Basic

public import WeilConjectures.CategoryTheory.FiniteFiltrationInduction

import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.HomologySequenceLemmas
/-!
# Quasi-isomorphisms from a filtered resolution union

Source: Stacks Project, More on Algebra, Tag 0H7X, lemma-resolution-filtered-complex,
proof, union and part (3) (blueprint: lem-pur-kunneth-filtered-union-quasiiso).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A basic filtered complex is degreewise free, with free filtered steps and free graded
pieces, and with zero differential.
Source: Stacks Project, More on Algebra, Tag 0H7X, lemma-resolution-filtered-complex,
proof, definition of a basic filtered complex
(blueprint: lem-pur-kunneth-filtered-union-quasiiso). -/
def IsBasicFilteredComplex {R : Type u} [CommRing R]
    (B : FilteredObject
      (CochainComplex (ModuleCat.{v} R) ℤ)) : Prop :=
  (∀ n : ℤ, Module.Free R (B.obj.X n)) ∧
    (∀ i n : ℤ, Module.Free R
      ((B.filtration.step i : CochainComplex (ModuleCat.{v} R) ℤ).X n)) ∧
    (∀ i n : ℤ, Module.Free R ((B.filtration.gradedPiece i).X n)) ∧
    (∀ n : ℤ, B.obj.d n (n + 1) = 0)

private theorem cycle_element {R : Type u} [CommRing R]
    (L : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℤ) (x : L.X n)
    (hx : L.d n (n + 1) x = 0) :
    ∃ z : L.cycles n, L.iCycles n z = x := by
  have hx' : (L.sc n).g x = 0 := by
    change L.d n ((ComplexShape.up ℤ).next n) x = 0
    rw [(ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl)]
    exact hx
  let z := (L.sc n).moduleCatCyclesIso.inv ⟨x, hx'⟩
  refine ⟨z, ?_⟩
  exact ConcreteCategory.congr_hom (L.sc n).moduleCatCyclesIso_inv_iCycles ⟨x, hx'⟩

private theorem union_quasiIso {R : Type u} [CommRing R]
    (P : ℕ → CochainComplex (ModuleCat.{v} R) ℤ)
    (inc : ∀ m, P m ⟶ P (m + 1))
    (K U : CochainComplex (ModuleCat.{v} R) ℤ)
    (f : ∀ m, P m ⟶ K) (j : ∀ m, P m ⟶ U) (fU : U ⟶ K)
    (hj : ∀ m, Mono (j m))
    (hincU : ∀ m, inc m ≫ j (m + 1) = j m)
    (hf : ∀ m, j m ≫ fU = f m)
    (hunion : ∀ (n : ℤ) (x : U.X n), ∃ (m : ℕ) (y : (P m).X n), (j m).f n y = x)
    (hzero : ∀ n, Epi (HomologicalComplex.homologyMap (f 0) n))
    (hkill : ∀ m n, kernel.ι (HomologicalComplex.homologyMap (f m) n) ≫
      HomologicalComplex.homologyMap (inc m) n = 0) : QuasiIso fU := by
  classical
  have hrep (n : ℤ) (x : U.homology n) :
      ∃ (m : ℕ) (y : (P m).homology n), HomologicalComplex.homologyMap (j m) n y = x := by
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (U.homologyπ n)).mp inferInstance x
    obtain ⟨m, y, hy⟩ := hunion n (U.iCycles n z)
    have : Mono (j m) := hj m
    have hycycle : (P m).d n (n + 1) y = 0 := by
      apply (ModuleCat.mono_iff_injective ((j m).f (n + 1))).mp inferInstance
      have hw := ConcreteCategory.congr_hom ((j m).comm n (n + 1)) y
      have hz := ConcreteCategory.congr_hom (U.iCycles_d n (n + 1)) z
      simp only [ModuleCat.comp_apply] at hw hz
      rw [hy] at hw
      simpa only [map_zero, ModuleCat.hom_zero, LinearMap.zero_apply] using hw.symm.trans hz
    obtain ⟨c, hc⟩ := cycle_element (P m) n y hycycle
    have hcmap : HomologicalComplex.cyclesMap (j m) n c = z := by
      apply (ModuleCat.mono_iff_injective (U.iCycles n)).mp inferInstance
      have hw := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i (j m) n) c
      simpa only [ModuleCat.comp_apply, hc, hy] using hw
    refine ⟨m, (P m).homologyπ n c, ?_⟩
    have hw := ConcreteCategory.congr_hom
      (HomologicalComplex.homologyπ_naturality (j m) n) c
    simpa only [ModuleCat.comp_apply, hcmap] using hw
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap, isIso_iff_mono_and_epi]
  constructor
  · rw [ModuleCat.mono_iff_injective]
    apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    obtain ⟨m, y, hy⟩ := hrep n x
    have hfmap := congrArg (fun a ↦ HomologicalComplex.homologyMap a n) (hf m)
    rw [HomologicalComplex.homologyMap_comp] at hfmap
    have hyzero : HomologicalComplex.homologyMap (f m) n y = 0 := by
      rw [← hfmap, ModuleCat.comp_apply, hy, hx]
    let c := (ModuleCat.kernelIsoKer (HomologicalComplex.homologyMap (f m) n)).inv
      ⟨y, hyzero⟩
    have hc : kernel.ι (HomologicalComplex.homologyMap (f m) n) c = y :=
      ConcreteCategory.congr_hom
        (ModuleCat.kernelIsoKer_inv_kernel_ι (HomologicalComplex.homologyMap (f m) n))
        ⟨y, hyzero⟩
    have hykill : HomologicalComplex.homologyMap (inc m) n y = 0 := by
      have hw := ConcreteCategory.congr_hom (hkill m n) c
      simpa only [ModuleCat.comp_apply, hc, ModuleCat.hom_zero, LinearMap.zero_apply] using hw
    have hjmap := congrArg (fun a ↦ HomologicalComplex.homologyMap a n) (hincU m)
    rw [HomologicalComplex.homologyMap_comp] at hjmap
    rw [← hy, ← hjmap, ModuleCat.comp_apply, hykill, map_zero]
  · have : Epi (HomologicalComplex.homologyMap (f 0) n) := hzero n
    exact epi_of_epi_fac
      (f := HomologicalComplex.homologyMap (j 0) n)
      (h := HomologicalComplex.homologyMap (f 0) n) (by
        simpa only [← HomologicalComplex.homologyMap_comp] using
          congrArg (fun a ↦ HomologicalComplex.homologyMap a n) (hf 0))

-- The construction hypotheses are retained in the public statement.
end CategoryTheory
