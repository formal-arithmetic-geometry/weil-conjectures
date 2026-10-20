/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.FieldTheory.TameRootsProduct
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology

import Sheaf.FieldTheory.FiniteRadicalRestriction
import Mathlib.FieldTheory.Galois.Profinite

/-! The Galois subgroup fixing all prime-to-residue-characteristic uniformizer radicals. -/

@[expose] public section
set_option autoImplicit false
universe u v w q
namespace IsDiscreteValuationRing

/-- The subgroup fixing the specified uniformizer radical tower, as an intersection of
actual stabilizers in the absolute Galois group.
Source: Stacks Project, pione.tex Tag 0BUB (blueprint: def-per-tame-radical-kernel). -/
def tameRadicalKernel {K : Type v} [Field K] {Ksep : Type w} [Field Ksep]
    [Algebra K Ksep] {p : ℕ} (α : TameRoots.Order p → Ksep) : Subgroup Gal(Ksep/K) :=
  ⨅ d, MulAction.stabilizer Gal(Ksep/K) (α d)

/-- The radical tower has pro-p absolute Galois kernel, trivial in residue characteristic zero.
Source: Stacks Project, pione.tex Tags 0BUA and 0BUB; more-algebra.tex Tag 09EE.
(blueprint: lem-per-tame-radical-kernel).

Proof: The finite radical-restriction theorem says that the image on every finite normal
subextension is a p-group, including the trivial group when p=1. A continuous map of the
radical kernel to a finite discrete group has an open kernel at the identity. The Krull
neighborhood basis supplies a finite normal subfield L whose fixing subgroup, intersected
with the radical kernel, lies in this open kernel. Descend the map through the image of
restriction to L; this image is a finite p-group, and its surjective image has p-power
cardinality. For p=1 its cardinality is one. To prove the subgroup itself trivial in this
case, place any element of Ksep in the finite Galois closure of its simple extension.
The restriction image is a 1-group and hence trivial, so every radical-fixing automorphism
fixes that element. Extensionality gives the identity automorphism. -/
theorem tame_radical_kernel_pro_p
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsStrictlyHenselianLocalRing R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (Ksep : Type w) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (p : ℕ) (hp : p = if ringChar (IsLocalRing.ResidueField R) = 0 then 1
      else ringChar (IsLocalRing.ResidueField R))
    (π : R) (hπ : Irreducible π) (α : TameRoots.Order p → Ksep)
    (hα : ∀ d : TameRoots.Order p,
      α d ^ d.1 = algebraMap K Ksep (algebraMap R K π))
    (hαc : ∀ d e : TameRoots.Order p, d.1 ∣ e.1 → α e ^ (e.1 / d.1) = α d) :
    (∀ (Q : Type q) [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
      [Finite Q] (f : tameRadicalKernel (K := K) α →* Q),
      Continuous f → Function.Surjective f → ∃ n : ℕ, Nat.card Q = p ^ n) ∧
    (p = 1 → tameRadicalKernel (K := K) α = ⊥) := by
  classical
  let S := tameRadicalKernel (K := K) α
  have hfinite (L : IntermediateField K Ksep) [FiniteDimensional K L] [Normal K L] :
      IsPGroup p (((AlgEquiv.restrictNormalHom L).comp S.subtype).range) :=
    finite_radical_restriction_p_group R K Ksep p hp π hπ α hα hαc L
  constructor
  · intro Q _ _ _ _ f hf hfs
    have hnhds : {x : S | f x = 1} ∈ nhds (1 : S) :=
      ((isOpen_discrete ({1} : Set Q)).preimage hf).mem_nhds (map_one f)
    rw [nhds_subtype] at hnhds
    obtain ⟨V, hV, hVK⟩ := Filter.mem_comap.mp hnhds
    obtain ⟨L, hfin, hnorm, hLV⟩ :=
      (krullTopology_mem_nhds_one_iff_of_normal K Ksep V).mp hV
    let := hfin
    let := hnorm
    let ρ : S →* Gal(L/K) := (AlgEquiv.restrictNormalHom L).comp S.subtype
    have hle : ρ.ker ≤ f.ker := by
      intro x hx
      apply hVK
      apply hLV
      rw [← L.restrictNormalHom_ker]
      exact hx
    let φ : ρ.range →* Q := ρ.rangeRestrict.liftOfSurjective ρ.rangeRestrict_surjective
      ⟨f, by simpa only [MonoidHom.ker_rangeRestrict] using hle⟩
    have hφ (x : S) : φ (ρ.rangeRestrict x) = f x :=
      MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x
    have hφsurj : Function.Surjective φ := by
      intro q
      obtain ⟨x, rfl⟩ := hfs q
      exact ⟨ρ.rangeRestrict x, hφ x⟩
    have hQ : IsPGroup p Q := (hfinite L).of_surjective φ hφsurj
    by_cases h : ringChar (IsLocalRing.ResidueField R) = 0
    · have hp1 : p = 1 := by simpa [h] using hp
      obtain ⟨n, hn⟩ := hQ.exists_card_dvd_pow
      refine ⟨0, ?_⟩
      have hcard : Nat.card Q = 1 := Nat.dvd_one.mp (by simpa [hp1] using hn)
      simpa using hcard
    · have hp' : p = ringChar (IsLocalRing.ResidueField R) := by simpa [h] using hp
      have hprime : p.Prime := hp' ▸
        (CharP.char_is_prime_or_zero (IsLocalRing.ResidueField R)
          (ringChar (IsLocalRing.ResidueField R))).resolve_right h
      let : Fact p.Prime := ⟨hprime⟩
      exact hQ.exists_card_eq
  · intro hp1
    apply le_antisymm _ bot_le
    intro h hh
    change h = 1
    apply AlgEquiv.ext
    intro x
    let L := FiniteGaloisIntermediateField.adjoin K ({x} : Set Ksep)
    have hres : (AlgEquiv.restrictNormalHom L) h = 1 := by
      have hP := hfinite L
      rw [hp1, isPGroup_one_iff_subsingleton] at hP
      let := hP
      let ρ : S →* Gal(L/K) := (AlgEquiv.restrictNormalHom L).comp S.subtype
      exact congrArg Subtype.val (Subsingleton.elim (ρ.rangeRestrict ⟨h, hh⟩) 1)
    have hx : x ∈ L.toIntermediateField := FiniteGaloisIntermediateField.subset_adjoin K _
      (by simp)
    have heq := congrArg (fun σ : Gal(L/K) ↦ ((σ ⟨x, hx⟩ : L) : Ksep)) hres
    simpa only [AlgEquiv.restrictNormalHom_apply, AlgEquiv.restrictNormal_apply,
      AlgEquiv.one_apply] using heq


end IsDiscreteValuationRing
