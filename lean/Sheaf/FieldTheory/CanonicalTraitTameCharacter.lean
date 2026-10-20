/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.FieldTheory.TameRootsProduct
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.GroupTheory.Index
import Sheaf.FieldTheory.CanonicalTameCharacterData
import Sheaf.FieldTheory.CanonicalTameCharacterStructure

/-!
# The canonical tame character of a strictly henselian trait

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVII, section 1.2,
printed page 259; Stacks Project, Tag 0BUB
(blueprint: lem-per-trait-tame-algebra).

The inverse limit and its topology are the existing `TameRoots.limitSubgroup` and
`TameRoots.limitTopology`. The coordinate formula specifies one map simultaneously for
all uniformizers and compatible root choices. Exactness uses its actual subgroup kernel.
-/

@[expose] public section

set_option autoImplicit false

universe u v w z q

namespace IsDiscreteValuationRing

/-- The canonical continuous tame character is surjective, has pro-p kernel (trivial
in residue characteristic zero), and its target has compatible primitive generators.
Source: Travaux de Gabber, Expose XVII, section 1.2, printed page 259; Stacks Tag 0BUB
(blueprint: lem-per-trait-tame-algebra).

Proof: Construct the finite canonical Kummer characters using Hensel roots of units,
Eisenstein irreducibility, and normality of the separable closure. Compactness assembles
them into the continuous surjective inverse-limit character and compatible radical
families. Identify its kernel with the subgroup fixing one radical tower. Its finite
Galois images are p-groups by the finite normalization and telescoping argument; the Krull
neighborhood basis then proves the finite-quotient assertion and the characteristic-zero
kernel assertion. Finite inverse-system compactness gives compatible primitive roots, and
the coordinate neighborhood basis proves density and the exact index of each power closure. -/
theorem exists_canonical_tame_character
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsStrictlyHenselianLocalRing R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (Ksep : Type w) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (Ω : Type z) [Field Ω] [IsAlgClosed Ω] [Algebra Ksep Ω]
    (p : ℕ) (hp : p = if ringChar (IsLocalRing.ResidueField R) = 0 then 1
      else ringChar (IsLocalRing.ResidueField R)) :
    ∃ t : Gal(Ksep/K) →* TameRoots.limitSubgroup Ω p,
      @Continuous _ _ inferInstance (TameRoots.limitTopology Ω p) t ∧
      Function.Surjective t ∧
      (∀ π : R, Irreducible π →
        ∃ α : TameRoots.Order p → Ksep,
          (∀ d : TameRoots.Order p,
            α d ^ d.1 = algebraMap K Ksep (algebraMap R K π)) ∧
          ∀ d e : TameRoots.Order p, d.1 ∣ e.1 → α e ^ (e.1 / d.1) = α d) ∧
      (∀ (π : R), Irreducible π → ∀ α : TameRoots.Order p → Ksep,
        (∀ d : TameRoots.Order p,
          α d ^ d.1 = algebraMap K Ksep (algebraMap R K π)) →
        (∀ d e : TameRoots.Order p, d.1 ∣ e.1 → α e ^ (e.1 / d.1) = α d) →
        ∀ (h : Gal(Ksep/K)) (d : TameRoots.Order p),
          (((t h).1 d : Ωˣ) : Ω) = algebraMap Ksep Ω (h (α d) / α d)) ∧
      (∀ (Q : Type q) [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q]
        (f : t.ker →* Q), Continuous f → Function.Surjective f →
          ∃ n : ℕ, Nat.card Q = p ^ n) ∧
      (p = 1 → t.ker = ⊥) ∧
      (∃ σ : TameRoots.limitSubgroup Ω p,
        TameRoots.IsCompatiblePrimitiveFamily p σ.1) ∧
      ∀ σ : TameRoots.limitSubgroup Ω p,
        TameRoots.IsCompatiblePrimitiveFamily p σ.1 →
        @DenseRange (TameRoots.limitSubgroup Ω p) (TameRoots.limitTopology Ω p) ℤ
          (fun n : ℤ ↦ σ ^ n) ∧
        ∀ d : TameRoots.Order p,
          ∃ U : Subgroup (TameRoots.limitSubgroup Ω p),
            (U : Set (TameRoots.limitSubgroup Ω p)) =
              @closure _ (TameRoots.limitTopology Ω p)
                (Set.range (fun n : ℤ ↦ (σ ^ d.1) ^ n)) ∧
            U.index = d.1 := by
  obtain ⟨t, ht, hs, ha, hf⟩ := canonical_tame_character_data R K Ksep Ω p hp
  obtain ⟨hq, hc, hprim, htop⟩ := canonical_tame_character_structure
    R K Ksep Ω p hp t ht hs ha hf
  exact ⟨t, ht, hs, ha, hf, hq, hc, hprim, htop⟩

end IsDiscreteValuationRing
