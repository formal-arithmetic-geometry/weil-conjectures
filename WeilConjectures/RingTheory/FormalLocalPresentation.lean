/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Formal presentations with a specified coefficient section

Source: Stacks Project, varieties.tex, Tag 0C52, and the presentation convention in
lem-trf-separable-closed-point-formal-presentation
(blueprint: def-trf-formal-local-presentation).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

namespace Algebra

/-- Maximal-ideal completion, using Mathlib's compatible-sequence construction.
Source: Stacks Project, Tag 0C52 (blueprint: def-trf-formal-local-presentation). -/
abbrev LocalCompletion (A : Type v) [CommRing A] [IsLocalRing A] :=
  AdicCompletion (IsLocalRing.maximalIdeal A) A

/-- A formal presentation includes its coefficient section, surjection, and chosen equations.
The constant compatibility makes the surjection an algebra map for the residue-field action
through the specified section. Continuity is expressed using powers of the variable ideal
and the extended maximal ideal, without choosing topological instances.
Source: Stacks Project, Tag 0C52; the harmless bound `2 ≤ n` is the dummy-variable convention
of lem-trf-separable-closed-point-formal-presentation
(blueprint: def-trf-formal-local-presentation). -/
structure FormalLocalPresentation (k : Type u) (A : Type v)
    [Field k] [CommRing A] [Algebra k A] [IsLocalRing A] where
  /-- Number of variables, with dummy variables allowed. -/
  n : ℕ
  /-- Number of chosen generators of the kernel, possibly zero. -/
  s : ℕ
  /-- The convention of at least two variables. -/
  two_le : 2 ≤ n
  /-- The specified coefficient-field section. -/
  sectionMap : IsLocalRing.ResidueField A →ₐ[k] LocalCompletion A
  /-- Reduction of the section is the identity on the residue field. -/
  section_residue : ∀ a : IsLocalRing.ResidueField A,
    AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal A) (sectionMap a) = a
  /-- The chosen surjection from the power series ring. -/
  map : MvPowerSeries (Fin n) (IsLocalRing.ResidueField A) →ₐ[k] LocalCompletion A
  /-- Compatibility with the chosen residue-field action. -/
  constants : ∀ a : IsLocalRing.ResidueField A, map (MvPowerSeries.C a) = sectionMap a
  /-- Surjectivity of the power series map. -/
  surjective : Function.Surjective map
  /-- The chosen kernel generators. -/
  relation : Fin s → MvPowerSeries (Fin n) (IsLocalRing.ResidueField A)
  /-- These equations generate exactly the kernel. -/
  kernel : RingHom.ker map.toRingHom = Ideal.span (Set.range relation)
  /-- All equations have zero constant term. -/
  kernel_le : RingHom.ker map.toRingHom ≤
    Ideal.span (Set.range (fun i : Fin n ↦
      (MvPowerSeries.X i : MvPowerSeries (Fin n) (IsLocalRing.ResidueField A))))
  /-- Continuity for the indicated adic topologies. -/
  adic_continuous : ∀ r : ℕ, ∃ N : ℕ,
    (Ideal.span (Set.range (fun i : Fin n ↦
      (MvPowerSeries.X i : MvPowerSeries (Fin n) (IsLocalRing.ResidueField A)))) ^ N).map
        map.toRingHom ≤
      ((IsLocalRing.maximalIdeal A).map (algebraMap A (LocalCompletion A))) ^ r

end Algebra
