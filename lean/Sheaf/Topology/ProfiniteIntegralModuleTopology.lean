/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S7
-/
module

public import Sheaf.Topology.ProfiniteIntegralScalarDefinitions

/-! # Topology and reconstruction of finite integral modules

Source: HRS Example 3.1 and Remark 3.2, with the argument in
`lem-sfb-profinite-integral-scalar-realization`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct CategoryTheory.Obj

namespace Profinite.IntegralScalar

/-- Finite integral modules are profinite and are reconstructed by their positive reductions.

Source: HRS Example 3.1; the finite-presentation supplement, steps 1--3 of
`lem-sfb-profinite-integral-scalar-realization`.
(blueprint: lem-sfb-integral-finite-module-topology)

Proof: Diagonalize the kernel of a finite free presentation over the DVR using Smith
normal form. The quotient is a finite product of copies of O and O/π^e, ignoring zero
summands. Matrix maps in both directions are continuous. The quotient from finite free
O is continuous and surjective onto this compact Hausdorff product, hence is quotient.
Lifting finitely many generators between presentations shows this is moduleTopology.
The free factors have the positive reduction limit of the integer ring, coordinatewise.
A torsion factor O/π^e has quotients O/π^min(e,k+1), with the actual reduction maps;
its tower is constant from k+1=e. These identifications commute with all quotient maps,
so their finite product identifies the specified limitMap, including its topology.
Each level is finite discrete. Empty products give the zero module.
-/
theorem finite_module_topology (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    letI := spectralNorm.normedField (Padic l) E
    let O := Padic.coefficientExtensionIntegers l E
    let π := Padic.coefficientExtensionUniformizer l E
    ∀ (B : Type u) [AddCommGroup B] [Module O B] [Module.FinitePresentation O B],
      letI := moduleTopology O B
      CompactSpace B ∧ T2Space B ∧ TotallyDisconnectedSpace B ∧
      (∀ k : ℕ, Finite (residue O π B k) ∧ DiscreteTopology (residue O π B k)) ∧
      IsHomeomorph (limitMap O π B) := by sorry

end Profinite.IntegralScalar
