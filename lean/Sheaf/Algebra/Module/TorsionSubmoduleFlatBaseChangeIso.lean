/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Sheaf.Algebra.Module.QuotientPrimaryComponentNoTorsion
import Sheaf.Paper.TorsionModuleFlatBaseChangeIso

/-!
# Flat base change of an ideal-power torsion submodule

Source: More on Algebra, Lemma 05EC, part (1)
(blueprint: lem-weil-pbc-torsion-submodule-flat-base-change-iso).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

/-- For a flat ring map inducing an isomorphism modulo a finitely generated ideal,
base change identifies the ideal-power torsion submodule.

Source: More on Algebra, Lemma 05EC, part (1)
(blueprint: lem-weil-pbc-torsion-submodule-flat-base-change-iso).
Proof (the seven blueprint steps):
Mathlib writes scalar extension as `S ⊗[R] M` (the convention of `LinearMap.baseChange`,
the recorded declaration of def-weil-module-base-change); tensor symmetry identifies it
with the source's `M ⊗_R S`, and `m ↦ m ⊗ 1` becomes `m ↦ 1 ⊗ m`.
1. Scalar compatibility of `m ↦ 1 ⊗ m` (def-weil-module-base-change) sends every
   element annihilated by a power of I to one annihilated by the same power;
   `Ideal.primaryComponent.map` is precisely this restriction.
2. Put T = M[I^∞] and M' = M/T. The finitely generated ideal hypothesis gives
   M'[I] = 0 (lem-weil-pbc-quotient-by-power-torsion-no-torsion). Induct on n:
   if I^n x = 0, each element of I^(n-1) x is killed by I, hence is zero;
   induction then gives x = 0. Thus M'[I^∞] = 0.
3. Write I = (f₁, …, fₜ). For n > 0 the map x ↦ (fₖ^n x)ₖ on M' is injective:
   its kernel is annihilated by I^(t(n-1)+1), since every monomial of that degree
   has some exponent at least n. If t = 0, I = 0 and M' = 0.
4. Flatness (def-weil-pbc-flat-ring-map) preserves this injection after tensoring.
   Tensoring commutes with the finite product (lem-weil-pbc-tensor-finite-product),
   so the resulting injection is y ↦ (fₖ^n y)ₖ. Any I-power torsion element of
   M' ⊗ S is in its kernel, hence is zero.
5. Tensor the exact sequence 0 → T → M → M' → 0. Flatness preserves the first
   injection; right exactness (lem-weil-pbc-tensor-right-exact) gives exactness
   of 0 → T ⊗ S → M ⊗ S → M' ⊗ S → 0.
6. Since T is I-power torsion, T → T ⊗ S is bijective by
   lem-weil-pbc-torsion-module-flat-base-change-iso, using flatness and the
   isomorphism R/I → S/IS.
7. The comparison is the composite of this bijection with the injection in step 5,
   so is injective. A torsion element y of M ⊗ S has zero image in M' ⊗ S by
   step 4. Exactness lifts it to T ⊗ S, and step 6 writes this lift as x ⊗ 1
   for x ∈ T. This proves surjectivity. -/
theorem Ideal.primaryComponent_baseChange_bijective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] (I : Ideal R) (hI : I.FG)
    (hflat : RingHom.Flat (algebraMap R S))
    (hquot : Function.Bijective
      (Ideal.quotientMap (Ideal.map (algebraMap R S) I)
        (algebraMap R S) Ideal.le_comap_map))
    (M : Type w) [AddCommGroup M] [Module R M] :
    Function.Bijective
      ((Ideal.primaryComponent.map I (TensorProduct.mk R S M 1)) :
        Ideal.primaryComponent M I →ₗ[R]
          Ideal.primaryComponent (S ⊗[R] M) I) := by
  sorry
