/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import WeilConjectures.RingTheory.AnnihilatorAssociatedPrimes
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Sheaf.RingTheory.LocalUniversalInjectiveResidue

/-!
# Relative associated primes of a projective module over a local base

Source: Stacks Project, More on Flatness, Tag 05FV (`lemma-explain-why-pure`)
(blueprint: lem-sfb-projective-local-fibre-assassin-specialization).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace RingTheory

/-- A relative fibre-associated prime of a module projective over a local base has
proper sum with the extended maximal ideal, provided the closed fibre is finite over
its Noetherian coefficient ring. No finite generation over the base is required.
The extended ideal is `Ideal.map (algebraMap R C) (IsLocalRing.maximalIdeal R)`;
its product with the whole module is precisely the submodule `mP`.
`PrimeSpectrum.comap` supplies the contracted prime and its canonical residue field.

Source: Stacks Project, More on Flatness, Tag 05FV (`lemma-explain-why-pure`)
(blueprint: lem-sfb-projective-local-fibre-assassin-specialization).

Proof:
1. Put `Pbar = P / mP` and let `Sigma` consist of scalars in `C` whose action on
   `Pbar` is injective. It contains one and is closed under multiplication. The
   projective module `P` is flat over `R` by lem-weil-pbc-projective-module-flat.
2. For `s` in `Sigma`, scalar multiplication on `P` is `R`-linear and is injective
   modulo `m`. Apply lem-trf-local-universal-injective-residue (Tag 05FQ), with
   source and target both `P`. Thus it remains injective after tensoring with
   every `R`-module, in particular the residue field of the contracted prime.
   The tensor flip conjugates left tensoring to right tensoring; on pure tensors
   this is exactly the `C`-action on `P` tensor the residue field. The tensor
   universal property (def-weil-pbc-module-tensor-product) proves the equality.
3. Choose an element `z` of that fibre whose exact annihilator is `q`, using
   def-weil-pbc-annihilator-associated-primes. Primality makes `q` proper, hence
   `z` is nonzero. No member of `Sigma` can annihilate `z`, by step 2, so `q`
   is disjoint from `Sigma`.
4. By lem-weil-pbc-localization-spectrum-embedding, `q` is the contraction of a
   prime of the localization at `Sigma`. Apply
   lem-sfb-fibre-regular-localization-spectrum (Tag 05DE), with its Noetherian
   closed-fibre ring and finite closed-fibre module hypotheses as in the statement.
   Its spectrum description gives `q ≤ q'` for an element-annihilator associated
   prime `q'` of `Pbar` as a `C`-module.
5. Every image of an element of `m` kills `Pbar`; therefore `mC ≤ q'`, by its
   annihilator witness. Hence `q + mC ≤ q' ≠ C`, proving the assertion.
-/
theorem fibre_associatedPrime_sup_maximalIdeal_ne_top_of_projective
    {R : Type u} {C : Type v} {P : Type w}
    [CommRing R] [IsLocalRing R] [CommRing C] [Algebra R C]
    [AddCommGroup P] [Module C P] [Module R P] [IsScalarTower R C P]
    [Module.Projective R P]
    [IsNoetherianRing (C ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R C))]
    [Module.Finite (C ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R C))
      (P ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R C) •
        (⊤ : Submodule C P)))]
    (q : PrimeSpectrum C)
    (hq : q.asIdeal ∈ annihilatorAssociatedPrimes C
      (P ⊗[R] (PrimeSpectrum.comap (algebraMap R C) q).asIdeal.ResidueField)) :
    q.asIdeal ⊔ (IsLocalRing.maximalIdeal R).map (algebraMap R C) ≠ ⊤ := by
  sorry

end RingTheory
