/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q147
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.RingTheory.AnnihilatorAssociatedPrimes
import Sheaf.RingTheory.UniversalInjectiveFiniteTest
import Sheaf.TraceFormula.AssociatedPrimesFibreBound
import Sheaf.RingTheory.KrullIntersectionLocalization
import WeilConjectures.RingTheory.InjectivePiLocalizationAssociatedPrimes
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# Universal injectivity of a flat module into its adic completion

Source: Stacks Project, More on Flatness, Tag 05DM,
`lemma-universally-injective-to-completion-flat`
(blueprint: lem-trf-flat-completion-universally-injective).
-/

@[expose] public section

set_option autoImplicit false

universe u v w x

open scoped TensorProduct

namespace RingTheory

/-- A finite module over a Noetherian algebra, flat over the Noetherian base, maps
universally injectively into its adic completion when every associated prime of its
corresponding residue-field fibre has proper sum with the extended ideal.
The fibre has the canonical scalar action through its first tensor factor.
`AdicCompletion I P` consists of compatible families in `P / I^n P`, with componentwise
operations. Its extra coordinate at `n = 0` is the unique element of `P / P`, so it is
exactly the inverse limit over positive powers in the statement. `AdicCompletion.of I P`
sends an element to its family of residue classes.

Source: Stacks Project, More on Flatness, Tag 05DM,
`lemma-universally-injective-to-completion-flat`
(blueprint: lem-trf-flat-completion-universally-injective).

Proof, following the six steps of the node:
1. By `lem-trf-universal-injective-finite-test`, it suffices to tensor with finite
   base modules `Q`; Noetherianity makes them finitely presented.
2. Quotient maps induce the canonical map from the tensor with the completion to
   the completion of `Q ⊗ P`. Its composite with the tensor of the completion map is
   the completion map of `M = Q ⊗ P`. Injectivity of the latter suffices.
3. `M` is finite over `S`. The kernel `K` of its completion map is the intersection
   of the positive powers of `IS` times `M`. By
   `lem-weil-pbc-module-injects-localizations-associated-primes`, it suffices to kill
   the image of each element of `K` at every associated prime of `M`.
4. For such a prime `q`, `lem-trf-associated-primes-fibre-bound` places `q` among
   the associated primes of the corresponding fibre of `P`. The hypothesis gives
   `IS + q ≠ S`; `lem-weil-pbc-minimal-prime-over-proper-ideal` supplies a prime
   `q'` containing that sum.
5. Apply `lem-weil-pbc-krull-intersection-localization` over `S` at `q'`. The
   intersection including power zero is still `K`. It gives `f` outside `q'`
   with `K_f = 0`. Since `q ≤ q'`, also `f` is outside `q`. Each element of `K`
   is killed by a power of `f`, hence vanishes at `q`, by
   `def-weil-pbc-module-localization`.
6. Detection at associated primes gives `K = 0`. The comparison in step 2 proves
   injectivity for finite tensor factors, and step 1 gives all tensor factors.
-/
theorem flat_completion_universally_injective
    (R : Type u) (S : Type v) (P : Type w) [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup P] [Module S P] [Module R P]
    [IsScalarTower R S P] [IsNoetherianRing R] [IsNoetherianRing S]
    [Module.Finite S P] [Module.Flat R P] (I : Ideal R)
    (hassoc : ∀ (p : PrimeSpectrum R) (q : PrimeSpectrum S),
      q.asIdeal.comap (algebraMap R S) = p.asIdeal →
      q.asIdeal ∈ annihilatorAssociatedPrimes S (P ⊗[R] p.asIdeal.ResidueField) →
      Ideal.map (algebraMap R S) I ⊔ q.asIdeal ≠ ⊤) :
    ∀ (Q : Type (max u v w x)) [AddCommGroup Q] [Module R Q],
      Function.Injective ((AdicCompletion.of I P).rTensor Q) := by
  sorry

end RingTheory
