## What changed

Proved `CochainComplex.exists_localized_homotopyEquiv_zero_degree` with its original
signature, universes, and visibility unchanged. Its proof builds a nullhomotopic idempotent
supported in three degrees, applies the proved source library's kernel-complex API, and
transports the kernel complex so that untouched objects are literally equal to the original
objects. It proves the differential HEq, neighboring retractions, finiteness, and preservation
of every originally zero term.

Added two fully proved modules, with one public theorem each:

- `Sheaf.Algebra.Homology.LocalizedExactPairContraction`, containing
  `ModuleCat.exists_localized_exact_pair_contraction`: compare the two residue fields, form
  the bounded three-term complex over the prime localization, apply the proved source
  minimal-complex theorem, use Nakayama, and read its homotopy components.
- `Sheaf.Algebra.Homology.PrincipalContractionSpreading`, containing
  `ModuleCat.exists_principal_contraction_of_atPrime`: clear the denominators of the local
  maps and the error in their middle identity; spread free bases of the cokernels of the
  resulting scaled projectors; identify those cokernels with the desired kernels; normalize
  the maps and transport back to categorical extension of scalars.

All added proof dependencies are ordinary, non-public imports. No existing statement or
definition was changed, and no consumer adaptation or change record is needed.

## Proved and sorry left

Closed the original hole in
`CochainComplex.exists_localized_homotopyEquiv_zero_degree`
(node `lem-weil-pbc-free-complex-residue-degree-cancellation`).

Also fully proved the two new public theorems:
`ModuleCat.exists_localized_exact_pair_contraction`
(node `lem-weil-pbc-localized-exact-pair-contraction`) and
`ModuleCat.exists_principal_contraction_of_atPrime`
(node `lem-weil-pbc-principal-contraction-spreading`).

Original holes closed: **1 of 1**. Holes added: **0**. Sorries remaining in every delivered
module: **0**. No unfinished statement is split off. Every private helper is proved, and the
private tensor comparison definitions contain actual constructed data.

Validation: all three modules compile together through `lcompile.py --all`, and the delivery
dry run passes compilation and preflight. `#print axioms` for all three public theorems reports
exactly `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

No original Sheaf proof-dependency import is removed: the original module had no such
imports, and its stated dependencies were definitions, all still needed. No existing module
is withdrawn or claimed to become globally unreachable.

The original six-step pivot induction, including residue-field invariance at every pivot,
composition of successive cancellation homotopies, and a rank-decrease induction on the
unbounded complex, is unnecessary. The node now records one adjacent-pair lemma and a
three-degree idempotent instead. The bounded minimal-complex theorem is used only on the
auxiliary three-term complex, so no boundedness assumption is imposed on the original complex.

The new pair and spreading modules expose only the imports needed by their statements.
Their proofs use the existing `WeilConjectures.Algebra.Homology.MinimalComplex` module and
Mathlib's exactness, localization, finite-presentation, tensor finiteness/freeness, residue-field,
and additive-adjunction APIs. No other planned cancellation node or module is imported.

## Where the brief, the DAG or earlier work was wrong

No false statement, target change, hollow definition, or forced consumer adaptation was found.
The DAG's elementary pivot proof is mathematically adequate but unnecessary given the proved
source library. The existing `ModuleCat.tensorEquivExtendScalars` has module universe equal
to the ring universe; this item's module universe is `max u v`. Private, explicitly constructed
universe-general versions supply the required comparison without changing that existing API.

## New nodes

`lem-weil-pbc-localized-exact-pair-contraction` records the proved adjacent-pair algebra
interface. It separates the residue/local-ring argument from the original complex and its
preservation clauses.

`lem-weil-pbc-principal-contraction-spreading` records the proved denominator-clearing and
local-freeness step. It assumes a middle contraction over the prime localization and the
square-zero relation, and has no residue-field criterion or complex-level conclusion.
Both nodes inherit the proper-base-change unit and trace their blueprint origin through the
original cancellation node. No change record is required.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
