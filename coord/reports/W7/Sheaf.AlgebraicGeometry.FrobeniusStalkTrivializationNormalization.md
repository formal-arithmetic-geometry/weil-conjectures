## What changed

Proved `AlgebraicGeometry.Scheme.frobeniusStalkTrivializationNormalization` in
`Sheaf.AlgebraicGeometry.FrobeniusStalkTrivializationNormalization` from the existing
Frobenius trivialization and pullback-stalk coherence declarations. The public theorem
signature is unchanged. Refactored `FrobeniusStalkTrivializationNormalized` into explicit
clause predicates with map and point parameters; the normalization formulas,
data and boundedness hypotheses are preserved. Named proved point-equality lemmas replace
repeated inline proof terms. The reparametrization source is written explicitly as
`𝟙 _ ≫ z`, the same point used by its comparison. The definition change is recorded in
`coord/changes/frobenius-stalk-normalization-predicates.md`.

The proof constructs the inverse-Frobenius pointed lift, evaluates the specified
adjunction-unit section, and uses the pointed colimit relation. Surjectivity of germ
representatives gives equality of module maps. A general exact-functor calculation
then gives the specified derived equality, including its equality transports.
The pullback compatibility clauses come directly from the existing coherence theorem.
The calculation helpers are private and proved in this module. The clause predicates and
two point-equality lemmas are public because the public definition uses them;
they introduce no postponed proof or chosen data.

Added proof imports `Mathlib.FieldTheory.Perfect` and
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`.
Updated the existing node's proof, proof dependencies, origin, and obsolete tool approval.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.frobeniusStalkTrivializationNormalization`
(node `lem-trf-frobenius-stalk-trivialization-normalization`).

Actual holes left in the item: 0. Holes added: 0. Split-off statements: 0.
The imported stage-3 dependency declarations retain their existing holes; this delivery
adds none. The final module compiled without warnings via `lcompile.py` in 27.5 seconds.
A fresh two-file compile of the exact current module and unchanged
`Sheaf.Paper.LocalFrobeniusConjugacy` consumer passed (54.6 and 30.4 seconds).
The delivery's axiom probe passed compilation and server preflight passed
(dry-run commit `7be702a210`, review class CODEX).
The whole-definition `rfl` check is not a definitional equality: the naturality witness
was moved inside its own predicate. The old and new final clauses differ by the logical
equivalence `(∃ w, P w) ∧ D ↔ ∃ w, P w ∧ D`, where `D` is independent of `w`.
An explicit tuple reconstruction check was attempted but exceeded 60 seconds; the
formula expansions and this regrouping remain subject to independent definition review.

## No longer needed

Removed direct proof imports:
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`: the imported Frobenius theorem
  already supplies the coefficient-normalized unit equation.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`: already publicly imported
  by `FrobeniusTrivializationPullback`.
- `Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor`: already publicly imported
  by `ProEtalePullbackStalkCoherence`.

Removed direct proof dependencies:
- `lem-weil-pbc-conjugate-iso-unit-equation`: its result is already part of the supplied
  trivialization data; no mate construction is repeated here.
- `prop-weil-pbc-proetale-constant-ring-map`: the same supplied unit equation includes
  coefficient normalization. Removed its obsolete top-level `tool_uses` entry.
- `def-pc-fibre-product`: the needed pointed lift is constructed by composition with
  the given site isomorphism, using its projection equation and inverse identities.

These may remain transitive dependencies of imported declarations. No module is
withdrawn, and no blueprint unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy was found. A definition refactor was needed for kernel
performance; it does not change the mathematical normalization asserted. The original DAG described
constructing a mate and using a fibre-product universal property although the supplied
normalized data give a shorter direct calculation.

Kernel conversion was expensive when concrete composite point maps were repeated in
large expressions. Generalizing private calculations over arbitrary point maps and
exact functors, and isolating the unpacking of the Frobenius existence theorem,
and factoring the repeated formulas into predicates with arbitrary source points made
the complete theorem compile within the fixed limit. Earlier 53.5- and 54.8-second runs
had insufficient margin: later checks timed out, prompting the further refactor.

The resumed launcher reset the reference metadata during interrupted provider attempts;
the observed `.budget.start` values included 1792438080.3784573. No budget metadata or
launcher file was edited, and no delivery push had been started before this continuation.

## Second reading by W7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
