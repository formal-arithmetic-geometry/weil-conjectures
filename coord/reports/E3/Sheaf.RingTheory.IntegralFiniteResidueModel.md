## What changed

Proved `Algebra.exists_integral_finite_residue_model` with its signature unchanged.
The finite generating set consists of numerator and denominator lifts for finite spanning
families and pairwise prime separators. Integral incomparability proves injectivity on
the prime fibre, and injective lying over proves surjectivity. The canonical residue
embedding defines the intermediate field by `AlgHom.fieldRange`. Mathlib's finite-residue
instance and the field-range equivalence give finite-dimensionality; the spanning
families give containment, and `IsPurelyInseparable.tower_top` gives the final property.
Two private proved helpers handle fraction representatives and the scalar-module
identification for Mathlib's finite-residue instance. Added the proof-only import
`Mathlib.RingTheory.QuasiFinite.Basic`. Updated the node's step 6 to match that API.

Validation: a clean single-file compilation and an explicit `#print axioms` check
showing only `propext`, `Classical.choice`, and `Quot.sound` (15.5 seconds). The final
delivery preflight checks the exact delivered file again. A local heartbeat allowance
covers comparison of the explicitly specified scalar structures; the successful full
compile took about 20 seconds, within the unchanged 60-second limit.

## Proved and sorry left

Closed: `Algebra.exists_integral_finite_residue_model`
(blueprint: lem-dl-a1-integral-finite-residue-model), 1 of 1 original holes.
Added holes: none. Remaining holes in the delivery: zero. Split-off statements: zero.
Both private helper theorems are proved from Mathlib.

## No longer needed

Removed the proof-only import `Mathlib.RingTheory.Spectrum.Prime.Topology`:
`Ideal.exists_ideal_over_prime_of_isIntegral` already supplies lying over.
The node `lem-weil-pbc-finite-dimensional-domain-is-field` is no longer a direct
proof dependency: Mathlib's finite-residue-field instance replaces the explicit
finite-span/domain-field construction. Its Mathlib module remains a public import
required by the existing interface. No project modules are withdrawn; all other listed
dependencies remain used. The separability hypothesis is preserved but the proof only
needs the given finite-dimensional subfields and pure inseparability above them.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. Empty fibres are handled by empty index
sets throughout; no nontriviality or injectivity of A → D is assumed. Characteristic
zero and positive characteristic are both handled by the tower theorem. The residue
embedding compatibility is proved explicitly, so the conclusion concerns the exact
canonical image requested in the original statement. Mathlib's residue-module instance
is not definitionally equal to the statement's explicit algebra module; the proved
private helper identifies those structures rather than changing the statement.

Searches used LeanFinder, Loogle and grep through msearch.py, plus local rg over Mathlib,
Sheaf and WeilConjectures. LeanFinder located the finite-residue-field instance.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
