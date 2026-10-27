## What changed

Preserved the exact statement of
`WeilConjectures.RawHeartAdic.raw_heart_adic_lisse_stratification` and replaced its sorry
with an explicit assembly. Obtain normalized lisse, completed-system, coherent coefficient
and continuous families from their existing theorems. Use the normalized heart-model theorem
directly to select one finite heart representative and its continuous constructible sheaf.
Construct `Strata` with that exact stage and representative, the finite reduced partition,
and the classical restriction models supplied by the finite-strata transport lemma. Add
the frontier and rational Weil clauses from the supplied-partition extension lemma.

Extracted the 37 existing data declarations into RawHeartAdicLisseData and publicly
reexported them from the original module to avoid an import cycle with the new proof lemmas.
Their signatures, fields and bodies are unchanged (checked against the original text).
The new obligations encode the translations between the four planned dependencies' different
classical-system interfaces, including small E versus ULift E, and the normalized projection
of the frontier base change. None asserts the original simultaneous theorem.

Validation: remote single-file compilation of all five delivered modules in import order;
normalized theorem-signature comparison and byte-for-byte comparison of the moved data bodies. The delivery tool additionally checks declaration axioms and the three named remaining holes.

## Proved and sorry left

Closed the original textual hole in
`WeilConjectures.RawHeartAdic.raw_heart_adic_lisse_stratification` (1 of 1 in the original
module), by decomposition into three strictly smaller obligations. This is a decomposition,
not a complete proof or positive net hole reduction: 1 hole closed, 3 holes added, net -2.
The assembly itself has no sorry.

Every remaining sorry in this delivery is the whole proof of one public theorem:

- `WeilConjectures.RawHeartAdic.raw_heart_adic_comparison_bridge`
  (lem-zl-raw-heart-adic-comparison-bridge): compatible global comparison functors,
  no heart object or partition.
- `WeilConjectures.RawHeartAdic.raw_heart_adic_strata_bridge`
  (lem-zl-raw-heart-adic-strata-bridge): finite classical systems on a reduced partition
  for an already supplied finite-stage heart object and its constructible continuous
  realization; no finite-stage descent, common representative, Weil map or frontier.
- `WeilConjectures.RawHeartAdic.raw_heart_adic_restriction_bridge`
  (lem-zl-raw-heart-adic-restriction-bridge): Weil and frontier extension for a supplied
  classical partition; no comparison-family or initial-strata existence.

RawHeartAdicLisseData contains zero holes and no new arbitrary-witness construction.
Each remaining theorem has a source and a complete natural-language proof in its docstring.
The three bridge statements remain proof obligations for subsequent stage-3 workers.

## No longer needed

No mathematical node or library module is withdrawn or claimed globally pruned. The four
original proof dependencies remain needed: the normalized heart-model theorem is applied
directly; the lattice and classical-system results supply the new transport obligations;
the Weil/frontier result supplies the final obligation. The unit's reduction-to-a-lisse-stratum
step and the original theorem remain in place. Zero Lean importers does not justify withdrawal.

The following old private proof imports are removed from the data/assembly file; they are
parts of the downstream theory of the original plan rather than declarations used by the
new assembly:

- `Sheaf.Paper.DerivedPullbackTensorHom`
- `Sheaf.Paper.PbcQbarCompletedPullback`
- `Sheaf.Paper.ContinuousCoefficientModuleEncoding`
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Sheaf.Paper.TopologicalStratifiedLisseLattices`
- `Sheaf.Paper.IntegralPullbackComparisonRealization`
- `Sheaf.Paper.ContinuousModuleEncodingSliceFreeness`
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`
- `Sheaf.Paper.LocalizedTStructure`
- `Sheaf.Paper.IntegralTStructure`

All original public statement imports are retained in RawHeartAdicLisseData and reexported.
No top-level tool_uses approval is pruned, since the underlying arguments remain needed.

## Where the brief, the DAG or earlier work was wrong

The four stated dependencies cover the mathematics but do not directly have the structures
of this item's conclusion. ClassicalRawLisse uses a scalar-localized finite-free small
coefficient system; the item uses the free full subcategory of a lifted LisseRationalSheaf.
The Weil/frontier interface uses a large algebraic coefficient closure and a different
partition/realization package. The frontier theorem also does not expose this item's
geometric_projection field, although the canonical projection is used in its descent proof.
The new lemmas isolate these missing encoding translations rather than assuming them by
notation. No false statement, changed target or departure from the unit route was found.

Edge cases considered: empty X and empty partitions; zero local rank; nonreduced X; m=1;
a nonintegral scalar Weil automorphism of a rank-one sheaf (only a rational lift is needed).
No positivity, nonempty-stratum, invariant-lattice or Frobenius-stable-partition assumption
is added. `iota` remains the original binder, although this existence argument does not use it.

## New nodes

`def-zl-raw-heart-adic-lisse-data`: unchanged interface extraction, with all moved declarations
attached; no existence assertion and no sorry.

`lem-zl-raw-heart-adic-comparison-bridge`: uniform coefficient-size and normalized realization
transport, independent of a particular heart object, retaining sf/PBC halves and fibres.

`lem-zl-raw-heart-adic-strata-bridge`: fixed-stage reduced classical partition from a supplied
finite heart model and its continuous constructible realization.

`lem-zl-raw-heart-adic-restriction-bridge`: rational Weil and finite-field frontier extension
for a supplied partition, preserving the actual iterated Weil map and model projections.

Change record: coord/changes/C8-raw-heart-adic-lisse-data-extraction.md.

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
