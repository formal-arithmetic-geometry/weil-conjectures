## What changed

Proved the original Boolean-component theorem by cases and the selected-open comparison `perfectOverlapTailProjectionAt`. Its proof combines the now-proved local normalization and cartesian projection calculation. The normalization uses the existing composition prism, naturality of the inclusion comparison, inverse cancellation, and the existing stage-object tail API. The projection calculation uses the existing abstract projection prism and naturality twice. New proved component APIs and scheme equations make the endpoints explicit. The original theorem signature and all existing definitions are unchanged.

## Proved and sorry left

Closed: `AlgebraicGeometry.perfectOverlapTailProjectionComponent` (the one original hole). Added holes: zero. No `sorry` remains in any delivered Lean file. Both retained obligations from the earlier attempt, `AlgebraicGeometry.perfectOverlapCompositeStageTailAt_eq_factors` and `AlgebraicGeometry.perfectOverlapTailProjectionFactors`, are proved in the resumed sandbox, rather than handed on. The selected-open theorem, the two-factor projection prism, the two scheme equations, and the two stage component APIs are also proved. Net relative to the original item: one hole closed, zero added. These proofs use the existing library dependencies; they do not claim to close holes already in those dependencies. No definition contains `sorry`. All nine delivered modules compile in import order. The resumed dry run passed compilation, axiom probes and static preflight, except for the second reading reserved for the independent reader; nothing was pushed.

## No longer needed

Removed direct parent proof imports: `DerivedPullbackComposition`, `PerfectOverlapNestedPullbackSquare`, `PerfectOverlapObjectRealizationCoreComparisons`, `PerfectOverlapStageEquivalence`, `PerfectHomComparisonTriangle`, and `PerfectOverlapObjectRealizationCoreTransport` (all under `Sheaf.AlgebraicGeometry`). Their relevant APIs remain available through the actual intermediate proof dependencies; no whole module is claimed pruned from the target closure. No planned geometric or unit-level step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The resumed sandbox already contained complete proofs of the normalization and projection applications. This session checked them against the current library and reran the three kinds of search, correcting the new-node search summaries to match the recorded results and repairing their blueprint provenance to inherit the parent’s blueprint ancestor. Blueprint searches for overlap tail projection, derived pullback, and restriction compatibility found no duplicate of these component equations. Both applications are coherence calculations from existing named APIs. Normalize the projections of `Over.mk` in the abstract two-factor lemma before specializing to dependent open-subscheme coefficients. The scheme equations and all isomorphism calculations cover empty and equal opens without additional assumptions. The final verification compiled every sandbox module in import order. Source text checked: Stacks `perfect.tex`, `lemma-quasi-coherence-pullback` (08DW), proof sentence on compatibility with open restriction; and `cohomology.tex`, `lemma-derived-pullback-composition` (0D5S), its K-flat computation of the canonical composition comparison.

## New nodes

`lem-pc-perfect-overlap-tail-restricted-composite`: proved restricted-map composition.

`lem-pc-perfect-overlap-tail-stage-projection`: proved scheme projection equation.

`lem-pc-perfect-overlap-tail-normal-form`: proved normalization using the nested-square inverse, naturality, and the composition prism.

`lem-pc-perfect-overlap-tail-projection-factors`: proved cartesian projection calculation after normalization.

`lem-pc-perfect-overlap-stage-object-factors`: proved expansion of the fixed stage-object comparison.

`lem-pc-perfect-overlap-stage-transport-component`: proved constructor component equation.

`lem-pc-perfect-overlap-projection-two-factors`: proved projection prism with two preceding coefficient maps.

`new-lem-pc-perfect-overlap-tail-projection-component-at`: proved selected-open comparison combining normalization and projection.

Change record: `coord/changes/perfect-overlap-tail-projection-linter.md` records the module-local linter setting for the original unused signature lets. It changes no exported interface or mathematical statement.

## Second reading by R1

1. **Interface and statements.** Compared the delivered item module with the repository version. The
original theorem signature and all existing declarations are byte-for-byte unchanged; only its proof,
proof-only imports, and a local linter option changed. Read every new node and its Lean declaration
against the parent component statement and the selected-open specialization. The Boolean branches use
exactly the U and V open hypotheses, and the intermediate statements retain all map, pullback, and
object hypotheses. The restricted-composition and projection equations were checked on empty opens and
on equal opens; they are ordinary scheme equalities and require no nonemptiness assumption. Verdict: pass.

2. **Proof soundness.** Compiled all nine delivered modules in dependency order with `lcompile.py --all`.
Searched the project and Mathlib for duplicate declarations and for the naturality, restriction, and
pullback projection APIs. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
`implemented_by` declarations in the delivered files. The proofs use the existing composition prism,
cartesian projection prism, naturality, inverse cancellation, and explicit stage-object and stage-
transport APIs. Verdict: pass; the final delivery axiom probes are left to `deliver3.py`.

3. **Split-off statements and nodes.** Checked that each split-off theorem is a strict intermediate
calculation used by a later theorem: restricted composition, raw scheme projection, tail normal form,
two-factor projection, stage-object factorization, stage-transport component, normalized projection
factors, and selected-open comparison. None restates the item theorem. The new nodes record their
source, proof steps, proof dependencies, blueprint ancestry, and recorded Mathlib searches. The
restricted-composition and raw-projection calculations were separated into modules so their public
imports match their signatures. Verdict: pass.

4. **Pruning and route.** The item now imports the selected-open comparison, which imports the two
normalization/projection calculations. Removed the former direct parent proof imports listed above;
proof-only imports remain nonpublic except where a public declaration needs their types. The unit route
through the composite stage tail, stage equivalence, nested pullback square, and fixed comparison
prism is preserved. The `import all` in the normalization module is retained because it supplies the
existing private derived-category helpers needed by the proof and cannot be replaced by the public
interface without losing an instance. Verdict: pass.

5. **Axioms and metadata.** Checked all declarations for standard proof dependencies and verified the
DAG `proof`, `proof_deps`, `proof_origin`, `lean`, chapter, and unit fields against the Lean proofs.
The report's hole accounting is unchanged: one original item hole closed and no holes added. The
linter change has a dedicated change record and does not alter an exported interface. Verdict: pass.

Changed during second reading: made the projection-prism support import proof-only while adding direct
public imports for its signature dependencies; split the two elementary geometric equations into
separate modules with matching node metadata; added the required second-reading record. No mathematical
statement or definition was changed.
