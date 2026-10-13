## What changed

Proved `AlgebraicGeometry.Scheme.root_split_away_localization_point` with its original
signature, visibility and public imports unchanged. Three new, fully proved modules give
its localization chart, the etaleness of the punctured cover, and a point of that cover
above y. All their imports into the original module are proof-only imports.

The ring is explicitly `Localization.Away (algebraMap R A g)`. The etaleness proof uses
the standard etale pair `(X^n-C(g), C(g))` and the checked Bezout identity
`f'*(C(n^-1)*X)+f*(-1)=C(g)`. The point proof uses the already proved source theorem
`AdjoinRoot.faithfullyFlat_of_monic`, then Mathlib surjectivity on prime spectra. The
final proof transports the point through the chart inverse and uses composition of
etale morphisms. No statement or definition in the existing library was changed.

All four modules compile cleanly with lcompile.py. Edge cases are covered: n=1 uses
the same identity, n=0 is excluded by the existing hypothesis, and a zero ring or g=0
makes the supplied point off g impossible. The chart itself permits all n and empty
basic opens; the etaleness theorem also permits the empty basic open. The point lemma
requires positivity but does not require n to be invertible.

## Proved and sorry left

Closed the sole original hole, `AlgebraicGeometry.Scheme.root_split_away_localization_point`
(node `lem-sbc-root-split-away-localization-point`). Added zero holes. All new declarations
are proved: `root_split_away_localization_chart`, `root_split_away_cover_etale`, and
`root_split_away_cover_point`. No delivered declaration contains sorry. This is a proof,
not a decomposition into postponed statements.

## No longer needed

No original imports, nodes or modules are removed. The new chart and point modules
import Mathlib.AlgebraicGeometry.Restrict in place of the broader Etale module; only
the new etaleness module requires Etale. The original node had no proof
imports or named proof dependencies to prune. Both original public imports are needed
for its statement. No module for transporting a prescribed root splitting is imported:
that work belongs to the caller and is not needed here. The unit and chapter route
remain unchanged.

## Where the brief, the DAG or earlier work was wrong

No error in the original statement. The original single proof paragraph lacked named
components. The completed DAG now records the three components actually used, all of
which have complete Lean proofs. The etaleness calculation directly constructs a
standard etale pair over R, avoiding a separate comparison after localization of R.

Searched LeanFinder, Loogle, project sources and Mathlib with the dispatcher search
script. LeanSearch returned Internal Server Error; its unavailability is recorded
without an absence claim. The successful searches found the standard etale pair and
localization machinery and the faithfully-flat spectrum theorem; no complete scheme
statement was found. Read Tag 0EYG online: its off-divisor paragraph motivates this
specialization; the explicit auxiliary ring calculation is written here, rather than
claimed to occur verbatim in that paragraph. No missing literature obligation remains.

## New nodes

`lem-sbc-root-split-away-localization-chart` records the actual affine localization,
its chart isomorphism over R, and invertibility of g, without positivity assumptions.
Its module is `Sheaf.AlgebraicGeometry.Morphisms.RootSplitAwayLocalizationChart`.

`lem-sbc-root-split-away-cover-etale` records the etaleness of V to Spec R for positive
invertible n. Its module is `Sheaf.AlgebraicGeometry.Morphisms.RootSplitAwayCoverEtale`.

`lem-sbc-root-split-away-cover-point` records lifting y to V for positive n, without
an invertibility assumption. Its module is `Sheaf.AlgebraicGeometry.Morphisms.RootSplitAwayCoverPoint`.

All three nodes inherit the original chapter and unit, carry exact Lean signatures,
complete proof steps and recorded searches, and introduce no remaining proof obligation.
No change record is required because no existing interface changed.

## Second reading by V4

1. **Interfaces unchanged.** I diffed the delivered localization-point module against the repository version. The target theorem signature, visibility, and existing public imports are byte-for-byte unchanged; only proof-only imports and the proof body changed. The three auxiliary module interfaces match their DAG node statements.

2. **Proof and axioms.** I compiled all four delivered modules with `lcompile.py --all`; they compile without warnings. The axiom probe reports only `propext`, `Classical.choice`, and `Quot.sound` for every declaration. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations, and no definition contains postponed data.

3. **New statements.** I checked the chart, etaleness, and point statements against their proofs and tested the edge cases described by the worker (positive degree, degree one, and arbitrary rings for the chart). They are strict components of the target argument and are not restatements of the target. Searches of the project and Mathlib found no existing declaration with these statements. The source tag 0EYG was checked; it motivates the tame off-divisor argument, while the explicit affine calculation here is the Lean realization.

4. **Pruning and route.** The target proof uses exactly the three auxiliary declarations it imports. The chart uses `basicOpenIsoSpecAway`; the cover proof uses the standard etale pair and its localization equivalence; the point proof uses faithful flatness of a positive-degree monic AdjoinRoot and prime-spectrum surjectivity. No old proof dependency or import is unused, and the unit route is represented by the existing chart, etale, and point steps.

5. **DAG agreement.** I checked the four node records and their exact Lean signatures. The target node proof and `proof_deps` list the three auxiliary nodes used by the proof; each auxiliary node records its construction, source, searches, module, and declaration. The unit record remains unchanged, with no route bypass introduced.

I changed only this second-reading report section; no Lean statement or definition required repair.
