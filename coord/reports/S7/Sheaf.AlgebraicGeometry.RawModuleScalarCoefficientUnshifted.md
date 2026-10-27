## What changed

Completed the retirement repair listed in coord/retire-items.tsv for
Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientUnshifted. The item currently
contains zero sorries; both mathematical theorem nodes already attach to their
proved canonical upstream declarations. Withdraw the redundant compatibility module
via deleted.txt, while preserving its historical derivedPullbackIso abbreviation
verbatim in the existing RawModuleScalarDerivedPullbackIso definition module.

Adapt the only two remaining direct importers, RawModuleScalarCoefficientSquare
and RawModuleScalarSourceClassFormula, to import that definition module and the
canonical upstream theorem API. The former's upstream twin already publicly imports
the canonical unshifted module. The latter adds its public import explicitly, so
both importers continue to expose exactly the previous names. No adopted upstream
file or existing theorem signature, proof, instance or definition body changes.
The moved abbreviation keeps its complete old signature and explicit inverse
structure, including the reducible inv projection needed by
RawModuleAbelianHomSourceFormula.

The existing definition node def-sbc-raw-scalar-derived-pullback-iso gains the moved
abbreviation in its lean.declarations. No new node, statement, mathematical proof
route, dependency, unit realization or target statement is introduced or changed.
The unshifted theorem still follows the existing generic source-square and sheaf
composition proofs; its upstream proof is reused in full.

Change record:
coord/changes/S7-retire-raw-module-scalar-coefficient-unshifted.md.


Validation: all three changed modules compiled without warnings through lcompile.py
(21.3, 7.6 and 6.0 seconds). Exact import scans over both live Lean roots and
quarantine/ find no remaining import of the retired path in the proposed sources.
The moved declaration's signature and full body are byte-identical to the original.
The node diff changes only its lean field. tools/downstream.py identifies six
transitive consumers of the retired wrapper, including exactly two direct importers;
whole-name search identifies the source-formula theorem as the only external user
of the historical abbreviation. All are listed in the change record.

The scratch compatibility proof compiled in 10.5 seconds: rfl proves
derivedPullbackIso = derivedPullbackIsoImpl and identifies its inv with the canonical
comparison's hom; the upstream shift theorem applies directly to the moved alias.
#print axioms for the alias, its formula theorem and both canonical unshifted
theorems lists only propext, Classical.choice and Quot.sound.

The unchanged active direct importers of the receiving definition module compiled:
ComparisonForgetScalars, OrdinaryFiniteP1Kummer, RawModuleAbelianHomMap,
RawModuleFreeSourceAcyclic, RawModuleFreeSourceHomBijective,
RawModuleScalarClassMorphisms, RawModuleScalarSourceFactors and
CartierRelativeBoundaryRealization. Temporary verification copies are removed from
the delivery; another group's concurrent FreeSource changes are not overwritten.

Optional wider checks hit the 60-second limit in the unchanged
RawModuleScalarHomEvaluation, RawModuleAbelianHomSourceFormula and
RawModuleAbelianHomTargetFormula. The evaluation consumer also times out against
the untouched published baseline, establishing a pre-existing compile-cost issue.
The source-formula consumer also times out against the untouched baseline.
The untouched target-formula baseline compiled in 58.3 seconds, close to the
same limit; its isolated overlay check subsequently passed (0.3 seconds as
reported by lcompile.py). These unrelated
theorem proofs are not adapted in this retirement packet.

Searches ran through msearch.py: LeanFinder returned generic natural-isomorphism
inverse facts; Loogle found CategoryTheory.Iso.symm_hom; grep confirmed Iso.symm's
explicit inverse construction. Direct library search located the exact already-proved
upstream coefficient and shift statements. No new mathematical lemma is needed.

## Proved and sorry left

Retirement repair with zero original holes. Holes closed: none. Holes added: none.
Holes left in the item or adapted modules: none. Split off: none.
AlgebraicGeometry.Etale.rawModuleScalar_coefficient_unshifted and
AlgebraicGeometry.Etale.rawModuleScalar_derivedPullbackIso_commShift were already
proved in WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientUnshifted;
those complete proofs are retained and are not counted as new hole closures.
The historical derivedPullbackIso abbreviation is preserved with the same data.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientUnshifted.
Its two former imports, Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso
and WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientUnshifted, remain
needed and are available to the two migrated consumers. Both consumers remove
their public import of the retired Sheaf path.

No mathematical node or dependency is pruned. In particular retain
lem-sbc-raw-scalar-coefficient-unshifted,
lem-sbc-raw-scalar-derived-pullback-shift,
def-sbc-raw-scalar-derived-pullback-iso,
lem-sbc-raw-scalar-source-square-core and
lem-sbc-raw-scalar-sheaf-composition, with their existing parent dependencies.
The coefficient-square, shift-transport and source-class parent nodes still use
the same declarations and comparison. The already withdrawn concrete source-square
module is not restored or deleted. No unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The generic dispatched brief describes a deep open proof chain, but the current
queue and retirement list assign a retirement repair, and the present item has
zero holes. The old retirement row lists three consumers; currently only the
coefficient-square and source-class wrappers still import the item. The listed
concrete source-square module is already withdrawn. The reported missing
historical derivedPullbackIso is real; it must be retained because the unchanged
RawModuleAbelianHomSourceFormula statement uses it. Moving that abbreviation
verbatim to its existing definition module resolves the retirement without
changing the comparison or weakening any theorem. This preserves the explicit
inverse-structure correction mandated by the earlier P2 independent review.

The two theorem-node Lean attachments are already canonical and require no change.
Only the definition-node Lean attachment needs its declaration list extended to
record the relocated historical name. All mathematical dependencies and the
current blueprint unit route are preserved.

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
