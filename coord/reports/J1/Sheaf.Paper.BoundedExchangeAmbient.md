## What changed

Restored `Sheaf.Paper.BoundedExchangeAmbient` from its quarantine archive, as required by
the current `coord/rework.tsv` row. The live module was absent following a merge-queue
cluster restore. Restored both constructed definitions (`residueExchangeSquare`,
`residueExchangeBaseChange`) and both public theorems with their original signatures,
definitions and complete proofs. Wrapped the archived lines exceeding 100 characters
and removed the redundant private `import all` of MorphismDefs. All public imports stay
unchanged, including IntegralResidueComparisons, preserving the archived public interface
for its quarantined consumers.

The change record is `coord/changes/J1-bounded-exchange-ambient-restoration.md`.
The restored module compiles cleanly through lcompile.py (17.5 seconds). The direct
archived consumer IntegralResidueExchangeAlgebra also compiles cleanly against the
restoration (8.1 seconds); its temporary source copy is excluded from the delivery.
No source-library module, target, node statement or unit route is changed.

## Proved and sorry left

This is a zero-hole rework restoration: 0 holes closed, 0 holes added, 0 holes split off,
and 0 textual holes remain in the delivered module.

The restored complete proofs are
`AlgebraicGeometry.ProEtale.CondensedRing.residueExchangeBaseChange_counit`
(lem-weil-pbc-residue-exchange-counit) and
`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleBaseChange_hom_eq_ambient`
(lem-weil-pbc-bounded-exchange-ambient), together with their proved private component
helpers. The two ambient definitions are actual constructions, not chosen witnesses.
The existing bounded restriction and ambient mate are identified by injectivity of the
adjunction hom-equivalence, using the matching counit and pull-square components.

## No longer needed

Removed the redundant private `import all` of
WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs;
the public import supplies its existing adjunct theorem without private definition access.
No nodes or modules are pruned: the preserved ambient construction, the counit identity,
the transported-composition lemma and the bounded adjunct API all remain needed.
IntegralResidueComparisons remains publicly imported to preserve the original reexports.

LeanFinder and Loogle searches through msearch.py found the Mathlib restricted-counit
identity and mate counit identity used by the existing proof. Local searches found no
different specialized bounded-to-ambient comparison. The existing three-step node proof
already implements the short formal adjunction argument; it requires no new nodes.

## Where the brief, the DAG or earlier work was wrong

The item is a quarantined restoration with no archived sorry, rather than a new four-times
split mathematical obligation. Its rework row explicitly preserves all three node
attachments; absence from lean/ does not justify withdrawal. The archive compiles against
the current library, and its only compiler findings were long-line style warnings, fixed
in this delivery. No mathematical error or statement dispute was found. The DAG proof,
attachments and dependencies already agree with the restored code and are retained.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
