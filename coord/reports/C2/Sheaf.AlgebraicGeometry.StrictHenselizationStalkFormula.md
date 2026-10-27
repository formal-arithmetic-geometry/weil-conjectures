## What changed

Repair the dangling Lean attachment of
prop-weil-pbc-strict-henselization-stalk-formula. Its recorded declaration is
already fully proved in the adopted module
WeilConjectures.AlgebraicGeometry.StrictHenselizationStalkFormula, while the old
attachment points at an empty withdrawn SHEAF stub. Set existing = true and
record the adopted module, file and exact current signature.

Reconcile the explicit DIFFERENT retirement in coord/retire-items.tsv using
deleted.txt. The item is not an absent quarantined source: its empty module is
present in lean/, and coord/rework-done.tsv records its earlier reconciliation.
No archive, Lean declaration, source import or definition is changed. Only the
node's lean record changes; all its mathematical fields and dependencies remain.
Change record: coord/changes/C2-strict-henselization-stalk-formula-retirement.md.

Read the current blueprint statement and both proof paragraphs under
sec-curve-estimates/sk-thm-curveestimate, Stacks etale-cohomology.tex
Theorem theorem-higher-direct-images (03Q9), and all four existing proof
dependencies. The ordinary clause applies the unrestricted formula. The derived
clause combines the unique germ restriction, its invertibility, invertibility
of global homology of the mate, and the homology and Leray isomorphisms.
This is exactly the already proved adopted argument. Its hypotheses, both
conjuncts, integer degrees, and canonical-map equations are retained.

The old signature differs, ignoring whitespace, only by replacing
strictHenselizationScheme with strictLocalization and
strictHenselizationStructuralMap with strictLocalizationToBase. The models are
canonically isomorphic over the base, not definitionally equal. The existing
smallStrictHenselizationColimitIso and smallStrictHenselizationColimitIso_toBase
supply that comparison. Consumers already use the adopted theorem, with explicit
model transport where required; the separately retained small-model results stay.

The exact adopted source, with an appended #print axioms probe, compiled through
lcompile.py in 4.8 seconds. The theorem uses only propext, Classical.choice and
Quot.sound. The recorded signature was checked byte-for-byte against that source.
The optional unchanged-consumer check of
Sheaf.AlgebraicGeometry.Sites.FieldHigherDirectImageStalk hit the 60-second
file timeout. No changed dependency or source was supplied to it. This is a
pre-existing baseline compile limit, not a passing consumer check; the
attachment-only repair has no Lean elaboration effect. The unchanged consumer
Sheaf.Paper.AffineProfiniteFamilySerreCd compiled successfully in 11.9 seconds
through lcompile.py, including its existing use of the adopted formula.

## Proved and sorry left

Assigned live module: zero holes before and after this repair; proved 0 of 0.
Holes closed: none. Holes added: none. Split off: none. No sorry remains in the
item and no new Lean declaration or node is introduced.
AlgebraicGeometry.Etale.strictHenselizationStalkFormula already has a complete,
standard-axiom proof in the adopted module. This delivery claims attachment
repair and duplicate retirement, not new theorem-proof progress or decomposition.

## No longer needed

The duplicate Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula is already
an empty withdrawn module. Keep it withdrawn and replace its obsolete attachment
with the actual adopted declaration. No additional live module or import is
pruned: tools/downstream.py --uses and source searches found zero importers and
zero declaration users through the stub.

All 21 direct DAG parents, including parents without a live Lean attachment,
retain their mathematical dependency. The explicit retirement assignment, the
completed rework entry, and the existing adopted formula justify this repair;
zero live importers alone are not used to infer irrelevance. No statement,
proof dependency, proof step, tool-use approval, unit route or small-model
result is removed. Unit sk-prop-h2 has no realized attachment to this node and
its statement and all steps remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a holed item. The current assignment is
instead a listed retirement with zero holes; the live source is a withdrawn
stub and the residual defect is its dangling DAG attachment. Restoring the old
same-named theorem would collide with the adopted declaration. Copying the
stub without fixing the attachment would be a no-op.

The old Lean signature uses a distinct model of the strict henselization.
Direct definitional conversion between these models is not claimed. Existing
consumers already supply transport and the separately retained small-model
results are preserved. No target, mathematical statement or dependency changes.

Required searches were run through msearch.py: Lean Finder returned structure
sheaf and module stalk results, Loogle returned no match for the theorem name,
and grep returned no Mathlib match. The exact result is in the adopted library.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
