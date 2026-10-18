## What changed

Proved `AlgebraicGeometry.ProEtale.point_proEtale_sections_exact` in
`Sheaf.Paper.PointProEtaleSectionsExact`, with its original signature and definition
of `pointModuleSections` unchanged. The field has a singleton spectrum, separably
closed residue field, and strictly henselian maximal localizations. Apply the existing
geometric retraction criterion, full-small-site set-sheaf evaluation theorem, and
arbitrary-ring-sheaf exact evaluation theorem. Forgetting abelian groups to sets gives
the abelian clause directly through local surjectivity. Mathlib supplies preservation
of quasi-isomorphisms, shifts, triangles, and the localization comparison; reuse the
proved source-library `mapDerivedCategoryHomologyFunctorIso` for the cohomology comparison.
All added imports are proof-only. Updated the theorem's proof docstring and the node's
proof route to record the direct abelian argument.

Validation: the complete proof compiled through `lcompile.py` in under seven seconds.
`#print axioms AlgebraicGeometry.ProEtale.point_proEtale_sections_exact` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
The import-direction check accepts the additional source-library import. The unit
`sk-def-sf-admissible` has no realized statement or proof steps to bypass.
The argument applies unchanged to nonconstant and zero coefficient ring sheaves;
all integer cohomology degrees and both arbitrary derived-category universes remain.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.point_proEtale_sections_exact`
(node `lem-weil-point-proetale-sections-exact`). Proved 1 of 1 sorries.
No remaining `sorry` in the item, no holes added, and no split-offs.
The axiom check also confirms that its actual proof dependencies have no remaining holes.

## No longer needed

Removed the redundant proof import
`Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`; the required homology API
is already available through the derived-category imports. Removed the planned proof
step's use of `def-weil-pbc-constant-sheaf` and `def-weil-pbc-sheafification`: the abelian
clause uses local surjectivity and forgets to sets, so it needs no integer-action
construction. These are pruned direct proof dependencies, not a claim that their
modules disappear from the entire target closure. No existing statement module is
withdrawn. All three substantive geometric/evaluation dependencies are used.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. Step 5's integer-action argument was unnecessary: the
two existing general-site Mathlib leaves
`lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective` and
`lem-weil-pbc-site-sheaf-sets-epi-locally-surjective` give a shorter direct argument.
Their use is recorded in the node; no new nodes or definitions are needed.
The existing source-library derived homology comparison completes step 7 directly.
No definition, public import, consumer, or statement was changed, and no change record
or forced adaptation is required.

## Second reading by J9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
