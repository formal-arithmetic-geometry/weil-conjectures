## What changed

Proved `AlgebraicGeometry.AlgebraicSpace.chartwise_etale_permanence` in
`Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence`, preserving its entire signature,
public imports, and definitions. Added private proof imports of
`AlgebraicSpaceRepresentableEtaleSchemeTests`, `SpaceEtaleSourceAtlasDetection`, and
`PresheafFieldLiftFamilyCalculus`.

The scheme-test theorem supplies composition, isomorphisms, Yoneda tests, and the
comparison of schemes etale over one algebraic space. The source-atlas theorem supplies
atlas existence and descent. Two proved private helpers transport any representable
scheme-test property through a pullback square and expose the underlying presheaf
pullback of the sheaf fibre product. Pasting these squares proves chartwise base change.
For cancellation, the surjectivity test for a target atlas gives a scheme cover of each
source chart; Yoneda fullness supplies the comparison scheme map, and scheme-source
descent finishes. Identity and chartwise composition are direct quantifier arguments.
The field-lift theorem supplies singleton isomorphisms and composite families; for
pullbacks, naturality and the type-level pullback universal property lift the compatible
pair directly. This works for all the displayed universes and empty index families.

Updated the existing node's proof and proof origin to describe the explicit pullback
transport and direct field-section argument. No statement, definition, target, consumer,
or source-library file changed. The unit's route is preserved.

Validation: `lcompile.py` compiled the complete file cleanly in 8.5 seconds. The public
theorem signature was compared verbatim with the shared source. All Lean lines have at
most 100 characters. Import-direction checks permit each of the three proof imports.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.AlgebraicSpace.chartwise_etale_permanence`
(node `lem-trf-space-chartwise-etale-permanence`).

Item holes: 1 before, 0 after. Added holes: 0. Split-off statements: 0.
Both private helper theorems are proved. There are no retained `sorry` declarations in
the delivery. The proof uses the already stated scheme-test, atlas-detection, and
field-lift theorems; their existing holes remain work in their own modules.

## No longer needed

Removed the direct proof import `Sheaf.AlgebraicGeometry.EtaleDescentThroughSourceCover`:
the assigned theorem now applies the recorded source-atlas detection interface instead.
This is not a claim that the source-cover theorem or its module is globally obsolete;
it remains an input of source-atlas detection.

No DAG dependency nodes or modules are withdrawn. All five current proof dependencies
remain relevant, including the algebraic-space and fibre-product definitions. Within the
scheme-test interface only composition, isomorphisms, Yoneda etale tests, and scheme
comparison are used. Generic pullback pasting proves the particular base-change
transport without invoking its separate base-change conjuncts. Within field-lift
calculus the singleton and composition clauses are used; the compatible-pair pullback
clause is implemented directly for the actual sheaf pullback, avoiding an additional
transport from the explicit combined cone. No public import was removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement defect found. The module's retained docstring describes the
older ten-step presentation, while the current node organizes the same argument in four
steps through the three already stated interfaces. The delivery follows those current
interfaces and records its concrete pullback constructions in the node.

The shortest-route searches used launcher `msearch.py` with LeanFinder (chartwise etale
algebraic spaces, base change, cancellation), Loogle (`"IsEtale", "comp"`), and grep
(`chartwise|IsChartwiseEtale`), as well as repository searches. Results concerned scheme
etaleness or rings, not this algebraic-space theorem. The existing DAG declarations give
the needed route; no new mathematical result or interface repair was necessary.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
