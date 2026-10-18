## What changed

Proved `AlgebraicGeometry.Etale.isZero_higherDirectImage_iff_geometric_cohomology_colimits`
in `Sheaf.AlgebraicGeometry.EtaleHigherDirectImageStalkCriterion`, preserving its signature.
The proof obtains the higher-direct-image/sheafification isomorphism from
`nonempty_higherDirectImage_iso_sheafification_abelian_single`, applies
`Point.presheafToSheafCompSheafFiberIso`, and uses
`Scheme.sheafHom_ext_of_sheafFiber_map_algClosurePoint` to show that the identity of a
sheaf with zero geometric stalks is zero. This is the joint-faithfulness form of the
planned conservativity argument. The node's third proof step and proof origin now record it.

Replaced the public strict-henselization import with public imports of
`Mathlib.AlgebraicGeometry.Sites.EtalePoint` (the point used in the statement) and
`WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients` (the abelian
coefficient instances needed by its derived-category expression). All three proof-only
imports remain used. No definitions or theorem statements change, and no modules are adapted.
Change record: `coord/changes/M1-etale-higher-direct-image-stalk-imports.md`.

Validation: remote single-file compilation succeeds without warnings (4.1 seconds).
The unchanged sole direct importer,
`Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension` (held by C3),
also compiles against the revised item (4.6 seconds); no adaptation is needed. Read the current
blueprint statement and proof at `main-20261015`, Stacks `lemma-higher-direct-images`
(Tag 03Q8), and `lemma-stalk-exact` (Tag 03PT). The argument also covers q = 0, the zero
sheaf, and an empty base scheme: joint faithfulness makes the empty-family case valid.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Etale.isZero_higherDirectImage_iff_geometric_cohomology_colimits`
(node `lem-kun-cd-stalk-criterion`). Zero holes remain in the item, and zero are added.
No split-offs. The proof uses the existing declared higher-direct-image/sheafification
comparison, without adding any assumptions or new proof obligations.

## No longer needed

Removed the import `Sheaf.AlgebraicGeometry.StrictHenselization`; neither the statement
nor this proof constructs or uses a strict henselization. Its two actual interface
requirements are now imported directly as described above. This does not claim that the
module is unused by other library modules. No declared proof dependencies are pruned:
all four existing proof-dependency nodes retain their roles (the stalk definition is
realized directly by Mathlib's point fiber). No new nodes or alternative unit route.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect was found. The original public strict-henselization import supplied
unrelated declarations indirectly. The existing proof-dependency interfaces fit the goal.
The qcqs and torsion hypotheses are unnecessary for this formal sheaf/stalk comparison,
but all are retained verbatim. The final step uses joint faithfulness on id and zero,
instead of reflecting an isomorphism from the zero sheaf; both implement the same
geometric-stalk conservativity step. The original unit record has no realized statement
or proof steps that this argument would bypass.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
