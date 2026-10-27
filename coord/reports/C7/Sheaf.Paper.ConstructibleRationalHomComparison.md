## What changed

`Sheaf.Paper.ConstructibleRationalHomComparison` now assembles its complete original
statement from the existing completed-continuous Hom hypotheses and one new normalized
coefficient-transport obligation. It proves the coproduct-Hom assertion, converts it to
sequential Hom continuity by reindexing `ULift ℕ`, supplies integral boundedness, restricts
the general comparison to integral objects, and proves full faithfulness of the specified
`R.J`. The latter proof converts degree-zero localized shifted Homs to tensor Homs,
conjugates by `R.objects`, and checks equality with `R.J.map` on every fraction using
`R.fractions` and the normalized inverse-uniformizer formula. The generic private
zero-shift/tensor comparison follows the already proved argument in
`Sheaf.CategoryTheory.BoundedHomLocalizationEmbedding`.

The new module `Sheaf.Paper.RationalRealizationHomTransport` isolates comparison of
standard exact sheaf localization with the prescribed universal derived tensor and
normalized rational constant action. It applies to all Hom-continuous source objects
and bounded-below targets; it asserts neither constructible continuity nor raw-functor
full faithfulness. Its proof plan cites the existing scalar-localization theorem,
normalized ring-isomorphism transport and uniqueness of exact derived functors.

`AlgebraicGeometry.Scheme.rationalRealizationLocalizedLinear` is moved verbatim into
that module and publicly reexported at its original import path. The full name,
attribute, signature and body are identical. The comparison predicate and item theorem
statements are unchanged. The move avoids a cycle between the new transport theorem
and the predicate using its scalar action. Every downstream consumer is listed in
`coord/changes/C7-rational-localized-linear-relocation.md`; no consumer adaptation or
change of target meaning is required.

## Proved and sorry left

Closed the original textual hole in
`AlgebraicGeometry.Scheme.constructibleRationalHomComparison`
(node `lem-per-constructible-rational-hom-comparison`): its assembly proof is complete.
The item had one hole and now has zero. Both sandbox modules compiled together via
`lcompile.py --all`. The delivery compile also checks the final warning-free version
of the private reindexing helper.

Added one hole:
`AlgebraicGeometry.Scheme.rationalRealizationHomTransport`
(node `lem-per-rational-realization-hom-transport`). This is the coefficient-presentation
and universal-derived-functor transport portion of the original proof, with the general
Hom-continuity and lower-bound predicates. It has a full sourced proof plan in its
docstring and node. This delivery is a decomposition (one hole closed, one added),
not a net hole reduction. All newly added private helpers are proved. No data is chosen
from an arbitrary unproved existence theorem; the moved scalar structure is unchanged.

The existing theorems `rationalModuleRealizationFunctor` and
`completedContinuousHomHypotheses` are used as assigned stage-3 dependencies and remain
untouched. In particular, no proof of their obligations is claimed here.

## No longer needed

Removed the item's proof imports of:

- `Sheaf.Paper.IntegralConstructibleHomSums`;
- `Sheaf.Paper.IntegralConstructibleBoundedBelowCompactness`;
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`.

The first and third are now used through the assigned
`Sheaf.Paper.CompletedContinuousHomHypotheses` interface; the second is below Hom sums.
Their nodes `lem-weil-pbc-integral-constructible-hom-sums`,
`lem-weil-pbc-integral-constructible-bounded-below-compactness` and
`lem-weil-pbc-integral-stratified-perfect-characterization` are not direct obligations of
the item's assembly. They remain needed transitively; no global withdrawal is requested.
The obsolete direct tool approvals for Hom sums, characterization and scalar-derived-Hom
are removed from the item node; the actual dependencies are recorded in its new proof.

`Sheaf.CategoryTheory.BoundedHomLocalizationEmbedding` is not imported: its terminal
raw-functor existential would still require identifying its functor with the specified
`R.J`. The proof uses the scalar-localization Hom comparison through the new transport
obligation and carries out this identification directly. Its node
`lem-per-bounded-hom-localization-embedding` is no longer a direct dependency of the
item; its generic degree-zero tensor argument is proved privately here. No unit statement
or unit proof step is bypassed. The item does not realize a unit's own statement or step.

The original public rational-realization import is now reexported by the new public
transport import. No public API is removed. No module is withdrawn and no source-library
declaration is changed.

## Where the brief, the DAG or earlier work was wrong

The DAG correctly gives two conceptual assembly steps, but the Lean embedding theorem
is formulated for the exact termwise functor into the standard sheaf-localization ring.
The item instead fixes the universal K-flat derived tensor into the continuous rational
coefficient sheaf, with a normalized constant field action. These are naturally
isomorphic, rather than definitionally equal, and no existing declaration supplies this
coefficient and derived-functor transport. The new node isolates exactly that missing
glue. It does not restate the constructible theorem or assume its full-faithfulness
conclusion. The existing first-conjunct Hom sums use index types in `Type (u + 1)`,
whereas the generic continuity predicate uses `ℕ`; the explicit `ULift` reindexing
resolves this universe difference without changing either interface.

## New nodes

`lem-per-rational-realization-hom-transport`, stated by
`AlgebraicGeometry.Scheme.rationalRealizationHomTransport` in
`Sheaf.Paper.RationalRealizationHomTransport`, is the normalized coefficient and
universal-derived-tensor transport of the general bounded-below localization theorem.
Its source is Bhatt--Scholze, Lemma 6.8.12 and Proposition 6.8.14(2), pp. 61--62,
together with the existing normalized ring-isomorphism and exact-derived-functor nodes.
LeanFinder, LeanSearch, Mathlib grep, local source search and blueprint duplicate search
found the underlying localization and transport tools but no existing declaration of
this combined normalized comparison. Zero and torsion objects and the empty scheme
are included; no flatness of cohomology or global-denominator hypothesis is introduced.
The change record is `coord/changes/C7-rational-localized-linear-relocation.md`.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
