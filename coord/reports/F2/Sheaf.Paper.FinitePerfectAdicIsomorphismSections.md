## What changed

Replaced the single hole in `AlgebraicGeometry.Scheme.finitePerfectAdic_isomorphism_sections`
by a proof from two strictly earlier interfaces. The statement and its original four public
imports are unchanged. Added private proof imports of the new presentation module and the
existing finite-ring derived local constancy theorem.

The item now constructs the canonical sheafifications `I n`, sheafifies the specified etale
presheaf maps to obtain `r n`, and proves their finite local constancy directly from
`AlgebraicGeometry.Etale.finiteRing_derived_local_constancy`. It evaluates source-site Isom
sections, transports their raw normalization square, inverts the resulting isomorphisms,
and proves the exact requested orientation by cancelling the two isomorphisms. In
particular the final square includes every further `W → finitePerfectAdicChartObject V U`
and the actual strict-tower maps.

`FinitePerfectAdicIsomorphismPresentation` records the finite-coefficient etale complexes,
their bounded/lisse cohomology, inhabited canonical Isom stalks, the normalization arrows,
and a reduction map on actual etale Isom presheaves with its equation on generators.
Its scalar-forgetting realization functors, coefficient interchange and level comparisons
have two explicit normalization identities. The definition `transport` applies these
functors to raw derived isomorphisms. The proved lemma
`FinitePerfectAdicIsomorphismPresentation.transport_square` derives forward square
preservation from the two identities and naturality. No square-preservation assumption
is stored in the presentation, and it supplies no evaluation of sheafification sections.

`sourceIsomorphism_normalized_presheaf_evaluation` is a preservation theorem for a fixed
presheaf map satisfying a generator equation. It constructs no presheaf map or universal
normalization, and has no finite, perfect, bounded, lisse or nonempty-stalk assumptions.
It is not the existing existential normalized Isom-section reduction theorem under a new
name. These two obligations separate etale descent/normalization from preservation by
pro-etale evaluation. Neither is the assigned theorem with its hypotheses repackaged.

The coefficient ring lift and quotient homomorphism and the canonical etale normalization
arrow are explicit definitions, with no holes or arbitrary chosen data. The existence
witness for the presentation is eliminated only inside the proof of the item theorem;
no definition selects data from its unproved existence theorem.

Validation: `lcompile.py --all` compiled all three modules cleanly in import order,
with per-file times 1.2 s, 30.9 s and 12.7 s. The assigned theorem's signature was
compared with the source and is unchanged. Every new dependency ID resolves, and no new
node has a dependency path back to the assigned theorem.

## Proved and sorry left

Closed the one original hole:

- `AlgebraicGeometry.Scheme.finitePerfectAdic_isomorphism_sections`
  (`lem-weil-pbc-finite-perfect-adic-isomorphism-sections`).

Added two named theorem holes, each the entire proof of its public theorem in a separate
new module:

- `AlgebraicGeometry.Scheme.finitePerfectAdic_isomorphism_presentation`
  (`lem-weil-pbc-finite-perfect-adic-isomorphism-presentation`), in
  `Sheaf.Paper.FinitePerfectAdicIsomorphismPresentation`.
- `AlgebraicGeometry.Scheme.sourceIsomorphism_normalized_presheaf_evaluation`
  (`lem-weil-pbc-source-isomorphism-normalized-presheaf-evaluation`), in
  `Sheaf.Paper.SourceIsomorphismNormalizedPresheafEvaluation`.

This is a decomposition: one original hole closed, two lower holes added, two holes left
in the delivery, net minus one before any unrelated changes to the import closure.
The item's proof, the new transport-square theorem and every new definition contain zero
holes. The finite-lisse predicate is proved using an existing theorem, not included as an assumption on the presentation.
Both new theorem docstrings state their source and complete intended proof.

## No longer needed

No original public import was removed, and no module or declaration was withdrawn.
No whole module is claimed pruned.

The item's direct proof no longer calls
`lem-weil-pbc-normalized-derived-isomorphism-section-reduction`
(`Sheaf.Paper.NormalizedDerivedIsomorphismSectionReduction`): it sheafifies the presentation's
specified presheaf maps and uses the fixed-map evaluation preservation lemma instead.
The archived reduction module and its dependencies are preserved unchanged; this is not a
withdrawal of quarantined mathematics or a claim that its other consumers no longer need it.

The item's former descent, coefficient and restriction dependencies now belong below the
new presentation obligation rather than being direct applications in the item:
`lem-weil-pbc-finite-ring-constructible-derived-origin`, `thm-weil-pbc-site-comparison`,
`lem-weil-pbc-completed-constant-sheaf-reduction`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, and
`def-weil-pbc-ringed-derived-restriction`. These are retained in its new node's proof route;
they are not globally pruned. The existing derived local Isom definitions remain used.
The finite-ring derived local constancy node remains a direct dependency of the item.

## Where the brief, the DAG or earlier work was wrong

The original Isom-section construction is not a one-line application of the normalized
section-reduction theorem: one must first supply compatible descended etale levels and
identify their normalization arrows with those of the actual strict completed tower.
The presentation obligation states that bridge explicitly at the raw presheaf level.

The current source for `NormalizedDerivedIsomorphismSectionReduction` is quarantined
(the `coord/rework.tsv` entry preserves its archive), as are its transport and scalar
extension proof dependencies. I read the archived theorem and transport signatures;
the archives are not treated as withdrawn and no restored or existing module is changed.
The new presentation node retains the declared scalar-extension and normalization theory
it needs. The new preservation lemma addresses the distinct fixed-presheaf-map interface.

The unit and chapter route are unchanged. Empty charts, zero coefficients and zero
complexes impose no additional nonemptiness assumptions: stalk requirements are vacuous
on an empty chart, the lifted quotient map is defined for the zero ring, and the final
cancellation argument applies to all isomorphisms, including those between zero objects.

## New nodes

`def-weil-pbc-etale-isomorphism-normalization-arrow` records
`etaleIsomorphismNormalizationArrow` in
`Sheaf.Paper.SourceIsomorphismNormalizedPresheafEvaluation`. This is the actual derived
etale inverse image followed by the canonical coefficient mate (Stacks 03DA and 03ED),
with all coefficient-universe sizes explicit.

`lem-weil-pbc-source-isomorphism-normalized-presheaf-evaluation` records preservation of a
specified generator normalization equation by canonical source-site evaluation (Stacks
09BV, 0F63 and coefficient-mate pasting). It has one theorem hole and no hidden definition.

`def-weil-pbc-finite-perfect-adic-isomorphism-presentation` records the explicit lifted
finite coefficient ring, its quotient homomorphism, the etale derived category, and the
presentation structure in `Sheaf.Paper.FinitePerfectAdicIsomorphismPresentation`. This is
raw etale diagram and scalar-transport data, before pro-etale section evaluation.

`lem-weil-pbc-finite-perfect-adic-isomorphism-presentation` records existence of that
presentation from the supplied algebraic tower and separate local markings, following
finite quotient descent and normalization in Stacks 09C6, 09BV and 06YY. It has one theorem
hole. All four nodes record LeanSearch, LeanFinder/Loogle, and source grep searches;
only generic sheafification/condensed-local-constancy results were found. There are no
changes to another existing module or to another module's node, and no change record is
required for a shared interface.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
