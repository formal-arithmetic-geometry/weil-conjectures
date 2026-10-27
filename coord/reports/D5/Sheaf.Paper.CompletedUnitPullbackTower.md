## What changed

Implemented `WeilConjectures.CompletedUnitPullback.completedUnitPullbackTower`
without changing its statement. The proof constructs Core over the literal coefficient
field and its canonical small model, then constructs Result. Mathlib's regular-module
pullback isomorphism proves the finite and whole-system maps invertible. Exact derived
localization proves systemMap invertible. The normalized primitive-counit realization,
the strict reduction comparison, and inverse augmentation construct the integral unit.
Its formula is definitional; counit naturality and the adjunction triangle prove the
whole-system coherent_reduction equality. The rational and common-stage isomorphisms
are functorial images of that integral isomorphism with the prescribed source transports.

`completedUnitAdmissible` proves the uniform Tor interval [0,0] from the finite flat-model
criterion and existing constant-coefficient constructibility.
`completedUnitMultiplicationComponents` proves the normalized adjunction-mate equation
by equality on sections, including all equality transports. `completedUnitReduction`
constructs the section-preserving finite identifications directly, then obtains the
specified augmentation from existing completeness and normalized reconstruction.

The existing data declarations were moved byte for byte into
`Sheaf.Paper.CompletedUnitPullbackData`, publicly re-exported from the original module.
This permits the independent source lemmas to import the data without a cycle.
No definition body, target statement, or existing public signature changes.
Change record: `coord/changes/completed-unit-proof-interface.md`.

## Proved and sorry left

Original hole closed: `WeilConjectures.CompletedUnitPullback.completedUnitPullbackTower`.
The original module has one hole; its delivered proof has zero. This is a decomposition,
not a claim that the parent is axiom-free: the independent source compatibility results
listed below remain. The new admissibility, reduction, and finite-component lemmas have no holes.

Holes added: two, one in each separate public theorem module:

- `WeilConjectures.CompletedUnitPullback.completedUnitStrictComparison`
  (`lem-pur-completed-unit-strict-comparison`): assembling the actual regular tensor
  chain maps into a whole-system comparison with its specified finite equations.
- `WeilConjectures.CompletedUnitPullback.completedUnitScalarNaturality`
  (`lem-pur-completed-unit-scalar-naturality`): compatibility of the actual reconstructed
  unit with normalized scalar transport and rationalization.

Each is a strictly separate part of the source argument, with no conclusion asserting
Result, Core, or the parent theorem. Each has its source and full argument in its docstring
and node. The parent proof combines these with real adjunction and localization calculations.
No hole occurs in a definition or private declaration. The original tower module compiled
with zero holes before the final delivery checks. The final finite-component proof
also compiled with zero holes. The unchanged direct consumers
`AdicUnitTraceReductionData` and `PointTraceReconstruction` both compiled against
the extracted public interface. Empty schemes, exponent one,
identity scheme maps, and ramified coefficient fields use the same constructions.

## No longer needed

No original public import is withdrawn: the original module keeps all seven verbatim
and also re-exports the data module. The private proof imports in the parent are exactly the lemmas it uses.
No module is withdrawn or claimed globally pruned.

The parent no longer directly reproves the surjective-tower/Roos completeness argument:
`lem-weil-constant-coefficient-objects-constructible` supplies the completed regular
object's completeness and actual finite reductions, and normalized reconstruction supplies
its actual adjunction-unit isomorphism. Thus the parent no longer directly needs
`lem-sp-ell-coefficient-fiber`, `lem-weil-proetale-surjective-tower-derived-limit`,
`lem-weil-strict-roos-comparison`, `def-weil-derived-complete`,
`def-weil-finite-torsion-constructibility`, `def-weil-derived-complete-integral-detailed`,
or `def-weil-finite-tor-amplitude` as proof steps. They remain prerequisites in the
existing theorems or in the meaning of Admissible where applicable.

`lem-weil-constant-scalar-strict-unit` is used below the strict-comparison lemma rather
than repeated in the parent. The ordinary pullback-unit theorem replaces the parent's
explicit tensor inverse and quotient-square isomorphism construction, so
`prop-weil-pbc-proetale-constant-ring-map`, `prop-weil-pbc-proetale-constant-exact`,
and `def-pur-integral-derived-operations` are no longer separate parent proof steps;
the specified functors and their exactness are still the original ones. No source-library
declaration, proof or dependency is removed. The blueprint unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The broad proof plan is mathematically appropriate. The constant-coefficient theorem
already proves constructibility, completeness, finite reduction invertibility and their
cohomological bounds; repeating its surjective-tower proof is unnecessary. Tor amplitude
is a separate remaining calculation and is proved here with the finite flat-model criterion.
The whole-system coherence equation must use the actual augmentation equality. It follows
by counit naturality and the triangle identity; equality is never inferred merely from
finite derived evaluations. The existing public interface was monolithic, requiring its
unchanged data block to be extracted before independent proof lemmas could import it.

## New nodes

`lem-pur-completed-unit-admissible` records the proved zero Tor bound and all existing
constructibility clauses. `lem-pur-completed-unit-reduction` records the proved construction
of the finite identifications and normalized augmentation from the strict comparison.
`lem-pur-completed-unit-strict-comparison` is the regular-system part of source step 1;
it asks for a whole-system isomorphism, not a family of derived objects.
`lem-pur-completed-unit-multiplication-components` is the finite adjunction-mate portion
of source step 4. `lem-pur-completed-unit-scalar-naturality` is precisely the coefficient
transport portion of source step 6. The three proved constructions and the two separate
remaining lemmas are linked from the updated parent proof. Definition ownership is updated
in `def-pur-completed-unit-pullback-data`; the parent theorem's attachment retains its theorem.
The change record is `coord/changes/completed-unit-proof-interface.md`.

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
