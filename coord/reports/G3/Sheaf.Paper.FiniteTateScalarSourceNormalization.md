## What changed

The original theorem statement and all specified finite Tate scalar maps and predicates are
preserved. Their definitions are verbatim in the new, publicly reexported
`Sheaf.Paper.FiniteTateScalarSourceData`, so the separate construction lemma can state its
result without an import cycle. The item proves the flat-single computation and uniqueness
of a generator-normalized balancing family, then combines them with the separate existence
and compatibility assertion in `Sheaf.Paper.FiniteTateScalarSourceExistence`.

The adapted dependencies `EtaleDerivedScalarTensor` and `VectorPurityScalarSingle`
share the representative formula. Current main independently changed
`FiniteSmoothCoefficientArrows.scalarSingleMap` to the same alias and added the proved
`scalarSingleMap_cochain` theorem. That module is now taken unchanged from main. The generic theorem
`CategoryTheory.purityAdjunctionSingleMap_eq_representative` is proved; it identifies the
original adjunction transpose with the original cochain formula. The scalar/single alias
uses that same arrow. No adopted source-library module is changed.

Reviewer fix (2026-10-26, third application of the accepted fix of the C-f9841 and C-95241
reviews): `EtaleDerivedScalarTensor` only gains the abbrev `scalarAdjunctionRepresentativeMap`.
The body of `scalarExtensionRepresentative` keeps its published formula: the delivered rewrite
breaks `Sheaf.Paper.ExceptionalCoefficientMaps` and `Sheaf.SixFunctors.EtaleHomComparisonModels`,
which `unfold scalarExtensionRepresentative; rw [← mapComplex_unit_formula]`. The item proves the
agreement of the specialized abbrev with it locally (`hrep` in `single_map_iso`). T7's
`scalarRepresentativeUnit` and private `scalarExtensionRepresentative_unit` are not carried: the
T7 landing 68e7567cd43 was taken out of `sheaf-dag` by 73427fd8534. The item's `proof_deps` add
`def-pur-finite-tate-scalar-source-data`, `lem-pur-etale-scalar-pullback-uniqueness`
(`scalarRepresentative_isIso`) and `lem-asd-etale-finite-twist-pullback-rest` (`lineHomEquiv`),
whose private lemmas the proof uses through `import all`. `def-pur-vector-purity-scalar-single`
cites `lem-pur-etale-scalar-pullback-uniqueness` for `mapComplex_unit_formula`.

Change records: `coord/changes/G3-scalar-representative-sharing.md`,
`coord/changes/G3-purity-representative-single-constructor.md`,
`coord/changes/G3-finite-tate-source-data-module.md`.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.PurityFiniteSetting.finite_tate_scalar_source_normalization` by a
reduction, not a complete proof from the old dependencies. The flat-single computation and
uniqueness argument are proved. The latter uses the scalar adjunction, the rank-one root
universal property, and induction with the specified tensor-power recursion.

Added one hole:
`WeilConjectures.PurityFiniteSetting.finite_tate_scalar_source_normalization_exists`,
node `lem-pur-finite-tate-scalar-source-existence`. It asserts existence and compatibility,
without uniqueness or the comparison for arbitrary flat sheaves. This is a decomposition:
one upper hole closed, one lower hole added, net zero holes closed. No definition contains
`sorry`, and no data is selected from this existence theorem.

The adapted `EtaleDerivedScalarTensor` retains its single pre-existing hole
`AlgebraicGeometry.Etale.scalarTensorIso_existsUnique`, node
`lem-pur-derived-change-of-rings`. The parent module and the other adapted dependencies have zero holes; the new
existence theorem has the one added hole named above.
The existence statement includes empty schemes, zero rings, N=1 and r=0; no nonzero or
coefficient-flatness hypothesis has been inserted.

## No longer needed

No whole dependency module is claimed pruned: the construction lemma still needs the
ordinary balancing and coherence argument of the original plan. The parent proof no longer
constructs K-flat resolutions of arbitrary unbounded complexes; it uses the separate
construction assertion for source compatibility. Removed proof imports from the parent:
`Sheaf.Paper.PurEtaleScalarMateProjection` and
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
The former remains needed for the construction lemma's planned proof. Original public
imports are retained. The new data-only module also drops its inherited private
proof imports of `KFlatIndependentCoefficients`, `CochainTensorUniverses`,
`PurEtaleScalarMateProjection` and `KFlatResolutionIndependentCoefficients`; none
is used by its definitions. Exploratory comparison and boundary constructors are not delivered.

## Where the brief, the DAG or earlier work was wrong

Repair of return C-f9841 (head `f9841bc0cb4`): the independent reader accepted the
mathematics, but landing rejected a reviewer override named
`G3-scalar-representative-sharing.md`. The change record is present in this packet at
`coord/changes/G3-scalar-representative-sharing.md`. In the landing tool's flat
`--apply-fixes` directory its accepted override name is
`G3-scalar-representative-sharing.change.md` (see `tools/batch_land.py`, `fixes`).
The same `.change.md` convention applies to the other two retained change records. The
repository paths keep their original `.md` names. This packet records the filename
mismatch explicitly so a new review can land without repeating it.

Rechecked the retained Lean declarations against current `sheaf-dag`; the two adapted
dependencies retain their original interfaces and the item retains its original
statement. The delivery tool creates the new packet on the current branch. The final preflight exposed an independent landing in `FiniteSmoothCoefficientArrows`
that occurred during this session. Removed that stale adapted module and its obsolete
change record from this packet, retaining main's new `scalarSingleMap_cochain` theorem,
private helper, imports, options and original `scalarZeroLineIso` verbatim. This is a
packet omission, not a module withdrawal. The subsequent delivery supersedes
`95241d81236`, whose snapshot must not land. This repair adds no Lean holes. (Reviewer
correction: the concurrent T7 additions `scalarRepresentativeUnit` and
`scalarExtensionRepresentative_unit` were withdrawn from `sheaf-dag` by 73427fd8534 and are not
part of this delivery.)
The first server check of all six delivered Lean files ran through `lcompile.py --all` on the project
server with `LCOMPILE_NO_LOCAL=1`; the command returned exit code 0. A subsequent
dry run rejected the data module at 65 seconds. Profiling found type checking and
linting dominated its cost. Removed four unused private proof imports from that
new data module and made its already-defined scalar/source maps locally irreducible
while elaborating the remaining predicates. These local attributes preserve the
exported transparency, definitions and signatures; no public attribute changed.

No false statement was found. The generic scalar/single equality required an explicit
adjunction calculation rather than relying on definitional equality of the representative
and adjunction formulas. The complete construction/coherence draft did not finish compilation;
it is not claimed as proved. The retained existence lemma records that unfinished,
mathematically separate construction. The target's flat-single and uniqueness conclusions
are independent real arguments, rather than a renaming of the target.

## New nodes

`def-pur-finite-tate-scalar-source-data` attaches the unchanged specified maps and predicates
to their independent API module. It adds no hole and changes no mathematical definition.

`lem-pur-finite-tate-scalar-source-existence` records the balancing-family construction and
its five compatibility predicates. Its module and docstring include the source and a
complete natural-language argument; the proof remains one named hole.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
