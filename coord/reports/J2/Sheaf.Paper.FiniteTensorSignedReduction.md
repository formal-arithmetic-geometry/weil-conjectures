## What changed

The assigned `Sheaf.Paper.FiniteTensorSignedReduction` now proves
`WeilConjectures.PurityFiniteSetting.existsUnique_finiteTensorCore` from a specified
constructed model and its representative equation. `finiteScalarMonoidalModel` is
actual data: the native proved left-derived monoidal functor transported along the
canonical comparison between its scalar adjunction and the chosen fixed scalar
adjunction. No unproved mere-existence assertion supplies data.

The main item contains the complete uniqueness proof. On K-flat pairs the source
of the normalization square is invertible: its factors are the localization
tensorator, scalar representative at the tensor complex, and ordinary scalar
cochain comparison. The candidate equation then makes the common tail invertible.
Cancel that tail in two normalized equations to identify inverse tensorators.
K-flat density and naturality extend equality to every pair of derived objects.
The unit laws, whisker exchange and unitor naturality identify unit maps;
structure extensionality identifies the monoidal structures.

The actual square is constructed in `FiniteScalarTensorData`, with intermediate
objects, three source factors, their invertibility certificates and the tail as
fields of `TensorRepresentativeData`. Its generic methods form the common target,
source composite and complete normalization predicate before specializing cochain
instances. `FiniteTensorCoreNormalized` applies that entire predicate to the same
actual diagram. The single-input scalar representative and its certificate are
stored before evaluation at the tensor complex. Three proved native property APIs
supply the factor certificates; `finiteScalarTensorData_source_isIso` combines
them generically. Certificates provide no object or map data. The unclaimed parent
`FiniteTensorReductionData` gives the unchanged native cochain comparison its
explicit morphism type and marks it irreducible; its property proof unfolds it.

A clean compile originally took 68 seconds. A declaration-level profile found
25 seconds converting the scalar-core result to its finite-level specialization.
Forming the normalization predicate in the generic diagram API removes that
repeated concrete conversion. This is an actual definition/API repair. The whole
cancellation, density and unit argument remains in the assigned item.

The signed-line specialization separately took 41--68 seconds in kernel checking.
Its normalization now has the same kind of actual-data interface:
`finiteTensorLineComparisonData` is constructed in the parent from the identical
`finiteTensorAdjunction` and entire original single-functor/restriction composite.
`TransposedFamilyData.Pointwise` is exactly the original heterogeneous equality;
its `Normalized` predicate conjoins those equations over all exponents. The
pointwise existence witness, proved unique-comparison theorem and main family
assembly share this datum. The generic pointwise uniqueness proof uses the same
adjunction injectivity and `Iso.ext` argument as before. The whole family assembly
stays in the main file. `finiteTensorFixedLineMap` retains its original signature
and body. Both pointwise consumer modules were unclaimed when adapted.

All eleven public signature texts and original docstrings of the assigned module
remain verbatim. The twist/shift argument is preserved. The two pointwise consumer
signatures change only the computational representation of their complete equation,
as documented below. All original public imports are retained; statements and data
add their necessary public data imports. No adopted source-library file is edited.

The newly landed, unclaimed `FiniteTensorSymmetryCoherence` is adapted to the
normalization interface using the completed native braided scalar constructor,
transport and normalized-core uniqueness. Its public signature and docstring
remain verbatim. Ordinary concurrent checking replaces the main and symmetry
files' former `Elab.async false` setting.

Change records: `coord/changes/J2-finite-scalar-monoidal-model.md`,
`coord/changes/J2-tensor-representative-data.md`,
`coord/changes/J2-cochain-comparison-interface.md`,
`coord/changes/J2-line-comparison-data.md` and
`coord/changes/J2-scalar-symmetry-interface.md`.

The complete fourteen-file compile passed the per-file acceptance checks. The final
main profile reported 347 ms of cumulative kernel checking after the actual-data
repairs. Profiling options were then removed, and the clean main-file compile
passed without warnings.

## Proved and sorry left

Original assigned holes: 1. Removed the original hole in
`WeilConjectures.PurityFiniteSetting.existsUnique_finiteTensorCore`
(node `def-pur-finite-signed-reduction-comparisons`). The assigned module has zero
direct remaining holes. Its full uniqueness and family-assembly arguments are
proved; construction of the monoidal model is actual data.

Added holes: 1,
`WeilConjectures.PurityFiniteSetting.finiteScalarMonoidalModel_representative`
(node `lem-pur-finite-scalar-monoidal-representative`). It is the full cochain
counit equation for the particular independently constructed model, for every
pair of complexes. It has no existence or uniqueness conclusion.

Existing consumer hole retained: 1,
`WeilConjectures.PurityFiniteSetting.exists_finiteTensorLineDerivedComparison`
(node `lem-pur-finite-tensor-line-derived-existence-witness`). Its named hole and
mathematical statement are retained; only the representation of its complete
pointwise equation uses the actual shared data. It is not counted as newly proved
or newly added. The existing unique-comparison theorem stays proved.

Thus the assigned hole is decomposed into one new, strictly partial equation
obligation, with net hole closure zero. The changed packet has two direct holes:
the new representative equation and the retained existing pointwise witness.
The closure ledger additionally accounts for existing proof-dependency imports.
All new definitions and other new APIs have zero holes. Symmetry adds no hole.

## No longer needed

The main item retains all four original declared proof dependencies and original
public imports. All added proof imports are used. Ordinary signed-family reduction
and the pointwise derived comparison remain the inputs to the family assembly.
No adopted source declaration or module is removed.

The symmetry consumer no longer needs its separate K-flat resolution/cochain
braiding argument. Its proof dependencies `lem-sfb-abstract-kflat-resolution`,
`lem-sfb-exact-right-adjoint-kflat-representative` and
`lem-pur-external-rhom-derived-braiding` are replaced by the existing native braided
scalar constructor and transport, followed by normalized-core uniqueness. Removed
private imports are `Sheaf.CategoryTheory.ExactRightDerivedAdjointKFlatRepresentative`
and `Sheaf.Paper.ExternalRHomDerivedBraiding`. The first is still used by the main
item's representative API; the second is still used by
`Sheaf.Paper.ExternalRHomConePairingDefs`. No global module is withdrawn.

Removed unused private symmetry helpers: `qBraided`, `q_mu_iso`,
`representative_braiding`, `derivedRepresentativeBraiding`, `cochainMapBraiding`,
`cochainComparisonIso`, `mappedUnit`, `cochainRepresentative`,
`cochainRepresentative_app`, `cochainRepresentative_iso`,
`adjointRepresentativeBraiding` and `scalarSymmetry`.

## Where the brief, the DAG or earlier work was wrong

The planned descent step did not name the already proved native derived-monoidal
constructor. It constructs the candidate directly. Uniqueness needs source
invertibility and the candidate equation, without a separate assertion that both
scalar-extended inputs are K-flat. Mathlib supplies transport, hom equivalence and
extensionality ingredients, but not the exact fixed-adjoint counit equation.

No statement was found false and no unit route is bypassed. No target signature
changes. Both repaired normalization predicates retain their entire original
formulas, maps and hypotheses through actual constructed data. Their target-meaning
reviews are reopened, as recorded in the definition change records. Identity
coefficient maps, equal levels, zero rings and the empty scheme use the same
constructions. No coefficient-morphism flatness or boundedness is added.

The expensive kernel conversions required definition/API repairs; moving a proof
body to another module or raising the file limit would not fix them. The complete
core uniqueness and signed-family assembly remain in the assigned file.

## Forced adaptations

`Sheaf.Paper.FiniteTensorSymmetryCoherence` landed from Y7 during this session and
was unclaimed. Its original file failed against the repaired dependencies at
original line 339 (`exact hn`): the sealed native cochain comparison no longer
unfolded during concrete specialization. It also failed at original line 358:
the chosen normalization was the typed diagram equation rather than the old
unfolded generic square. Opening the old square locally took 68 seconds; moving
conversion to its old scalar helper took 88 seconds.

The final proof uses the already completed
`ProEtale.leftDerivedSheafExtendScalarsBraided`. Its two new private helpers
(final lines 35--66) transport braidedness along the very same left-adjoint
comparison defining the model. The public proof (lines 81--89) uses the candidate
equation and uniqueness to identify this model with the chosen core, then
substitutes the equality in the transported symmetry square. Twelve old private
helpers and two unused private imports are removed. Public signature, public
imports and docstring remain verbatim; no source constructor or proof changes.

The two unclaimed signed-line consumers are adapted together with their parent
normalization to share its complete pointwise predicate. This is an interface
repair of unclaimed modules, not an edit to a module held by another group.
`FiniteTensorLineDerivedExistenceWitness` retains the same existence assertion and
named hole, with its full equation represented by `Pointwise`.
`FiniteTensorLineDerivedExistence` retains the same uniqueness assertion and uses
the proved generic pointwise-uniqueness API for its former injectivity argument.
Their old and new signatures and exact unfolding are recorded in
`coord/changes/J2-line-comparison-data.md`. No mathematical conclusion changes.

## New nodes

`def-pur-finite-scalar-monoidal-model` records the actual native monoidal model
transported along canonical left-adjoint uniqueness, in
`Sheaf.Paper.FiniteScalarMonoidalModel`. Its data and coherences are constructed.

`lem-pur-finite-scalar-monoidal-representative` records the remaining full counit
square for that specified model, in `Sheaf.Paper.FiniteScalarMonoidalRepresentative`.
Its proof in words describes the native homotopy counit square, quotient comparison,
exact-restriction unit identity and cancellation of the left-adjoint comparison.

`def-pur-tensor-representative-data` records the actual source factorization,
tail, common target and full normalization predicate in
`Sheaf.Paper.TensorRepresentativeData`. The common-target alias is reducible so
source and tail have the same target under rewriting's implicit transparency.

`def-pur-finite-scalar-tensor-data` records the directly constructed scalar diagram
with the original maps, in `Sheaf.Paper.FiniteScalarTensorData`.

`lem-pur-finite-scalar-tensor-source` records the fully proved composite source
invertibility API in `Sheaf.Paper.FiniteScalarTensorSource`.

`lem-pur-finite-scalar-representative-invertible` exposes the proved K-flat scalar
representative certificate in `Sheaf.Paper.FiniteScalarRepresentativeIso`.

`lem-pur-cochain-localization-tensor-invertible` exposes the native tensorator
property in `Sheaf.Paper.CochainLocalizationTensorIso`. Its explicitly typed actual
map `cochainLocalizationTensor` seals the same native lax tensorator before
concrete comparison; its property is proved by a private generic argument.

`lem-pur-finite-scalar-cochain-comparison-invertible` exposes the proved native
cochain scalar component certificate in `Sheaf.Paper.FiniteScalarCochainComparisonIso`.
These property APIs have no hole and supply only proof fields to the actual data.

`def-pur-transposed-family-data` records the actual adjunction/prescribed-value
interface, its entire pointwise and family equations and fully proved pointwise
uniqueness, in `Sheaf.Paper.TransposedFamilyData`. The actual finite datum is
constructed in the existing parent module, recorded by the existing node
`def-pur-finite-tensor-reduction-data`. It introduces no proof hole or arbitrary
witness. The two existing pointwise nodes retain their mathematical statements;
their Lean records and proof routes describe the same equation through this datum.

`def-pur-native-derived-scalar-braiding` attaches the existing completed source
constructor `AlgebraicGeometry.ProEtale.leftDerivedSheafExtendScalarsBraided` in
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.Trace`.
It introduces no Lean file, declaration, data or hole; the source file is unchanged.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
