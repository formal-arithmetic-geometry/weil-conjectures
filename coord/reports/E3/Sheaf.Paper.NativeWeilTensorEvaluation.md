## What changed

Filled `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_evaluation` in
`Sheaf.Paper.NativeWeilTensorEvaluation`. Its statement and sole public import
are unchanged. The completed proof was first checked in one file; all declarations
elaborated without proof errors, but the file exceeded the 60-second limit. Categorical inference
was improved by explicit mapped morphisms and abstract diagram-pasting lemmas.
The remaining work is now organized into three fully proved new modules:

- `Sheaf.Paper.NativeHomEvaluationSquareAllSources` proves
  `native_hom_evaluation_square_all_sources`, extending the projection-normalized
  Hom comparison to an arbitrary source and a K-injective target. The comparison
  is constructed explicitly using proved product-Hom comparison helpers from
  `Sheaf.WeilSheaf.NativeHomPrecompositionQuasiIso`.
- `Sheaf.Paper.NativeWeilChainUncurryForget` proves
  `native_weil_chain_uncurry_forget`, the degreewise tensor-summand identity.
- `Sheaf.Paper.NativeWeilRepresentativeUncurry` proves
  `native_weil_representative_uncurry`. It compares the two normalized chain
  uncurrying maps on tensor summands, then pastes the localized model squares.

The item uses representative uncurrying, the proved generic
`NativeCurrying.hom_isKInjective` from
`Sheaf.Paper.NativeOrdinaryRepresentativeCurrying`, K-injective fullness of
localization from
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExact`,
and private categorical transport lemmas to prove evaluation for every pair of
derived objects. Every new import in the item is proof-only.

Updated the DAG to this argument. Validation: `lcompile.py --all` accepted all four modules in import order.
Three unused forall-binder names in the chain lemma were then prefixed with
underscores; the delivery compiler rechecks this warning-only cleanup. There are no changes to other existing modules or definitions.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_evaluation`
(`lem-sf-native-weil-tensor-evaluation`), one original hole.
No holes remain in the item. No holes or split-off statements are added.
The three public intermediate lemmas named above and every private helper are
proved in full. They introduce no holes; this is a proof, not a decomposition
into remaining obligations.

## No longer needed

No original import was removed; the original sole public import remains.
The planned dependency `lem-weil-pbc-ringed-slice-evaluation-coherence`
(`Sheaf.Algebra.Homology.RingedSliceEvaluationCoherence`) is not imported: its
private categorical transport argument is proved here using just the supplied
comparisons. Its slice-comparison structure additionally requires symmetry data
which this theorem does not assume. This prunes that dependency from this item's
proof; it makes no claim that the module is globally unused.

The theorem `quasiIso_bifunctorHomMapLeft` itself is unnecessary: source
replacement is handled by naturality of the already supplied representative
isomorphisms and cancellation of a derived source isomorphism. Its module and DAG
node remain dependencies of the new Hom-square lemma because that proof uses the
already proved explicit canonical product-Hom comparison and its naturality equation.

## Where the brief, the DAG or earlier work was wrong

The supplied proof plan refers to a private `evaluation_of_iso` specialized to a
comparison-data structure carrying symmetry data. That structure cannot be formed
from the hypotheses of this item. The transport argument itself needs no symmetry,
so it is proved locally without that extra interface. The planned separate
quasi-isomorphism theorem for precomposition on Hom complexes is also unnecessary
for extending the supplied square. No mathematical statement or definition is
changed. The quarantine copy was read and its declaration and attachment preserved.

## New nodes

`lem-sf-native-hom-evaluation-square-all-sources`:
`AlgebraicGeometry.ProEtaleWeilSheaf.native_hom_evaluation_square_all_sources`
in `Sheaf.Paper.NativeHomEvaluationSquareAllSources`, fully proved. It removes
only the source K-injectivity restriction from the supplied comparison square;
it asserts no tensor or evaluation compatibility. The proof constructs the
comparison by projections before transporting the square along source replacement.
It also applies to zero complexes and zero objects, since product projections
and invertible localization maps suffice throughout.

`lem-sf-native-weil-representative-uncurry`:
`AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_representative_uncurry` in
`Sheaf.Paper.NativeWeilRepresentativeUncurry`, fully proved. It compares inverse
transposition of chain-representable arrows on K-flat/K-injective representatives.
The argument works componentwise, including a zero tensor source or target and
the empty scheme. It is strictly the representative step; the item's proof still
must lift a derived internal-Hom representative to a chain map, cancel its tensor
isomorphism, and transport evaluation to arbitrary derived objects.

`lem-sf-native-weil-chain-uncurry-forget`:
`AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_chain_uncurry_forget` in
`Sheaf.Paper.NativeWeilChainUncurryForget`, fully proved. It proves the equality
of the native and ordinary normalized chain maps by the tensor-summand universal
property. It imposes no flatness or injectivity condition, because the two
component normalization equations and the underived uncurrying comparison suffice.
The zero-complex cases follow from the same universal property. It is extracted
from the completed representative proof after profiling and diagram-inference
improvements, to keep every file below the compile-time limit.

No change records are needed: only the item and new modules/nodes are changed.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
