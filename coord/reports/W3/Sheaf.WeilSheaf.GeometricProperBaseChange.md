## What changed

The existing geometric proper-base-change theorem is now proved by explicit affine-chart
reduction on the geometric fiber. The proof constructs a refined affine open cover, supplies
the chart structure morphisms over the algebraic closure, transports boundedness and native
constructibility to each source chart, and descends the local isomorphisms with the existing
native derived cover-conservativity theorem. Its original signature is preserved verbatim.
Neither absolute separatedness nor a condition on g nor a Frobenius structure is added.

`NativeAffineProperBaseChange` contains a complete Lean proof of the affine case from the
existing native module constructibility comparison, adic predicate comparison, rational
proper base-change theorem, and the new map-comparison lemma. In particular the encoded
bounded-constructible input is proved, not assumed. Properness supplies the separated,
quasi-compact, locally finite-type structure morphisms of both source schemes.

`NativeDerivedBaseChange` contains the two unchanged native derived exchange constructions,
extracted from the item to avoid a cycle. The item publicly reexports the foundation. Both
existing definition bodies and signatures are preserved. `NativeBaseChangeOpenChart` and
`NativeDerivedExchangeComparison` isolate two genuinely structural compatibilities of maps.
The latter also exposes the exact scalar-transport encoding used by the existing native
constructibility comparison, with proved additivity and equivalence instances.
The named encoding keeps coefficient transport folded when checking the derived argument.
Its coefficient isomorphisms are one chosen family with the finite-extension chart
normalization and naturality already proved in `locallyFiniteCoefficientRing_realization`.
The exchange argument keeps the bundled coefficient Λ and schemes over k abstract, with
an equality identifying the coefficient with the standard ring, until its native conclusion.
The actual encoding `nativeExchangeEncodingAt` is equality transport of the real functor;
its equivalence and additivity are proved. The bounded-constructible encoded input K
and its identification with the encoded native complex are explicit parameters of the
coefficient comparison and its combining proof. This keeps the actual condensed map at
an abstract K until the native conclusion. `nativeUnderlyingExchangeArrow` bundles its
underlying map through the inclusion, with invertibility transfer proved for an arbitrary
full subcategory. Rational proper base change supplies the invertible restricted map.
The coefficient equality is handled in a private proved helper.

The change record is `coord/changes/W3-native-derived-exchange-extraction.md`. No adopted
source-library file, other existing Lean module, target statement, or unit route is changed.
The rational proper-base-change clause of the unit remains in the proof.

Validation: lcompile.py accepted all five delivery modules and the unchanged sole direct
importer `Sheaf.WeilSheaf.NativeBaseChangeForgetComparison` (result sets
`0ac57f1db32ad0ee4f960524` and `f2d48717e9bd9dd64c36bf6a`). Cumulative kernel checks
were 0.403 seconds in the comparison module and 1.15 seconds in the affine module.
The only warnings were the temporary profiling options, now removed. The unchanged
consumer copy was removed after its successful check; it is not part of the delivery.

## Proved and sorry left

Original item: one hole. Closed in the item:
`AlgebraicGeometry.NativeBaseChange.geometric_proper_baseChange_isIso`.
The item now has zero `sorry`. This is a decomposition, not a completed axiom-free proof:
the delivery adds two holes, so its syntactic net is 1 closed minus 2 added = -1.

New proved declarations include
`AlgebraicGeometry.ProEtale.adicDerivedBaseChange_isIso_of_affine`,
`AlgebraicGeometry.ProEtale.adicChartSquare`, and the encoding equivalence/additivity
instances, `AlgebraicGeometry.ProEtale.nativeExchangeEncodingAt`, its proved instances,
`AlgebraicGeometry.ProEtale.nativeUnderlyingExchangeArrow`,
`AlgebraicGeometry.ProEtale.nativeUnderlyingExchangeArrow_isIso`.
The geometric Cartesian-square and affine descent helpers are private and proved.
The two extracted definitions contain their original real constructions and zero holes.

Every remaining hole added by this delivery is exactly the body of one public named theorem:

- `AlgebraicGeometry.ProEtale.adicDerivedBaseChange_openChart`, in
  `NativeBaseChangeOpenChart`, node `lem-sf-native-derived-exchange-open-chart`.
  This is restriction compatibility for arbitrary unbounded native complexes on arbitrary
  schemes. It imposes no properness, field, constructibility or boundedness hypotheses and
  asserts no invertibility of the exchange. It is strictly the restriction step of the argument.
- `AlgebraicGeometry.ProEtale.nativeDerivedExchange_condensed_comparison`, in
  `NativeDerivedExchangeComparison`, node
  `lem-sf-native-derived-exchange-condensed-comparison`.
  This compares two specified arrows under exact coefficient transport and fully faithful
  bounded-constructible restriction. It assumes a Cartesian square but no properness hypothesis
  and asserts no invertibility. The properness-dependent mathematical theorem is supplied
  separately by the existing rational proper-base-change declaration.

The open comparison was checked against empty charts, zero complexes, arbitrary g and
nonseparated global schemes: only its open restrictions and Cartesian identifications are
used. The scalar comparison applies to zero objects and arbitrary Cartesian squares;
it makes no assertion that their base-change maps are isomorphisms. Both have complete
natural-language proofs and sources in their docstrings and matching new nodes.

## No longer needed

No existing Lean module is withdrawn, and no source declaration is removed. The original
item had no proof-dependency imports to remove. No original public import is removed.
The geometric argument imports only its chart lemmas, the native cover detector,
`OverSquare`, and the specific `Comma.Over.Pullback` interface.

The following former direct proof dependencies of the geometric node are no longer direct
steps of its proof (some remain needed transitively by the affine/coefficient argument):

- `def-weil-proper-morphism` (`Mathlib.AlgebraicGeometry.Morphisms.Proper`).
- `def-weil-finite-type-morphism` (`Mathlib.AlgebraicGeometry.Morphisms.FiniteType`).
- `lem-sc-separated-over-affine-scheme-separated`.
- `lem-pod-separated-finite-type-base-change`.
- `lem-sf-native-adic-encoding-ordinary-operations` (`Sheaf.Paper.NativeAdicEncodingCore`).
- `lem-weil-pbc-qcqs-over-affine`.
- `lem-sf-native-adic-qcqs-stratification` (`WeilConjectures.SixFunctors.ProEtale.Adic.ExtensionByZero`).
- `lem-sf-weil-verdier-module-constructibility-comparison` (`Sheaf.Paper.NativeModuleConstructibilityComparison`).
- `det-def-sfb-constructible-local-model` (`Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`).
- `lem-sf-finite-span-module-derived-comparison` (`Sheaf.Paper.FiniteSpanModuleDerivedComparison`).
- `det-thm-sfb-proper-base-change-rational` (`Sheaf.Paper.ProperBaseChangeRational`).
- `lem-sf-ringed-restriction-exchange-open-descent` (`Sheaf.AlgebraicGeometry.RingedRestrictionExchangeOpenDescent`).
- `lem-sbc-ringed-topos-sheaf-slice-derived-comparison` (`Sheaf.Paper.SheafSliceDerivedComparison`).
- `lem-weil-pbc-unbounded-derived-iso-cohomology`.

In particular, `Sheaf.AlgebraicGeometry.RingedRestrictionExchangeOpenDescent` and
`Sheaf.Paper.SheafSliceDerivedComparison` are not imported for the geometric
descent. The existing native `Adic.BaseChange.adicDerivedBaseChangeIso` and native
`Adic.MayerVietoris.isIso_of_isIso_mapDerivedCategory_adicUpperStar` supply the direct native
restriction/descent route. Their attachments are new closed source-tool nodes. This is a
local dependency reduction, not a claim that these ringed modules are globally unreachable.

The qcqs stratification, constant-model predicate comparison, finite-span derived comparison
and native ordinary encoding remain available through the appropriate coefficient argument;
no claim is made that they can be deleted from the library.

## Where the brief, the DAG or earlier work was wrong

The original plan says that `finiteSpanModuleDerivedComparison` directly identifies the native
adic exchange with the condensed exchange. Its Lean theorem actually compares internal
condensed modules with sectionwise ringed-site modules. It does not itself expose the
identification with native `AdicSheaf`, nor the compatibility with the conditional
bounded-constructible exchange. The new scalar/mate comparison states exactly this missing
glue. The ordinary native encoding and its coefficient naturality already exist and should be
used in that proof; they are not restated as new holes.

The native source library already proves the open-derived base-change isomorphism and derived
cover conservativity. The old plan instead referred to general ringed-site restriction and
slice modules. The revised argument uses these stronger existing native tools, retaining only
the compatibility of the particular mate with chart restriction as a new obligation.

The attachment of `lem-sf-native-adic-constructible-pullback` currently lists the
source declaration but omits its module field. Its actual existing declaration is
`IsAdicConstructibleSheaf.upperStar` in
`WeilConjectures.SixFunctors.ProEtale.Adic.Constructible`, which the proof uses.
No false statement, changed target meaning, or process/tool failure was found.

## New nodes

`def-sf-native-derived-exchange-map` owns the extracted existing native pull-square and
unit-square-counit constructions in `NativeDerivedBaseChange`, with their unchanged data.

`lem-sf-native-derived-exchange-open-chart` states the precise open-chart compatibility of
the native mate, one new hole in `NativeBaseChangeOpenChart`.

`lem-sf-native-derived-exchange-condensed-comparison` states the scalar-transport and
restricted-adjunction compatibility of the two exchange arrows, one new hole in
`NativeDerivedExchangeComparison`; it also owns the actual encoding wrapper and its proved
instances and the explicit underlying-arrow construction.

`lem-sf-native-affine-proper-base-change` records the proved affine-base application of
rational proper base change in `NativeAffineProperBaseChange`.

`lem-sf-native-adic-derived-cover-conservative` attaches the already-proved native source
theorem `isIso_of_isIso_mapDerivedCategory_adicUpperStar`; no source file is edited.

`def-sf-native-adic-derived-open-base-change` attaches the already constructed source
isomorphism `adicDerivedBaseChangeIso`; no source file is edited.

The six nodes inherit chapter `sec-six-functors` and unit `sk-thm-sf-package`. Blueprint
searches for native derived exchange, affine proper base change, adic cover isomorphism and
adic open base change found no exact blueprint duplicates. Search results and proof steps are
in the node records. The parent node changes only its proof, proof dependencies, proof origin
and Lean attachment. The change record is
`coord/changes/W3-native-derived-exchange-extraction.md`.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
