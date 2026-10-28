## What changed

Replaced the one `sorry` in
`WeilConjectures.LocallyFiniteAdicRealization.normalizedFunctor_descent_image`
by a complete Lean assembly from two concrete finite tensor statements and existing
proved descent and encoding results. Its signature, universes, hypotheses, public import,
and visibility are unchanged. No other existing Lean module or definition is changed.

The forward implication encodes the native object using
`NativeEncoding.encoding_boundedConstructible`, applies the proved
`constructibleCocone_essSurjObj`, maps its full-subcategory isomorphism to the ambient
category, and uses the inverse derived encoding and its equivalence unit. A finite integral
representative gives a source pair. The proof composes `D.integral` with the tensor-model
isomorphism and lifts the resulting section-module isomorphism using `preimageIso`.
The section functor is an equivalence by the proved scalar-forgetting theorem and the
internal/section equivalence. The reverse implication destructs an actual source pair and
its raw integral representative and applies the tensor-constructibility statement to the
isomorphism obtained from `D.integral`.

The new statements have no normalized-functor argument or global essential-image conclusion.
The model statement starts with an already descended condensed complex over one fixed E and
returns an integral object at that same E. The preservation statement concerns one explicit
integral tensor extension. Thus the actual algebraic-closure descent, source-pair assembly,
and isomorphism lifting remain proved in the item, rather than delegated under another name.

All three files compile cleanly with `lcompile.py --all`; the latest times are 4.9 seconds
(model), 3.8 seconds (preservation), and 4.4 seconds (item). New statements were checked against
the zero complex, rank-zero strata, the empty scheme, arbitrary finite E including the base
field, and arbitrary normalized coefficient presentations. Residue and pointwise
normalization make the asserted tensor maps independent of presentation choices. There is
no field-of-definition enlargement in the new model statement.

## Proved and sorry left

This is a decomposition, not a completed proof or a net decrease in holes.
One old hole is discharged, two new holes are added, for net minus one hole closed.

Closed declaration:
`WeilConjectures.LocallyFiniteAdicRealization.normalizedFunctor_descent_image`
(node `lem-sf-locally-finite-adic-functor-descent-image`). Its combining proof has no `sorry`.

Remaining holes, one in each new module:

- `WeilConjectures.LocallyFiniteAdicRealization.nativeIntegralTensor_constructible`,
  node `lem-sf-native-integral-tensor-constructible`, module
  `Sheaf.Paper.NativeIntegralTensorConstructible`.
- `WeilConjectures.LocallyFiniteAdicRealization.condensedFinite_integralTensor_model`,
  node `lem-sf-condensed-finite-integral-tensor-model`, module
  `Sheaf.Paper.CondensedFiniteIntegralTensorModel`.

Each is a public theorem with exactly `:= by sorry`, a source and a proof in words.
There is no definition, private helper, or arbitrary chosen construction containing a hole.

## No longer needed

The item no longer directly imports:

- `Sheaf.Paper.ContinuousRationalDerivedRealization`.
- `Sheaf.Paper.RationalCoefficientCategoryComparison`.
- `Sheaf.Paper.CondensedFlatCoefficientCalculus`.
- `Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality`.
- `Sheaf.Paper.CondensedQbarLfpLocalTriviality`.
- `Sheaf.Paper.CondensedQbarFunctionCoefficients`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit`.

The last is now a public statement dependency of the finite condensed model module, and
its proved object clause is used by the main proof. Finite realization, finite-field local
triviality and flat tensor calculus remain mathematical dependencies of the new finite
statements; they are not claimed pruned globally. The full geometric Frobenius coefficient
comparison is unnecessary: only integral category transport is needed, supplied by
`integralStratifiedPerfectDetailed`. The separate algebraic-closure local-triviality theorem
is unnecessary for the assembly because the existing native encoding theorem already
supplies the required one-way constructibility inclusion.

No module is withdrawn, and no globally unreachable module is claimed. The unit route and
the parent image-descent dependency are preserved. The main node's proof dependencies now
record the actual encoding, scalar-forgetting, object descent and two finite tensor steps.

## Where the brief, the DAG or earlier work was wrong

The original node combines distinct coefficient transports in one prose step. Its existing
continuous rational realization theorem has the required general Noetherian hypotheses,
but its essential-image predicate and coefficient presentation are not definitionally the
condensed finite-stage predicate or the native section coefficient. The remaining work is
these normalized tensor comparisons, not a missing global object-descent theorem: the latter
is already proved as `constructibleCocone_essSurjObj`.

The nearby `CondensedERealization` theorem assumes a separated finite-type scheme over a
field, which the present general statement does not assume. The common-stage theorem in
`SfAdicCommonStageDescentEquivalence` imports the native realization parent, so using it here
would introduce an import cycle. Neither is used. No statement is weakened or disputed.

Read Bhatt--Scholze Lemmas 6.8.2 and 6.8.13 and Propositions 6.8.11(3) and 6.8.14, including
the integral-lattice and raw-localization arguments. The current blueprint's Verdier
paragraph now emphasizes the direct native route; it does not itself supply these missing
coefficient-identification proofs. The assigned source-based obligation is retained.

Mathlib searches were actually run with `msearch.py` and are in `searches.jsonl`: semantic
queries for both tensor assertions, a grep for bounded tensor/integral models, and Loogle
for `Functor.preimageIso`. They produced no matching coefficient-specific theorem; the
generic `preimageIso` API is used in the complete assembly. Repository searches also found
no existing theorem identifying these explicit native integral tensors with the finite
condensed models. No shared interface changes or forced adaptations require a change record.

## New nodes

`lem-sf-native-integral-tensor-constructible` states preservation of native bounded
constructibility for the concrete tensor extension of one integral constructible complex.
Its proof uses integral stratified perfect models, localization and flat coefficient
extension, followed by exact section-module transport. It does not construct any global
realization functor or assert its essential image.

`lem-sf-condensed-finite-integral-tensor-model` states existence of an integral tensor model
for one already finite condensed object, at the same coefficient field. Its proof uses
finite-field local triviality, continuous rational realization and its unchanged integral
objects, integral category transport, and normalized balanced tensor associativity. It does
not descend an arbitrary algebraic-closure object. Both nodes retain the item's chapter
and unit and attach their exact Lean statements to their own new modules.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CondensedFiniteIntegralTensorModel": "3efd3ae201ab9b8bf105c7a1b1c25b6d082fc383", "Sheaf.Paper.LocallyFiniteAdicFunctorDescentImage": "456e56444c2bb839b480ce3a6136bf403a0a15f3", "Sheaf.Paper.NativeIntegralTensorConstructible": "89f3f7ec93917097156c8a3b0b8097a924846469"}, "results": {"Sheaf.Paper.LocallyFiniteAdicFunctorDescent": {"hash": "5faeced6a7cc469b2c116417093b5ee54ffe2443", "status": "OK"}}, "seconds": 129, "time": "2026-10-28T10:29:28+0800", "transitive": 0, "version": 1}
```

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
