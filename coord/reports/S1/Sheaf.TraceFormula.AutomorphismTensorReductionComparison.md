## What changed

The proof of `automorphismTensorReductionComparison` assembles the existing
scalar-extension ring-isomorphism theorem into a natural isomorphism of strict
module systems and then maps it to ordinary unbounded complexes. Private proved
helpers identify adjacent coefficient restrictions, raw and transported module
restrictions, and inverse coefficient components and actions. Exactness follows
by forgetting to abelian sheaves and using the product site equivalence; the
forgetful functor reflects the required finite limits and colimits. The
quotient transition square follows from the existing coefficient-naturality
theorem. The completed square follows from the recorded limit-lift definition.

Every public theorem signature is preserved. Four definition presentations are
simplified without changing their mathematical objects: raw transport uses
`PresheafOfModules.pushforward₀` directly; inverse image factors raw transport
and scalar restriction; finite raw transport uses the same constructor; finite
tensor has its existing codomain stated explicitly. The tensor construction itself is unchanged. There are no downstream
modules or declaration users outside this item. The change records are:

- `coord/changes/trf-automorphism-raw-module-transport.md`
- `coord/changes/trf-automorphism-system-inverse-factorization.md`
- `coord/changes/trf-automorphism-finite-tensor-return-type.md`
- `coord/changes/trf-automorphism-finite-raw-transport.md`

The existing additivity proof now uses its scalar-extension addition calculation
at arbitrary ring sheaves, keeping the concrete coefficient rings folded.
The new explicit constructor `WeilConjectures.trfRawModuleTransport` is
registered under the existing item node and used by the public raw transport.
A private proved exactness theorem treats arbitrary ring sheaves before
specializing this constructor to the coefficient rings. Private proved
identifications relate the existing pure-tensor section constructions and the
underlying module maps.

The node proof records the sequence-site implementation of the same seven
comparison steps. No other Lean module is changed.

Validation: the final module compiled through `lcompile.py` in 29.6 seconds,
with no errors or warnings.

## Proved and sorry left

Original holes: 3. The proof of
`WeilConjectures.automorphismTensorReductionComparison` is supplied; no hole is
added. Existing holes remain in
`WeilConjectures.trfAutomorphismCoefficientComponent_naturality` and
`WeilConjectures.trfAutomorphismTensorEvaluation`, both attached to
`lem-trf-automorphism-tensor-reduction-comparison`.

The private helper theorems have complete proofs. The main theorem depends on
the existing coefficient-naturality theorem, as expected in stage 3.

## No longer needed

No imports, declarations, modules or nodes are withdrawn. The proof no longer
uses the componentwise exactness assertion of
`lem-coef-semilinear-derived-sections`: exactness follows on the entire sequence
site instead. Its proof-dependency edge is removed; the node remains a statement
dependency for the recorded system category. Existing public imports remain part
of the module's interface.

## Where the brief, the DAG or earlier work was wrong

The current read-only source has a proved private `finiteCoefficientTransport`
helper in `InverseImagePullbackComparison`, but the remote compiled snapshot
used during this session does not yet expose that helper. An environment probe
confirmed its absence. The proof does not duplicate it: the quotient square is
instead deduced from the item's existing coefficient-naturality statement.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
