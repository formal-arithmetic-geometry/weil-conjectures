## What changed

Partial delivery: proved middle naturality and the typed three-factor assembly;
the original scalar-compatibility theorem remains open and is marked
`STATEMENT-DISPUTED` for the normalization gap described below.

Refactored `middle` as the component of the new `middleFunctor`. The theorem
`middle_component` identifies it with exactly its previous canonical formula:
pullback/tensor, shifted root-line pullback, and the ordinary pullback square.
`tensorComparisonUnique` proves that the natural tensor comparison is uniquely
determined by its specified components. Its selection in `middleFunctor` therefore
uses uniquely determined data, as required by the data-selection rule. Moreover,
`tensorExchangeIso` keeps the literal canonical component isomorphisms as its data;
the selected natural comparison is used only to prove their naturality.
The generic `tensorExchangeIso` construction supplies naturality before the
specialization to rational constructible categories.

The earlier literal hom-expansion proof exhausted the kernel limit while comparing
repeated category and coefficient-instance aliases. The functor construction and
its component API avoid that reduction. All original signatures, public imports,
`exchange`, and `Conclusion` remain unchanged. The definition change is recorded in
`coord/changes/F9-smooth-exchange-middle-functor.md`.

The proved private helper `assembleExchange` pastes normalized endpoint and middle
scalar squares, identifies every component with `exchange`, transfers the two
endpoint unit and tower laws, and composes the three shift laws. Its normalization
premises are explicit; no unjustified universal existence assertion is added.

Added private proof imports `Sheaf.Paper.RationalPurityExchangeEndpoints` and
`Sheaf.Paper.DerivedPullbackTensorIso`. No existing module outside the item changed. The complete module compiled in
41.5 seconds before the final removal of unused section assumptions; delivery
checks validate the final version.

## Proved and sorry left

Holes closed: 0 of 1. Holes added: 0. Split off: 0.

Proved in `WeilConjectures.SmoothExchangeScalarCompatibility`:

- private `pasteScalar` and `pasteShift`;
- `tensorMiddle_naturality`;
- `tensorExchangeIso` and `tensorExchangeIso_app`;
- `tensorComparisonUnique`;
- `middleFunctor`, `middle_component`, and `middle_naturality`;
- private `assembleExchange`.

The definitions above contain no `sorry`; the only selected natural isomorphism
has a proved uniqueness clause. The normalized comparison existence input is the
already stated rational clause of `derivedPullbackTensorIso`.

For `assembleExchange`, the premises are the actual endpoint records, the two
canonical gamma component identifications, and the natural middle comparison with
its component, scalar and shift equations. Its proof constructs the three-factor
composite and checks every clause. This is the conditional assembly of the plan,
not a replacement axiom with the original theorem's conclusion.

Still `sorry`:
`WeilConjectures.SmoothExchangeScalarCompatibility.smoothExchangeScalarCompatibility`
(blueprint `lem-pur-smooth-exchange-scalar-compatibility`). No other hole is added.
The missing assertions are the arbitrary-system normalization and identification
with the supplied endpoint families, including their shift structures; these have
not been asserted as new lemmas because the current interfaces do not justify them.

## No longer needed

Removed the direct private proof imports:

- `Sheaf.Paper.RationalScalarComparisonIdentification`;
- `Sheaf.Paper.PbcRationalTransport`;
- `WeilConjectures.EtaleCohomology.Purity.Smooth.Reduction`.

The typed assembly uses the already defined maps and the endpoint equations; it
does not reconstruct or rationalize the exchange a second time. This is removal
of unused direct proof imports. The original theorem remains open, its planned
normalization dependencies remain in its node, and no entire module or node is
claimed pruned from the targets' closure. The unit route is retained.

## Where the brief, the DAG or earlier work was wrong

The stated dependency theorem `rationalPurityExchangeEndpoints` takes both
`I : Data D C f d S` and `I' : Data D C f' d S'` as inputs. In contrast,
`Conclusion` quantifies over every `S` and `S'`. The existence theorem
`adicPurityScalarNaturality` produces some `S` with `Data`; it does not produce
`Data` for an arbitrary supplied system. Nor does `LocalizedFamily` identify its
`gamma` with the published `rationalIso`: it localizes its supplied `I.gamma`.
This gap cannot be filled by applying that endpoint theorem directly.

There is a concrete reason not to assert the missing stronger bridge:
`Data` extends `OperationData`, whose `TargetOperationData.finiteRightNormalized`
requires an explicit Hom-transpose identity. `RingSystem.finiteRight` is merely a
natural isomorphism with the right endpoints. The `System` fields impose no such
identity on it. Changing that field leaves the operations, adjunctions, left
realizations and coefficient comparison fields unchanged, while it can change
the equation demanded by `finiteRightNormalized`. Thus an assertion of `Data`
for every `System` would add normalization absent from its definition.

There is also a shift issue requiring independent review: `Operation.leftShift`
and `Operation.rightShift` are supplied structures, and `LeftRealization` is an
unshifted natural isomorphism. The unit/counit shift identities relate the two
supplied shifts, but do not identify them with the ordinary realized shifts.
Likewise `FieldComparison.shiftX` and `shiftY` are supplied separately. The
canonical pure middle shift equation cannot simply be transported to two
unrelated `LocalizedFamily.hShift` structures without proving their compatibility.
The helper makes that required equation explicit rather than assuming it follows
from equality of the underlying functors. The identity-square, d=0 specialization
already requires the two resulting shift structures to agree through the canonical
purity composite; equality of functors alone does not establish this.

The read-only importer check used direct source searches and found no current Lean
importers. The generic `tools/downstream.py` scanner opens a cache under `local/`,
despite describing itself as reading sources only; it was stopped rather than used
further on this read-only checkout. No launcher or project tool was edited.

The two missing normalization assertions were tested before being committed to a
split: the proposed arbitrary-system `Data` existence is too strong, so neither it
nor a purported universal middle shift bridge is in this packet. The theorem's
signature and every clause of `Conclusion` have been preserved for the independent reader to
resolve the correct normalization repair.

The current blueprint source read was
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-purity-transport/`
`sk-thm-purity-transport.proof.md`, Steps 1–4, and its coefficient-change proof.
It requires the counit-preserving canonical comparison. The DAG's older proof
source path is absent from the latest snapshot; the partial proof-origin record
now cites the existing current source.

## Second reading by F9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
