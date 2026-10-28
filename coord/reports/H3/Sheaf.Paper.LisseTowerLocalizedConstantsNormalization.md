## What changed

Repaired `AlgebraicGeometry.Scheme.lisseTower_localized_constants_normalization`
in `Sheaf.Paper.LisseTowerLocalizedConstantsNormalization`. Its former universal
claim for arbitrary objectwise model isomorphisms is false. The replacement is a
proved criterion: natural model isomorphisms whose coefficient identity holds on
images of cochain complexes give the original square for every derived semilinear
arrow, including arrows that are not represented by chain maps. The proof uses
`Localization.natTrans_ext`, naturality, and the specified coefficient compositors.

The item adds the actual functors and natural isomorphisms
`lisseTowerConstantInput`, `lisseTowerPasteConstantScalar`,
`lisseTowerConstantScalarIso`, `lisseTowerAlgebraRestrictIso`, and
`lisseTowerConstantModelIso`. Every definition is constructed without a hole or an
existence choice. The abstract pasting helper keeps the kernel from unfolding the
large coefficient sheaves. The item and its definitions compile in 17.4 seconds.

Added `Sheaf.Paper.LisseTowerConstantComplexComparisons` for the remaining canonical
construction. Adapted the unclaimed `Sheaf.Paper.LisseTowerLocalizedConstants`:
it obtains the natural comparisons and coefficient identity together, takes their
components, and applies the proved criterion. Its theorem signature is verbatim
unchanged. Target statements, target definitions, and all adopted source-library
files are unchanged. The unchanged direct consumer `Sheaf.Paper.LisseTowerLocalizedRealization`
compiled against this packet in 20.3 seconds. All four files compiled without
errors or non-hole warnings, each below 60 seconds. Its temporary source copy was
removed after the check. The change record is
`coord/changes/lisse-tower-constant-model-coherence.md`.

## Proved and sorry left

The assigned module originally had one hole, in the false statement
`AlgebraicGeometry.Scheme.lisseTower_localized_constants_normalization`. This
packet does not claim to prove that false statement: **0 of the 1 original holes
are counted as proved**. Its corrected localization/naturality criterion is fully
proved; the item now contains **zero** `sorry`s. The parent
`AlgebraicGeometry.Scheme.lisseTower_localized_constants` remains a complete proof
from named dependencies with its original signature.

Exactly one hole is added, and it is the only hole in the delivered Lean files:
`AlgebraicGeometry.Scheme.lisseTower_constant_complex_comparisons`, node
`lem-weil-pbc-lisse-tower-constant-complex-comparisons`. It constructs natural model
comparisons and verifies only the identity coefficient square at represented
complexes. It does not quantify over arbitrary derived semilinear arrows. The
proved argument extending that identity to arbitrary arrows is in the item, rather
than left inside this hole. This is a statement repair and decomposition, not a
proof of the former universal claim. The canonical construction remains to be
formalized; the source and full argument are in the new theorem's docstring and
node. Its use is theorem elimination in the parent's proof; no definition chooses
arbitrary data from it.

## No longer needed

The parent no longer imports `Sheaf.Paper.LisseTowerLocalizedConstantsModel`, and
its node no longer has
`lem-weil-pbc-lisse-tower-localized-constants-model` as a proof dependency.
Objectwise nonemptiness cannot supply the needed joint coefficient coherence.
That module is held by X7 and is not edited or withdrawn; it remains available to
any other argument. The replacement construction provides the models and their
compatibility together.

Removed the item's proof-only `Mathlib.Data.ZMod.Basic` import and its two private
sign diagnostics. They diagnosed the old arbitrary-choice error; they are not
used by the corrected criterion. The counterexample explanation and old signature
remain in the X8 report and this packet's change record. Removed the parent's
redundant private import of
`Sheaf.Paper.LisseTowerLocalizedConstantsNormalization`, which is already public
through the new construction module.

The original coefficient, finite-realization, inverse-image, and constant-sheaf
dependencies remain necessary. No blueprint unit statement or unit proof step is
bypassed, and no Lean file or DAG node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The old split separated existence of arbitrary objectwise models from a theorem
claiming their normalization for every choice. This loses the coherence the parent
needs. As X8 observed, multiplying one level's chosen model by minus one changes
only one side of the claimed transition equation. Naturality at each level alone
also leaves independent scalar automorphisms at different levels. This is the
`STATEMENT-DISPUTED` defect assigned by the current queue, not an absent dependency
or an already-complete zero-hole item.

The repair changes that false intermediate interface explicitly, with its old and
new signatures and the sole existing consumer in the change record. The new
condition is supplied jointly with the models by the remaining construction
theorem; the parent gains no hypothesis and loses no conclusion. In particular,
this packet does not claim that an arbitrary model can be normalized afterwards.

The new statement is distinct from the old model-existence lemma (which has no
naturality or coefficient compatibility), the old false universal lemma, and the
parent (which asserts the square for every derived arrow). The actual reduction
is: check the identity square on represented complexes, use localization to obtain
an equality of natural transformations, then use naturality at an arbitrary
semilinear arrow. Its last two steps are written and compiled Lean. The remaining
construction follows constant-sheaf adjunctions and uniqueness of module
sheafification ([Stacks 0H7J](https://stacks.math.columbia.edu/tag/0H7J),
[03CY](https://stacks.math.columbia.edu/tag/03CY)); coefficient restriction and exact
localization use [03DA](https://stacks.math.columbia.edu/tag/03DA) and
[06YY](https://stacks.math.columbia.edu/tag/06YY).

## New nodes

`lem-weil-pbc-lisse-tower-constant-complex-comparisons`, in
`dag/nodes/sec-proper-base-change/`, realizes the single remaining theorem in
`Sheaf.Paper.LisseTowerConstantComplexComparisons`. It records the ordinary
constant-model construction, the identity coefficient check on constant sections,
and passage termwise to complexes. Its statement includes zero complexes, zero
coefficient rings, and empty schemes. It has source references, a complete proof
plan, three actual Mathlib searches, and the attachment to this new module. The
existing normalization node records the corrected criterion and its proof; the
parent's node records the new dependency and componentwise assembly. The change
record is `coord/changes/lisse-tower-constant-model-coherence.md`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.LisseTowerConstantComplexComparisons": "a6153f029cd9af33a31cf9587090f85d842191e1", "Sheaf.Paper.LisseTowerLocalizedConstants": "b06197969c1d021d1f57d6451856e81f5bfe39e7", "Sheaf.Paper.LisseTowerLocalizedConstantsNormalization": "57b51c44c0a18765e923b7eafb9f64fe0b7ae208"}, "results": {"Sheaf.Paper.LisseTowerLocalizedRealization": {"hash": "7fc02abbc15c7911b37fc7c4d346153166d44694", "status": "OK"}}, "seconds": 44, "time": "2026-10-28T12:11:55+0800", "transitive": 0, "version": 1}
```

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
