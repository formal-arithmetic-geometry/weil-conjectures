## What changed

Completed all three original obligations in `Sheaf.Paper.ConstantWeilStructure`.
The regular single complex is good by flatness of the tensor unit and zero terms,
then bounded-above K-flatness. For the chain unit, transport the degree-zero
positive-line comparison to single complexes and compose its inverse with the
library's normalized strict pullback augmentation. Its two normalization equations
are checked in Lean using naturality of the module-pullback and scalar-reduction
units. Maps from the single regular module are determined by the section one on
base-change objects, since base change along an isomorphism is an equivalence.
Product projections and the mapping-cocone decomposition then prove uniqueness.

Uniqueness identifies the published chain unit with that composite. The regular
object is constructible and the general augmentation theorem makes its image in
the derived category invertible. The auxiliary finite-field datum required by the
existing constructibility API is explicitly constructed: characteristic 3 if
`l = 2`, and characteristic 2 otherwise. It imposes no hypothesis on the scheme.

Added five proof-only imports: bounded-above flat K-flatness, the independent
coefficient tensor comparison, categorical zero flatness, the Frobenius coefficient
normalization API, and the normalized scalar-reduction adjunction. Existing public
signatures, definitions, docstrings, and public imports are unchanged. All added
helpers are private and proved. No other Lean module is adapted.

## Proved and sorry left

Closed all three original holes, each belonging to
`def-weil-constant-weil-structure`:

- `WeilConjectures.constantWeilIntegralComplex_good`;
- `WeilConjectures.constantWeilChainUnit_existsUnique`;
- `WeilConjectures.constantWeilChainUnit_isIso`.

No sorry remains in the item. No hole is added, and no statement is split off.
The proof uses existing named library theorems, including the still-open general
positive-line and strict-augmentation theorems; their source declarations are
unchanged. The two new DAG nodes below attach those existing independent results.

## No longer needed

Removed the direct proof imports
`Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage` and
`Sheaf.Paper.SfConstructibleHeart`, added to the live source during the earlier
interruption: their APIs remain available through the existing public imports
and the proof dependencies actually used. No node or module is pruned from the
import closure. All original stated proof dependencies are retained. A second construction of the finite pullback Roos
augmentation and its quasi-isomorphism argument is unnecessary: the completed
proof specializes the already declared general normalized augmentation and proves
the regular-single-complex normalization and uniqueness directly.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox report recorded only the K-flatness proof; both remaining
chain-unit obligations are now completed. The old node's unfinished proof step is
replaced by the actual Lean argument.

The general positive-line and augmentation theorems were attached only to the
large Frobenius-twist definition node. That definition also refers to constant
Weil structures. Using the whole definition as a proof dependency would create
a DAG cycle even though these independently stated lemmas do not import or use
the constant Weil chain unit. The two new nodes record precisely the existing
independent helper declarations. They introduce no new Lean statement or module.
The unit's realized statement and proof-step lists are empty, so no unit route is
bypassed. No definition or statement repair, or change record, is needed. The resumed dry
run detected a file-wide namespace opening and elaborator setting in the retained
packet; the helper names are now qualified and the setting is declaration-local.
The visible interface matches the current source exactly.

## New nodes

`lem-weil-positive-line-pullback-normalization` attaches the existing
`FrobeniusCoefficientTwists.existsUnique_positiveLineMaps` and `positiveLineMaps`
to their own self-contained dependency node. Only its degree-zero specialization
is used here. It retains the source's actual scalar/root normalization and the
scheme-isomorphism hypothesis.

`lem-weil-strict-pullback-augmentation` attaches the existing
`FrobeniusCoefficientTwists.existsUnique_pullbackAugmentation`,
`pullbackAugmentation`, and `pullbackAugmentation_isIso`. It records both strict
cone-component equations and the exact good-complex/constructibility hypotheses
of the quasi-isomorphism result. Both nodes point to declarations already present
in `Sheaf.Paper.FrobeniusCoefficientTwistsCanonical`; no new sorry is introduced.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
