## What changed

Filled all three original holes in `Sheaf.Paper.TraceBaseChangeFirst`. The ordinary
tensor normalization follows from the balancing quotient and the adjunction;
flatness follows from the existing inverse-image and scalar-extension results.
The square-family calculation is proved over abstract ordinary categories, then
specialized as the private folded proposition `traceDataSquare` over the same
bundle of comparison data. It is explicitly reassociated with `Category.assoc`.
The unit conversion uses the proved generic equality-transport helper. Private
coherence lemmas identify the chosen ordinary structure with the existing
one, derive braiding and composition compatibility, and prove the trace identity
by adjunction transposes, the Kunneth factorization and trace cancellation.

`TraceComparisonData` stores the three canonical tensor structures, the specified
degree-zero unit, tensor comparisons and Koszul braidings once. Its constructors
first work over abstract abelian categories, then internal modules, then the three
native pullbacks. `TraceFirstAssertion` calls the same `TraceFirstFormula` through
`traceDataFormula`, using those fields. Each field is the existing canonical
construction. This follows the existing derived-completeness implementation's
solution to proof-abstraction expansion: concrete monoidal instances occur inside
bundle bodies rather than being elaborated repeatedly in declared types.

The ordinary sheaf-symmetry cache is reflexively equal to the existing symmetry.
The generic unit function contains the original explicit degree-zero composite;
its equality with the derived monoidal unit is proved. The generic braiding is the
existing named wrapper's braiding. The node records the actual proof route and
all new public data declarations. The change record
`coord/changes/trace-base-change-first-braiding-cache.md` documents the unchanged
mathematical formula, consumers and renewed statement review.

The generic square and trace calculations compile. The complete module is checked
by the delivery compile and preflight. The two archived consumers were inspected;
their used signatures are unchanged and neither uses a removed alias or the
changed assertion body. No consumer compilation is asserted for these archived
modules.

The three theorem signatures and all retained public signatures stay unchanged.
Three unused aliases are pruned as detailed below. There are no new nodes or
split-off results, and no source-library file changes.

## Proved and sorry left

Original holes closed:

- `AlgebraicGeometry.ProEtale.CondensedRing.condensedTensorCore_existsUnique`.
- `AlgebraicGeometry.ProEtale.CondensedRing.condensedUpperStarPreservesFlat`.
- `AlgebraicGeometry.ProEtale.CondensedRing.trace_base_change_first`.

Holes added: none. Holes left in delivered Lean files: none. No split-off theorem.
The proof uses existing library declarations whose proofs remain work elsewhere.

## No longer needed

Pruned the unused public aliases
`AlgebraicGeometry.ProEtale.CondensedRing.condensedDerivedTensorIso`,
`AlgebraicGeometry.ProEtale.CondensedRing.condensedDerivedSymmetry`, and
`AlgebraicGeometry.ProEtale.CondensedRing.condensedDerivedTensorComparison`, with
their Lean attachments. The bundle stores the very same canonical Koszul braiding;
the assertion no longer uses a second native alias. A scan of both source roots,
the entire quarantine, node and unit records found no external consumer for any
alias. The prior review also records the tensor-isomorphism alias as unused. The
statement bundle and the square proof use the same explicit natural transformation
directly, without its unused native alias.

Removed the direct proof imports `Sheaf.Paper.ProjectionMateExact`,
`Sheaf.Paper.RingedProjectionTensorComposition`, and
`Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`.

This proof does not use the declared dependencies
`lem-sfb-ringed-kunneth-factorizations`,
`lem-sfb-ringed-derived-monoidal-comparisons`,
`lem-sfb-ringed-projection-tensor-composition`, or
`lem-weil-pbc-ringed-projection-mate-exact` as lemmas. Their formal identities are
proved directly using the given adjunctions and tensor comparisons, rather than
transporting the concrete categories through a separate ringed-topos model.

`Sheaf.Paper.RingedKunnethFactorizations` is not imported.
`Sheaf.Paper.RingedProjectionTensorComposition` is no longer in this module's
import closure. `ProjectionMateExact` and `RingedDerivedMonoidalComparisons` remain
reachable through other imports; this delivery does not claim they can be removed
from the library. No source-library declaration or module is withdrawn.

The obsolete top-level `tool_uses` approvals were removed for:

- `lem-sfb-ringed-derived-monoidal-comparisons`.
- `lem-weil-pbc-adjunct-counit-identity`.
- `lem-sfb-ringed-projection-tensor-composition`.
- `lem-weil-pbc-ringed-projection-mate-exact`.
- `lem-sfb-ringed-kunneth-factorizations`.

The corresponding library statements are not used by this proof.

## Where the brief, the DAG or earlier work was wrong

The planned ringed-topos comparison lemmas use a different presentation of the
module categories, so applying them directly would require additional transport.
The argument itself applies to arbitrary monoidal categories and is carried out
with the operations already fixed in this statement. The public statement and
its mathematical hypotheses are unchanged.

## Second reading by V9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
