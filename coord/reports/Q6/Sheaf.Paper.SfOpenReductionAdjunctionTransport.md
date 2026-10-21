## What changed

The statement and all existing definitions in
`Sheaf.Paper.SfOpenReductionAdjunctionTransport` are unchanged. Its theorem now combines
canonical restriction models and ordinary restriction completeness with explicit formal
adjunction calculations. Private proved helpers construct the natural inverse-unit
isomorphisms, identify the system unit and counit using Mathlib's mate correspondence,
and prove completion normalization, including every finite Roos projection.

Two new modules isolate geometric results from original steps 2--4:
`Sheaf.Paper.CanonicalOpenRestrictionModel` and
`Sheaf.Paper.OpenRestrictionCompleteness`. The former is independent of reconstruction
and realized adjunctions; the latter is independent of both reduction calculi and the
supplied extension comparison. The main theorem's proof combines their conclusions
with the actual units and counits, rather than assuming the realized identities.

## Proved and sorry left

Closed the original explicit hole in
`WeilConjectures.OpenReductionAdjunctionTransport.openReductionAdjunctionTransport`.
The item module has zero remaining holes. Added two geometric holes:

- `WeilConjectures.CanonicalOpenRestriction.canonicalOpenRestrictionModel`, node
  `lem-sf-canonical-open-restriction-model`.
- `WeilConjectures.OpenRestrictionCompleteness.openRestrictionComplete`, node
  `lem-sf-open-restriction-completeness`.

This is a decomposition, not a net hole reduction: one original hole is closed and
two holes are added. The formal inverse-unit naturality, reduction normalization,
realized unit, realized counit and completion projection calculations are proved.

Validation: the main module compiled without warnings through `lcompile.py` (54.3 s).
The delivery tool performs the full sandbox and axiom checks.

## No longer needed

Removed the direct proof imports
`Sheaf.Paper.SfImmersionCompletedPullbackComparison` and
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses` from the item. Their
geometric content remains needed below the two new nodes; neither module is withdrawn.
The item no longer directly uses
`lem-sf-open-semilinear-tensor-model`: its ExtensionModel is already a hypothesis, so
constructing another extension comparison is unnecessary. This is local pruning only;
no claim is made that this module is unused by other parents.
`lem-sf-open-tensor-normalization` and `lem-coef-semilinear-derived-sections` are used
in the geometric representative argument, not in the final formal calculation.
The corresponding direct proof dependencies and obsolete direct tool-use entries are
removed from the item node. No library module or declaration is deleted.

## Where the brief, the DAG or earlier work was wrong

The original CompletionModel clause is a general consequence of the defining
normalization of completionUnit; it needs neither completeness nor immersion theory.
The inverse-unit normalization and realized identities need only mate identities,
unit naturality and the adjunction triangle identity.

The geometric dependencies are mathematically relevant but cannot be applied verbatim
to the supplied interfaces: the immersion theorem ties the site and coefficient
universes together, uses another completed-coefficient presentation, and its strict
pullback unit is not definitionally the target completionUnit. The semilinear tensor
existence theorem chooses operations and requires coherence inputs, whereas this item
fixes operations and assumes their extension model. The new lemmas explicitly retain
the fixed operations and independent universes rather than identifying these inputs
without proof.

Mathlib searches found the generic mate identities and no geometric strict-system
or quotient-completeness theorem. Searches of the adopted source and project library
found exact localized restriction, tensor restriction and K-flat preservation; they
still require the fixed coefficient-equivalence and augmented-quotient transport.
The empty and identity opens and the zero complex satisfy both new statements. A
compatible twist of the finite evaluation maps cancels with its extension mate; an
incompatible twist violates the extension-model hypothesis. No assumption was added
to the original statement and no source-library declaration was changed.

## New nodes

`lem-sf-canonical-open-restriction-model` records the construction of the strict
augmented quotient restriction comparison and its identification with the mate of
the supplied extension comparison. Its module contains the expanded model formulas
to avoid importing the parent and creating a cycle.

`lem-sf-open-restriction-completeness` records ordinary open restriction's preservation
of quotient completeness and invertibility of its actual target completion unit.
It keeps site and coefficient universes independent. Both nodes serve the integral
open-factor adjunction sentence of `fix-prop-coherence` in the existing compatibility
unit. There are no definition changes and no change records.

## Second reading by Q6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
