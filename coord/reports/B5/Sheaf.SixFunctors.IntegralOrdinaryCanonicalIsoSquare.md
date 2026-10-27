## What changed

Replaced `ordinaryCanonicalIsoSquare` by a case analysis on all nine canonical
isomorphism constructors. Pull/proper/open composition, tensor reassociation,
clopen comparison, cartesian open base change and open projection are proved
by the normalized coefficient maps, their naturality, and adjunction transposition.
Compactification expansion is the identical open/proper recursion.

Added `Sheaf.SixFunctors.CanonicalReductionTensorPull`: the remaining geometric
input is a primitive square on two arbitrary ordinary derived objects. It has no
expression syntax, child coefficient maps, compactification, or open generators.
The main proof proves substitution into arbitrary expression children and the
open-projection transpose from this primitive square. Its public statement and
all existing definitions and public imports are unchanged. No other existing
module is changed.

Each constructor square has a proved private lemma. The base-change argument first
specializes formal mate pasting to the geometric functors with variable comparison
isomorphisms, then inserts the canonical isomorphisms and their normalization fields.
The irreducibility attributes used to control unfolding are local to this proof file.

Validation: the complete item compiled through `lcompile.py` in 52.9 seconds;
the new primitive compiled separately in 45.9 seconds. Both are below the
60-second limit. The delivered sources contain no profiling options or temporary
modules. The original theorem signature is unchanged, and both node JSON records
parse and match their Lean statements.

## Proved and sorry left

Original holes: 1. Closed: `WeilConjectures.IntegralSystemRealization.ordinaryCanonicalIsoSquare`
(node `lem-sf-integral-ordinary-canonical-iso-square`).

Added: 1, `WeilConjectures.IntegralSystemRealization.canonicalReductionTensorPull`
(node `lem-sf-canonical-reduction-tensor-pull`). This is the only remaining `sorry`
in the delivery. There are no holes in private helpers or definitions.

This is a decomposition: one upper hole closed and one strictly smaller primitive
hole added, hence zero net holes closed. The remaining statement is only the
normalized pullback/tensor coefficient square on two objects; eight generator
families and substitution/naturality are handled by complete Lean proofs.

## No longer needed

The proof does not use `lem-sf-open-base-change-reduction-square`
(`Sheaf.SixFunctors.OpenBaseChangeReductionSquare`) or
`lem-sf-open-tensor-reduction-square` (`Sheaf.SixFunctors.OpenTensorReductionSquare`).
Their short-word statements require finite-type, amplitude, admissibility and
structural-square data absent from this theorem. The open cases follow directly
from the published transpose normalizations and formal adjunction identities.
These two proof dependencies are removed from this node; neither was imported
by the original item. No existing module is withdrawn.

The proof still uses the tensor/adjunction module's generic proved helpers
`comparison_associator`, `mate_compositor_square`, and the unit/counit mate
identities, through a private `import all`. Its `GeneratorReduction.Operations`
word package and its scalar-unit fields are unnecessary.

## Where the brief, the DAG or earlier work was wrong

The planned short-word open lemmas cannot be directly applied to the original
unrestricted ordinary expression statement. The stated tensor/adjunction
selection also has no tensor/pullback generator. The replacement primitive is
precisely this missing geometric square, independently specified by K-flat and
ordinary section normalizations. It is not another expression-generator theorem.

The main node already has a long cycle through the statement dependency of
ordinary-expression reduction and realization assembly. The new primitive avoids
that cycle: it imports only `IntegralSystemCanonicalBridge`, expands its ordinary
tensor coefficient map directly, and its stated dependencies do not reach the
assigned node. No unrelated node was altered to repair the pre-existing cycle.

## New nodes

`lem-sf-canonical-reduction-tensor-pull` records the two-object primitive square,
its K-flat/pure-tensor proof, and the three actual searches. The source is the
first paragraph of current `lem-fix-operation-reduction.proof.md` and Stacks 07A4.
Identity scheme maps and zero inputs use the same pure-tensor computation;
no completeness or boundedness hypothesis is needed.

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
