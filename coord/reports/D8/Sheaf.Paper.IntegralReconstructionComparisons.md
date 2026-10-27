## What changed

Proved `AlgebraicGeometry.ProEtale.IntegralReconstructionComparisons.integral_reconstruction_comparisons`
from the existing normalized-equivalence, compactification-limit realization and
tower-gamma statements. The public statement, definitions and structure fields are unchanged.

Private proved helpers verify the common lower bound by exact coefficient evaluation,
apply tower-gamma to an arbitrary recorded compactification, obtain reconstruction data
for the fixed quotient-normalized LimitPresentation, restrict its adjunction, construct
its equivalence, and cancel the actual unit in the morphism reconstruction formula.
The final assembly restricts the supplied tower adjunction with its original ambient
unit/counit; forms b as reduction(realization) followed by the actual reconstruction
counit; forms c as the actual counit; and uses their naturality. All arrows are maps
of entire strict derived towers.

Added proof-only imports `Sheaf.Paper.SfIntegralConstructibleTriangulated` and
`Sheaf.Paper.SfDerivedCompleteLegacyComparison`. The former supplies invariance under
isomorphism (used as a general categorical tool, without replacing the unit route);
the latter connects intrinsic completeness to the normalized-equivalence interface.
Updated the existing node's proof, proof_deps and proof_origin to describe those uses
and the joint detection of zero strict systems. No new nodes, public declarations,
interface changes or consumer adaptations.

## Proved and sorry left

Closed the sole existing hole:
`AlgebraicGeometry.ProEtale.IntegralReconstructionComparisons.integral_reconstruction_comparisons`
(node `lem-sp-integral-reconstruction-comparisons`). Holes closed: 1. Holes added: 0.
No sorry remains in the item; no split-off statement is added.
Validation: lcompile.py compiled the final item cleanly with exit code 0 (55.9 s),
without warnings. Source comparison confirms every existing definition and structure
is unchanged and the main theorem signature is byte-for-byte identical.
The proof uses the published dependency declarations as intended by stage 3; it does
not claim that their transitive proof obligations have all been closed.

## No longer needed

The node's proof no longer needs `det-sp-integral-direct-image-tower` as a proof
dependency: its condensed-coefficient functor has a different source category and
is not used to identify the canonical b. The canonical compactification-limit
comparison and explicit supportCoordinates give that map directly. The node's
statement dependency is retained because it describes the original mathematical
setting; no module is withdrawn and no global unreachability is claimed.

The supplied adjunction is restricted directly, so the existence theorem
`SpTowerGluing.tower_gluing` is not invoked again. Its module and dependency remain:
the supplied support, Charts, Levels, adjunction and normalization route use it.
The tower-shriek-levels, normalized-towers and coefficient-tower modules remain
needed for their actual definitions and exact evaluation API. No existing public
import was removed and no source-library declaration was changed.

## Where the brief, the DAG or earlier work was wrong

The mathematical route works. Three interface details need explicit glue: the
normalization theorem's ambient adjunction need not be definitionally the fixed
LimitPresentation adjunction, so uniqueness of adjoints transports invertibility;
its completeness predicate quantifies an auxiliary FiniteFieldDatum in universe 0,
so the proof uses the same auxiliary finite-field construction as the published
normalization proof; and tower-gamma is phrased for a literal open/proper composite,
so the helper destructs the compactification and substitutes its factorization
before invoking it. None changes a hypothesis or conclusion.

Edge cases: the proof makes no nonemptiness assumption on schemes, selects no
finite evaluations to manufacture arrows, uses all positive levels (including
index 0 = quotient level 1), and treats every morphism in the full subcategories.
The d=0, identity, empty and zero-object cases use exactly the same functorial
construction. No definition takes arbitrary data from an unproved mere existence
statement: witnesses are eliminated inside the theorem proof only.

## Second reading by D8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
