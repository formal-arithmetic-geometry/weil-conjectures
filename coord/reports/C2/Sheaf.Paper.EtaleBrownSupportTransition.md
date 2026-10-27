## What changed

Filled `AlgebraicGeometry.etaleBrownSupportTransition` in
`Sheaf.Paper.EtaleBrownSupportTransition`, with its signature and existing docstring
unchanged. All additional helpers are private and proved. The proof normalizes
scalar mates from the existing restricted-image transpose equations, transposes
the actual transition squares, obtains the open-extension square by mate pasting,
and composes open and proper squares using naturality and `projection_def`.

Added proof imports `Sheaf.Paper.EtaleBrownEvaluationMate`,
`Sheaf.CategoryTheory.DerivedCategory.AdjunctionMateTranspose`, and
`import all Sheaf.Paper.CoefficientSystemUnboundedComparison` (only its proved
generic mate-whiskering helpers are used). The existing public import stays
unchanged. Updated the item's node proof and proof dependencies to describe these
steps. No shared module, definition, statement, instance or public interface changes.

The proof applies to arbitrary unbounded inputs and to every `n ≤ m`, including
the identity case. It uses only adjunction identities and naturality; no flatness,
boundedness, normalization or coefficient regularity is introduced.

Validation: the complete item passed `lcompile.py` in 25.0 seconds with no
errors or warnings. The theorem signature is textually unchanged. The new
import edges and the added DAG dependency were checked for cycles.

## Proved and sorry left

Closed: `AlgebraicGeometry.etaleBrownSupportTransition`
(node `lem-pur-etale-brown-support-transition`), the item's one original hole.
Added: zero holes. Remaining in the item: zero holes. No split-off statements.

## No longer needed

None. The proof follows all three planned steps and retains the original public
import. No module or node is withdrawn or bypassed. The unbounded-comparison node
is now cited for its existing generic mate-whiskering helpers, rather than
introducing duplicate public lemmas.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was necessary. The mate and transition data in the
stated dependencies suffice; the missing work was their formal normalization and
pasting. No new nodes or statement changes were needed.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
