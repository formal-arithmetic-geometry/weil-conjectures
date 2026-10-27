## What changed

Reduced semilinearOpenClosedComplexSequence to three independent ordinary
assembly steps. The item's proof now constructs its exact complex sequence by
applying the ordinary system sequence in each integer degree, proving the zero
composite by component extensionality, applying Mathlib's
HomologicalComplex.shortExact_of_degreewise_shortExact, and converting its
exactness to ComposableArrows exactness. It repeats the construction for the
second coefficient system and applies the separate scalar-comparison statement.

Moved the existing data and proved helper declarations verbatim to
Sheaf.Paper.SemilinearOpenClosedData and publicly re-exported them. Added only
the closed-operation subrecord ClosedData, not a new category or operation.
See coord/changes/H3-semilinear-open-closed-data-extraction.md. There are no
existing Lean importers, so no consumer adaptations are required. The original
theorem's signature and full proof docstring are preserved. Locally marking the
coefficient constructions rings, ringPresheaf and systemRing irreducible in the
final proof avoids repeated unfolding found by profiling; their definitions and
global reducibility attributes are unchanged. No heartbeat or wall-time limit is
raised.

## Proved and sorry left

Closed the original hole in
WeilConjectures.SemilinearSections.OpenClosed.semilinearOpenClosedComplexSequence
(node lem-sp-semilinear-open-closed-complex-sequence) by decomposition, not an
independent sorry-free proof. The complete Lean proof of the passage from
ordinary systems to unbounded complexes is private sequenceData_of_closed.

Added three holes, each in its own new module, each strictly part of the argument:

- WeilConjectures.SemilinearSections.OpenClosed.semilinearClosedSystemPresentation
  (lem-sp-semilinear-closed-system-presentation): closed exact operations and
  normalized evaluation only; no open functor, sequence, complex or scalar change.
- WeilConjectures.SemilinearSections.OpenClosed.semilinearOrdinaryLocalization
  (lem-sp-semilinear-ordinary-localization): an ordinary system short exact
  sequence with both operation data supplied; no complexes or scalar changes.
- WeilConjectures.SemilinearSections.OpenClosed.semilinearLocalizationScalarCompatibility
  (lem-sp-semilinear-localization-scalar-compatibility): normalized scalar
  comparisons with both exact localization data supplied; no existence or
  exactness claim about those supplied data.

Original holes: 1. Closed: 1 by decomposition. Added: 3. Holes left in item: 0;
holes left in delivered files: 3. Net hole reduction is -2. The pre-existing
ordinary open-extension dependency is used as stated even though its construction
still rests on a sorry. No hole is introduced inside a definition.

## No longer needed

The item no longer directly imports the proof-only modules
Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed,
Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction,
Sheaf.Paper.RingedOpenScalarLimitCoherence, or
Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation. Their mathematical
uses are retained in the smaller assembly nodes. The new statements import only
the data their signatures require; their unproved bodies need no proof imports. All three
original tool approvals are consequently removed from the item's tool_uses;
their generic lemmas remain dependencies below the new nodes. No module is
withdrawn and no mathematical dependency is claimed globally pruned.

The item uses the existing ordinary open-extension and coefficient theorems,
closed-system presentation,
ordinary localization and scalar compatibility; its proof_deps and proof steps
now record exactly this route. Former direct dependencies on definitions are
retained through statement dependencies and the new nodes. Mathlib's direct
degreewise assembly avoids adding a separate complex-exactness obligation. The proof also avoids
requesting the unused derived/scalar fields of sequenceSiteOpenExtension by
applying sequenceOpenCoefficients and sequenceOpenOrdinary directly, reusing the
same coefficient comparisons for B and D. The public import of the original
open-extension module is retained for API compatibility.

## Where the brief, the DAG or earlier work was wrong

The DAG called much of the strict-system assembly elementary; it is not supplied
as a Lean interface by the levelwise ringed theorem. The proved open-extension
package does supply the open side, but closed evaluation/mate normalization,
ordinary localization detection and arbitrary coefficient-system compatibility
require the three narrower statements above. Their proofs in words follow the
original seven-step plan and Stacks 09AH/09BM, 03DI/03CY and 09A5.

The blueprint read was literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-lem-sp-tower-bound/sk-lem-sp-tower-bound-operations.proof.md, paragraph (2),
last sentence. The unit sk-lem-sp-tower-bound and its route are preserved.
The Stacks proofs at lemma-ses-associated-to-open and
lemma-closed-immersion-complement-retrocompact-exact were read directly.
Edge cases checked: empty open and closed pieces, zero coefficient rings,
equality/composite transition indices, non-flat Z/4→Z/2 coefficient change,
unbounded complexes, and non-qcqs T. No argument uses a forbidden flatness,
boundedness or qcqs assumption. No existing target statement changes.

Searches: LeanFinder for short exact localization on inverse systems found
only generic sheaf/abelian and Mayer–Vietoris APIs; Loogle found the generic
ShortComplex.ShortExact API; LeanSearch found Mathlib's degreewise short-exact
criterion, used in the proof. Further LeanSearch/LeanFinder queries about closed
evaluation and scalar comparisons found ordinary pushforward/pullback adjunctions
and restriction-of-scalars definitions, not the required strict-system assembly.
The launcher logs record every query. Source searches and blueprint_refs searches
found no existing statement with these precise smaller interfaces.

## New nodes

- def-sp-semilinear-open-closed-data: attaches the extracted, unchanged public
  API and the closed-only subrecord to its own module, avoiding an import cycle.
- lem-sp-semilinear-closed-system-presentation: parent steps 1, 2, 4 and closed
  exactness in step 5, with identity section normalization and actual unit mate.
- lem-sp-semilinear-ordinary-localization: parent step 5 at ordinary objects,
  using evaluation and the levelwise ringed localization theorem.
- lem-sp-semilinear-localization-scalar-compatibility: parent steps 2, 3 and 7,
  with actual section maps and counit/unit equations, given both data.

Change record: coord/changes/H3-semilinear-open-closed-data-extraction.md.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
