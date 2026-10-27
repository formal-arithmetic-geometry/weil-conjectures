## What changed

The statement of WeilConjectures.pbc_proper_integral_strict_model_comparison is unchanged.
Its proof now combines the three genuine parts of the existing four-step argument:
ordinary module/derived pullback identification; the independently normalized strict
tower model comparison; completion-map compatibility on flat-term K-flat representatives.
Each part is stated in its own new module, with a source, proof in words and DAG node.

The original module proves the extension of the last equation to arbitrary ambient
derived objects. It packages both sides as natural transformations, applies the proved
fully faithful restriction along integralOperationsGoodLocalization, uses equality on
all good representatives, and evaluates the resulting equality at every L. A proved
private helper, strictUnit_app, identifies the actual strict-unit component with
completedPullbackComparison.
Thus the combination includes a localization argument, not just existential unpacking.

The module privately imports IntegralPullbackIdentificationExists,
IntegralStrictModelMatchingExists and IntegralCompletionMatchingOnGood, and imports
all of IntegralOperationsWellDefined to access its proved private fully-faithful
restriction API. Existing public imports, signatures, definitions and attributes are
preserved. No existing module other than the assigned item changes.
The parent node now records the Lean proof and the three smaller obligations.

Validation: lcompile.py --all compiled all four modules successfully with no errors
or warnings. The final individual times were 50.7 s (good representative equation),
45.9 s (ordinary identification), 52.7 s (model matching), and 53.4 s (the parent).
The parent statement text is unchanged, all Lean lines meet the 100-character bound,
and none of the delivered DAG nodes occurs below itself in the dependency graph.

## Proved and sorry left

Closed the one textual hole of
WeilConjectures.pbc_proper_integral_strict_model_comparison
(lem-weil-pbc-proper-integral-strict-model-comparison).
This is a decomposition, not an unconditional proof or a net reduction in holes:
one upper hole is replaced by three strictly smaller named obligations (net +2).
The assigned module has zero remaining sorry bodies.

The three holes added, each the whole proof of a public theorem in its own module, are:

- WeilConjectures.pbc_integral_pullback_identification_exists
  (lem-weil-pbc-integral-pullback-identification): only the ordinary pullback
  identification and its module-unit/derived-counit normalizations. It contains
  neither a completed-model comparison nor a completion-map equation.
- WeilConjectures.pbc_integral_strict_model_matching_exists
  (lem-weil-pbc-integral-strict-model-matching): given any such a, construct only
  b and its independently pinned strict tower/Roos normalization. It asserts
  no completion-map equation and does not construct a.
- WeilConjectures.pbc_integral_completion_matching_on_good
  (lem-weil-pbc-integral-completion-matching-on-good): given a, b and model matching,
  prove the completion equation on one flat-term K-flat representative. It neither
  constructs a or b nor extends that equation to arbitrary derived objects.

Edge cases were checked in the statements: zero complexes and identity scheme maps
are included, no invertibility of a completion unit is asserted, and no properness,
noetherian, constructibility, completeness or common-base hypotheses are introduced.
The good-representative assertion is universal in the supplied normalized a and b;
its conclusion follows from their pinned unit, counit and both cone coordinates.

## No longer needed

Removed the item's redundant direct proof import
Sheaf.Paper.OrdinaryIntegralPullbackConstruction. Its declarations remain publicly
available through ProperIntegralOrdinaryData and remain needed by the argument.

No mathematical dependency, source-library declaration, unit step or module is pruned.
The parent's old direct proof dependencies are distributed among the new obligations:
four-corners coefficient compatibility and ringed-topoi adjunction/derived pullback
belong to the ordinary-identification step; quotient augmentation and completed
pullback belong to strict tower and completion calculations; exact countable products,
strict Roos comparison and Rlim functoriality belong to the tower comparison and
representative compatibility. Comparison descent remains used for the ordinary unit.
The new direct parent dependencies are the three new nodes, integral-operations
well-definedness (the proved localization API), and completed pullback (the unit formula).
These redistributed dependencies are not claimed as pruned work.

## Where the brief, the DAG or earlier work was wrong

No statement repair was made. General adjunction uniqueness and abstract derived
comparison lemmas found by Mathlib searches do not by themselves supply the required
coefficient square, whole strict tower, or both normalized cone coordinates.

In expanding the parent proof, the actual tower counit must not be justified by
flatness of its quotient terms over the completed ring: those terms need not be flat.
Instead, the completed coefficient inverse-image identification makes module pullback
exact, and its levelwise tower functor is exact. Its derived counit is therefore
invertible on the reduction tower. Reduction itself is computed on the good K-flat P.
The new proof plans use this distinction explicitly.

The unit route is preserved; the assigned node is not itself one of the unit's
realized statement or proof-step nodes. No node or Lean attachment is withdrawn.

## New nodes

lem-weil-pbc-integral-pullback-identification, in
Sheaf.Paper.IntegralPullbackIdentificationExists, isolates original proof step 1.

lem-weil-pbc-integral-strict-model-matching, in
Sheaf.Paper.IntegralStrictModelMatchingExists, isolates original steps 2 and 3
without the completion-map identity.

lem-weil-pbc-integral-completion-matching-on-good, in
Sheaf.Paper.IntegralCompletionMatchingOnGood, isolates original step 4 at the
chain-computable good representatives. The parent proves its ambient extension.

No change record is needed: all existing public interfaces and mathematical
statements are unchanged, and the only other Lean files are new modules.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
