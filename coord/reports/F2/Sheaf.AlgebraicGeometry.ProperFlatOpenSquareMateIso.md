## What changed

Proved `AlgebraicGeometry.proper_flat_openSquare_mate_isIso` in
`Sheaf.AlgebraicGeometry.ProperFlatOpenSquareMateIso`, preserving its signature and visibility.
Three proved private helpers identify exact restriction with derived pullback, transport
invertibility to the canonical open pullback, and prove full faithfulness of derived open
pushforward. The main proof compares the exact-restriction unit with the canonical restricted
unit, applies the existing proper-flat restriction theorem, and composes this invertible
factor with the inverse conjugate and the open counit.

Added proof imports for the proved source-library restriction-limit instance and
derived fully faithful instances, and Mathlib's left-derived universal property API.
Derived pullback composition is already publicly available through the existing imports. Updated the item's DAG proof, dependency list and proof origin to match.
No definitions, existing signatures, public imports or other modules were changed.

Read Stacks Tags [0E4J](https://stacks.math.columbia.edu/tag/0E4J) and
[0A9L](https://stacks.math.columbia.edu/tag/0A9L). The repository's Stacks source tree is absent;
these primary-source pages give the proper-flat open statement and its three-factor formula.
Tag 0E9S could not be fetched, but no additional compatibility theorem from it is needed.
Searches: LeanFinder for open right-adjoint base change returned underived restriction
adjunctions but no exact derived theorem; Loogle `conjugateEquiv` returned an unknown-identifier
result; msearch grep found the generic conjugate isomorphism instance and the open pullback
scheme isomorphism. Local rg located the existing private restriction/pullback proof in
`RightAdjointMateNewBaseOpen` and proved derived full-faithfulness machinery. Only the private
proof was reused, so there is no import cycle. Import-direction checks passed for the added
library imports.

## Proved and sorry left

Closed the sole hole, `AlgebraicGeometry.proper_flat_openSquare_mate_isIso`
(node `lem-sc-proper-flat-open-square-mate-isiso`). No `sorry` remains in the delivered module;
no new hole or node was added. All three private helpers are fully proved. This is a proof
from existing library declarations, not a decomposition into new statements. Dependencies
may still reach existing library holes; the delivery does not claim that the entire target
import closure is axiom-free.

Local single-file compilation succeeded without warnings, within the 60-second limit.
The delivery dry run also passed its compilation, axiom probe and static preflight;
only the required second reading remains, and nothing was pushed.

## No longer needed

Removed proof imports:

- `Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded`
  (node `lem-pc-derived-direct-image-composition`).
- `Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction`
  (node `lem-pc-restrict-derived-direct-image-open`).

These two dependencies are unnecessary for this theorem: the mate definition already
provides the canonical conjugate, whose invertibility follows from `hβ` by Mathlib's generic
conjugate instance. They were removed from this node's `proof_deps`; this does not assert that
other users of their modules no longer need them. The redundant direct proof import of `Sheaf.AlgebraicGeometry.DerivedPullbackComposition`
added by the first worker was also removed; its node remains used and its module remains
available through `SchemeDerivedBaseChangeMap`. All other original proof dependencies are
retained; the existing tensor-pullback quasi-coherence node is explicitly recorded as well. No unit statement or unit proof step was bypassed. The restriction-limit node from
sec-proper-base-change is used only as a proved source-library tool for exact open restriction.

## Where the brief, the DAG or earlier work was wrong

The original docstring and DAG suggested an identity base-change square for the first clause
of the restriction theorem. The supplied square with `g = W.ι` already gives that clause and
avoids constructing extra right adjoints. The proposed direct-image composition and open
restriction comparisons are unnecessary because the canonical definition exposes the
invertible conjugate directly. No mathematical statement was corrected or disputed.


## Second reading by F2

1. **Interface — pass.** Diffed the sole delivered module and node against the repository.
   The existing theorem signature is byte-for-byte identical; visibility, definitions and
   all public imports are unchanged. The added helpers are private. No change record is
   needed, and there are no adapted modules.
2. **Proof — pass.** Compiled the module locally without warnings (45 seconds). A scratch
   copy with `#print axioms` compiled (47 seconds): all three helpers use only `propext`,
   `Classical.choice`, `Quot.sound`; the main theorem additionally uses `sorryAx` through
   existing dependencies. No delivered declaration contains `sorry`, `axiom`, `unsafe`,
   `opaque`, `implemented_by` or `extern`; the private fully-faithful definition is an
   actual construction. Local choices in proofs use the existing derived universal
   properties and adjunctions and introduce no arbitrary-witness definition.
3. **Split statements — pass (none).** No new public statement, node or hole is added.
   Read all three helper proofs: derived universal-property uniqueness gives the open
   comparison, functoriality transports invertibility through the projection factorization,
   and the proved right-derived fully faithful instances give the open counit. These
   arguments also apply to the empty open and identity morphisms, without boundedness
   assumptions. Independently searched `msearch.py ... grep` for derived full faithfulness,
   restriction isomorphisms and Kan-extension uniqueness, and used `rg` on both library
   roots. The matching open comparison is private in `RightAdjointMateNewBaseOpen`, a user
   of this item, so importing it would form a cycle. No shorter usable public theorem was
   found.
4. **Route and pruning — pass after repair.** Read the restriction theorem and canonical
   mate definition, and checked Stacks Tags [0E4J](https://stacks.math.columbia.edu/tag/0E4J)
   and [0A9L](https://stacks.math.columbia.edu/tag/0A9L). The proof uses the supplied square
   and existing geometric theorem before the inverse conjugate and open counit. Both old
   dependencies omitted from the proof are listed under No longer needed. Removed the
   redundant direct `DerivedPullbackComposition` import; compilation without it succeeded.
   A scratch compile without `PointwiseLeftDerived` failed at
   `Functor.isLeftDerivedFunctor_of_inverts`, confirming that import is needed. The other
   added imports supply restriction limits and derived full-faithfulness instances.
   Read `dag/units/sk-thm-picard-duality.json`: this tool node is not a realized unit
   statement or step; no unit route or realized field was changed or bypassed.
5. **DAG — pass.** The unchanged node statement and Lean record match the unchanged theorem.
   Read the Lean declarations recorded by every proof dependency. The new proof steps
   describe the actual argument, and `proof_deps` is exactly the union of their `uses`.
   The two pruned nodes are absent and the restriction-limit and tensor-QCoh dependencies
   are present. The agent proof origin correctly distinguishes this implementation from
   the cited source argument. There are no new nodes to validate.

Second reading changed only a redundant proof import, the theorem's proof docstring
(replacing the stale identity-square/direct-image-composition description with the actual
supplied-square/base-change argument), and this report. The proof terms were retained.
Final delivery validation is performed below by `deliver3.py`.
