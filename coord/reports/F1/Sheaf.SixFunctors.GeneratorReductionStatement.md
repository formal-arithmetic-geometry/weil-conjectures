## What changed

Implemented WeilConjectures.GeneratorReduction.generatorReductionCoherence by
induction and case assembly from its declared dependencies. A proved private
short_word_formulas induction supplies primitive transposes and both open inverse
laws for all endpoint words of length at most three. Tensor and pullback use the
existing quotient augmentation transposes; proper image is its defining counit.
At an open vertex, shortWordIntegralDomain and openReconstructionEffectivity make
the actual open comparison and reconstruction unit invertible.

The nine structural cases use tensorAdjunctionReductionSquares. For the four
open cases the proof applies openBaseChangeReductionSquare,
openTensorReductionSquare, properOpenLambdaReductionSquare and
properOpenInterchangeReductionSquare directly. Their common unrestricted
StructuralSquares hypothesis comes from the recorded structural substitution
lemma applied to the universal short structural-square family. The Lean proof
combines those cases and pairs their Assertion with both independently proved
endpoint primitiveFormulas. The parent DAG proof now records this direct route.
No statement, definition, canonical map, or unit/chapter route changes.

Restored Sheaf.SixFunctors.StructuralReductionWordSubstitution from the existing
node lem-sf-structural-reduction-word-substitution with exactly its recorded
signature. The earlier K4 take-out removed its Lean file but preserved its node
and the parent's plan. The existing node attachment records this restoration.
Its one named hole remains a separate task; this delivery
is a decomposition. It imports the independent OpenInterchangeReductionData,
which owns all predicates its statement needs, rather than the larger theorem
package. Its complete source-based natural-language argument is retained in its
docstring. Checked small cases: identity maps, empty opens, zero inputs, repeated
variables, scalar units, and empty initial input families. Its finite skeleton
uses at most three variables in the same universes.

Moved the proved completionMap_isIso verbatim to the independent module
Sheaf.SixFunctors.ShortWordCompletionIsomorphism. The item publicly re-exports it.
Redirected the tensor-square module's single public parent import to that helper
module; all of its existing signatures, visibility and complete proofs remain
unchanged, including all five uses of completionMap_isIso. Updated both existing
completion-isomorphism nodes' Lean attachments to the moved theorem. The
open-square package changed concurrently and is not included or overwritten.

Change record: coord/changes/F1-generator-reduction-completion-import-cycle.md,
including the complete consumer table. LeanFinder, Loogle and Mathlib grep were
searched with msearch.py; local source and the current blueprint were also read.
No generic Mathlib statement provides these specified coefficient squares.
The current four forward open-square statements give the shorter final route.

Validation: lcompile.py compiled the independent completion helper, restored
substitution theorem and adapted complete tensor proof without warnings. After
adding the explicit StructuralSquares type annotation in the final assembly,
the parent compiled cleanly with exit 0 in 18.5 seconds against those sandbox
modules and the five current unpublished data/forward-square dependencies in
the compile service's private overlay. The source import closure has no path
back to the parent; compared with using the larger open package, it omits
OpenInterchangeReductionSquares and CanonicalOpenReductionIsIso. The delivery
tool also passed the complete-set compile and required axiom probes. Its first
preflight requested the existing substitution node record in the packet; that
record is now included with its restoration metadata. The service enforces the 60-second Lean limit; its displayed job times
also include cache/setup overhead.

## Proved and sorry left

Closed the one original item hole:
WeilConjectures.GeneratorReduction.generatorReductionCoherence
(lem-sf-generator-reduction-coherence), by a complete Lean proof from the stated
lemmas. The new private short_word_formulas is fully proved.
primitiveReductionTranspose remains proved. completionMap_isIso remains proved,
with its original signature, docstring and proof, in its independent module.

Restored one split-off hole:
WeilConjectures.OpenInterchangeReduction.structuralReductionWordSubstitution
(lem-sf-structural-reduction-word-substitution), exactly `:= by sorry` in its own
module. This is strictly the structural-word substitution step: it assumes all
short structural squares and asserts their extension to substituted words. It
asserts none of the four open squares or endpoint primitive formulas. No new
node or duplicate theorem is introduced.

The tensor-square module and independent completion-helper module have zero
holes. The original item goes from one hole to zero. Across delivered modules,
one original hole becomes one restored split-lemma hole: net zero. This is a
decomposition with one upper hole closed and one lower hole restored. Existing
holes in imported dependencies remain separate items, including the four
forward open-square statements. Actual target-closure counts depend on the
project ledger after proof imports. No hole is added to any definition or
private theorem.

## No longer needed

The final proof does not need:

- Sheaf.SixFunctors.OpenInterchangeReductionSquares and its node
  lem-sf-open-interchange-reduction-squares. Its four forward case lemmas suffice;
  its extra inverse and naturality conclusions are unused.
- Sheaf.SixFunctors.CanonicalOpenReductionIsIso and its node
  lem-sf-canonical-open-reduction-is-iso, reached only through that larger package
  in the abandoned route. It is unnecessary for these forward coefficient squares.

Both source modules and their existing declarations remain in the library; this
is pruning of this parent's proof dependencies, not a withdrawal or a claim that
no other parent could use them. The parent node replaces the larger package edge
by the four actual forward-square nodes. The structural-substitution statement
imports only OpenInterchangeReductionData, without importing the theorem package.

The item's direct private PrimitiveCompletionEffectivity import is no longer
needed there after moving completionMap_isIso; the helper module retains that
import. Tensor no longer imports the parent: ShortWordCompletionIsomorphism
supplies both the data and the proved helper it uses. All other mathematical
steps of the recorded route are retained. primitiveReductionTranspose is
preserved; its length-one restriction cannot itself provide the length-three
endpoint formulas, so the private induction uses its underlying transposes.

## Where the brief, the DAG or earlier work was wrong

The DAG records StructuralReductionWordSubstitution as an existing Lean module,
but its file is absent following the earlier K4 take-out, with no quarantine row
in coord/rework.tsv. Its recorded statement is restored faithfully. The extension
to all structural words is needed for the internal length-four terms of the
proper/open factorization; the short tensor/adjunction theorem alone does not
supply it.

The K4 import repair redirected the tensor module to data alone and lost
completionMap_isIso at five uses; the recorded global-build errors report that
unknown identifier. This delivery extracts and re-exports the complete proved
helper, preserving the full tensor proof.

OpenInterchangeReductionSquares changed concurrently during this session. Its
current proof reduces to four forward lemmas and then adds inverse and
naturality clauses. Its compiled predecessor still brought in the parent when
used by our first packet without an overlay. Directly applying the four
forward lemmas is sufficient and avoids this unnecessary package dependency.
The other group's open-square work is preserved unchanged.

TensorAdjunctionReductionSquares is currently unclaimed. Its sole changed line
is the public import: the original produces the cycle
GeneratorReductionStatement -> TensorAdjunctionReductionSquares ->
GeneratorReductionStatement, reproduced by lcompile.py in
scratchpad/original-cycle. The independent helper resolves this cycle while
preserving every existing tensor declaration and proof. No held module is
adapted, and no source-library file is changed.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
