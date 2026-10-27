## What changed

Replaced the sole `sorry` in `CategoryTheory.ringCechCoordinates_tensor_step` by a
complete reduction to two independent parts of its stated proof. The original
signature, hypotheses, public imports and augmentation stay verbatim.

`Sheaf.Paper.RingLocalizationTensorBlocks` states the evaluated two-row tensor
matrix for any nonnegative augmented complex K and any single element s. It has
no generating list and assumes or constructs no ordered coordinates.

`Sheaf.Paper.RingCechAlgebraicConeCoordinates` states the ordered-subset identity
for ordinary modules: the degree-q term is M(q+1) times (A[1/f(0)] tensor M(q)).
It has no sheaf, categorical tensor, complex totalization or augmentation. Its
auxiliary `ringCechTailTerm` is an explicit recursion into `ModuleCat`; it selects
no witnesses and has no proof holes.

The assigned module constructs the tail degreewise equivalences, conjugates the
tail differential and verifies both of the algebraic lemma's hypotheses from
hd₀ and hd. It proves tensor naturality of this conjugation by tensor induction,
composes the three coordinate equivalences, and uses the actual tensor matrix
to obtain the two requested differential identities. The first identity also
uses ha and the evaluated tensor augmentation. This is a decomposition of the
categorical and algebraic calculations, not a renamed copy of the original
existential or a new assumption of the original conclusion.

The sources read were algebraization.tex, lemma-map-twice-localize (0996),
lemma-all-rings (099D), and more-algebra.tex, section-alternating-cech. The new
proofs in words elaborate the assigned node's steps 1–3; the source does not
already supply Lean-ready versions of either interface. Library and Mathlib
searches found generic tensor-total, finite-product tensor and localization
APIs, but no theorem supplying either complete interface. The current unit's
realized statement and steps are preserved.

Validation: final `lcompile.py --all` compiled all three modules without errors
or warnings. The assigned module took 42.8 seconds, below the unchanged
60-second file limit. Debug profiling options were removed. A direct textual
check confirms the original theorem signature is byte-for-byte unchanged; the
new node Lean statements match their files and all Lean lines fit 100 columns.

## Proved and sorry left

Original hole closed by decomposition:
`CategoryTheory.ringCechCoordinates_tensor_step`
(`lem-weil-pbc-ring-cech-coordinate-tensor-step`). There are no holes left in the
assigned module.

Two holes added, each the whole proof of its named public theorem:

- `CategoryTheory.ringLocalizationTensor_blocks`
  (`lem-weil-pbc-ring-localization-tensor-blocks`).
- `CategoryTheory.ringCechAlgebraicCone_coordinates`
  (`lem-weil-pbc-ring-cech-algebraic-cone-coordinates`).

Thus this delivery closes one hole and adds two; it is a decomposition, not a
net reduction in the sorry count. No new definition contains `sorry`, and no
data is chosen from an unproved existence statement in a definition.

Edge cases checked mathematically: with r=0 the first product factor is zero,
the degree-one second factor is S tensor A=S, and all higher terms vanish.
With f(0)=0 both S and every full coordinate containing zero are zero; coordinates
avoiding zero remain the tail coordinates. Repeated generators require no
cancellation. In the zero ring all terms vanish. For the tensor-block statement,
the only discarded degree-zero row is S tensor K^(-1), which vanishes by hneg.
The minus sign in row one agrees with first-factor degree one in the tensor
convention and with the one-position shift of the nonzero-deletion faces.

## No longer needed

No modules or imports are withdrawn. Both original public imports remain needed
by the assigned statement. The original direct proof dependency
`lem-weil-pbc-localization-base-change` moves to the algebraic-cone lemma and is
still needed there; this is not global pruning. The definition dependencies of
the original node remain in stmt_deps and occur in the tensor-block node. The
assigned node's proof_deps and proof steps now cite the two actual intermediates.
No unit, source-library declaration, quarantined module or parent is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original proof_deps contain the construction definitions and localization
base change, but none states the evaluated totalization matrix or the ordered
subset/sign identification. Those are distinct nontrivial calculations, now
stated separately. The earlier five decompositions of the obligation are not
repeated: neither new statement carries both the sheaf-totalization and ordered
localization coordinate obligations.

`blueprint_refs.py ancestor` returns None for this inherited new-node ancestry;
the new records preserve the null ancestor and explicitly name the assigned
proof steps and inherited via chain. Searching the blueprint for localization
tensor found no duplicate. No statement was found false, and no existing
statement or definition was changed.

## New nodes

`lem-weil-pbc-ring-localization-tensor-blocks`, in
`Sheaf.Paper.RingLocalizationTensorBlocks`, is the general evaluated tensor
matrix and augmentation calculation of assigned steps 1 and 3. It separates
all sheaf and total-coproduct issues from ordered localization combinatorics.

`lem-weil-pbc-ring-cech-algebraic-cone-coordinates`, in
`Sheaf.Paper.RingCechAlgebraicConeCoordinates`, is the ordinary module calculation
of assigned steps 2 and 3. It distributes localization over finite products,
partitions increasing subsets by zero membership and verifies the signs. Both
nodes carry their full statements, source places, proofs in words, Lean records
and actual LeanSearch/LeanFinder/grep search results. No change records are
needed because no existing interface changes.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
