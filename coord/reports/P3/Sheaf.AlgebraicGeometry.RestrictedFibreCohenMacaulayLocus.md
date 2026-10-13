## What changed

Replaced the sole sorry in
`Sheaf.AlgebraicGeometry.RestrictedFibreCohenMacaulayLocus` by a complete Lean
reduction to the new proof-only import
`Sheaf.AlgebraicGeometry.FibreCohenMacaulayLocus`.
The existing theorem's signature and public imports are unchanged.

The private helpers prove preservation of regular-sequence depth under arbitrary
local-ring equivalences, construct the restriction fibre isomorphism, identify
its asFiber point, and transfer the depth-equals-dimension predicate through its
stalk equivalence. The main proof applies unrestricted openness on the restricted
source, proves the exact image equality in both directions, and maps that open
set into X. No Noetherian assumption is needed for the transport argument.
The depth transport proof follows the already-proved private helpers in
`Sheaf.RingTheory.FlatFiberLocalDepth`, without importing its unrelated depth-formula
dependencies. Both delivered modules compile using lcompile.py.

## Proved and sorry left

Closed: `AlgebraicGeometry.isOpen_fibre_depth_eq_ringKrullDim_over_restrict`
(node `lem-sbc-restricted-fibre-cohen-macaulay-locus-open`).
No sorry remains in the assigned module or its private helpers.

Added and still sorry:
`AlgebraicGeometry.isOpen_fibre_depth_eq_ringKrullDim`
(node `lem-sbc-fibre-cohen-macaulay-locus-open`, new module
`Sheaf.AlgebraicGeometry.FibreCohenMacaulayLocus`).
It isolates the unrestricted geometric openness input of Stacks Tag 045U;
it says nothing about restriction, fibre transport, or the image inside X.
The original morphism need only be flat and finitely presented over U, so the
new theorem cannot be applied directly to f. It is applied to f restricted over U
and combined with the proved transport and image argument.
This is a decomposition: one original hole closed, one strictly simpler hole
added, net zero holes. It is not a claim of a sorry-free proof of openness.

Edge cases: the restriction-transport proof assumes neither flatness nor finite
presentation, and no finiteness of depth; it transports the supremum itself.
The image equality works for empty U or X without choosing any point or witness.
For U = top the unrestricted result is the expected special case. The new
openness statement retains both flatness and local finite presentation, exactly
as in Tag 045U (1), (2). No base Noetherianity is added.

## No longer needed

The assigned node no longer needs
`lem-sbc-restricted-fibre-locally-noetherian`, module
`Sheaf.AlgebraicGeometry.RestrictedFibreLocallyNoetherian`.
No existing import was removed: the assigned module did not yet import that
planned dependency, and its public imports are all used by its signature.
The restriction-transport argument proves invariance directly for all local
rings rather than converting to Cohen-Macaulayness via Noetherianity.
Local Noetherianity of the unrestricted fibres is part of the new openness
node's source proof, obtainable directly from finite type over a field.
No other planned node or module is bypassed, and no unit realization is removed.
The existing FlatFiberLocalDepth module and its depth-formula dependencies are
not imported for the copied, fully proved regular-sequence transport argument.

## Where the brief, the DAG or earlier work was wrong

The assigned node's second step invoked Tag 045U openness with no corresponding
Lean declaration or proof dependency. Its only recorded proof dependency,
restricted-fibre local Noetherianity, does not state openness. The new node
supplies precisely that missing unrestricted input, while the original node's
first-step transport and second-step open-image argument are proved in Lean.
The mathematical statement and the unit route are unchanged.

The Stacks source was read at Tags 045U and 00N8 and the linked affine theorem
00RI. LeanSearch returned an Internal Server Error, recorded as unavailable;
LeanFinder, Loogle, and Mathlib/library grep searches found supporting machinery
but no unrestricted Cohen-Macaulay fibre-locus openness theorem. Blueprint search
for Cohen-Macaulay returned no existing blueprint node to reuse.

## New nodes

`lem-sbc-fibre-cohen-macaulay-locus-open` records unrestricted openness for a flat
locally finitely presented morphism in the same depth formulation. Its module is
`lean/Sheaf/AlgebraicGeometry/FibreCohenMacaulayLocus.lean`; its source is Stacks
045U (1), (2), affine input 00RI, and the self-module condition 00N8. The new node
inherits the assigned node's chapter, unit, and blueprint ancestor. The existing
node's proof and proof_deps now describe the actual transport-plus-image route.
There are no statement/interface changes or change records and no adaptations.

## Second reading by P3

Independent second reader, 2026-10-13. Verdict: pass as a decomposition, with
one original hole closed and one new hole added (net zero).

1. Compared the delivered assigned module with the repository using diff and
   an exact signature substring comparison. The existing theorem signature is
   byte-for-byte unchanged; all public imports and definitions are unchanged.
   The new module is the only added public statement. No adaptation or change
   record is required.
2. Compiled both delivered modules in import order through lcompile.py, with
   no errors or warnings. Scanned both sources: the only sorry is the named
   unrestricted openness theorem listed above; there are no forbidden constructs
   or holed definitions. A scratch copy with explicit #print axioms checks showed
   that all four private helpers use only propext, Classical.choice, Quot.sound.
   The assigned theorem and the new openness theorem additionally use sorryAx,
   as expected from the one remaining geometric input. The scratch copy was removed.
3. Read the new statement, its docstring proof and node against Stacks
   [045U](https://stacks.math.columbia.edu/tag/045U),
   [00RI](https://stacks.math.columbia.edu/tag/00RI), and
   [00N8](https://stacks.math.columbia.edu/tag/00N8), and read the actual depth
   definition. The statement is true with the stated flatness and local finite
   presentation hypotheses and without base Noetherianity. Empty sources and
   empty restrictions give the empty locus; fields give depth and dimension zero.
   The restriction transport preserves the entire supremum, including infinite
   depth, without Noetherian hypotheses. Additional msearch queries used
   "fibre local ring has maximal depth" (LeanFinder), '"depth", "IsOpen"'
   (Loogle, no hits), and depth/open or Cohen/locus combinations (grep, no hits),
   plus rg over Mathlib and both library roots. No existing unrestricted openness
   theorem was found; existing ring-equivalence depth helpers are private.
   The new hole isolates the geometric openness step, while the assigned module
   proves fibre/stalk identification, predicate transport and the open-image
   reduction. This is a real decomposition rather than a renamed application.
4. Read the proof from its conclusion backwards. No shorter available theorem
   was found. All public imports support the signatures; the sole new proof
   import is plain import. The old sole proof dependency, restricted-fibre local
   Noetherianity, is fully listed under No longer needed. Read
   dag/units/sk-prop-normal-form.json: its realized fields are unchanged, and no
   unit statement or step is bypassed. The report makes no claim that a globally
   unreachable module has been established by this local pruning.
5. Compared the existing JSON node with the repository: only proof, proof_deps,
   and proof_origin differ. Both nodes' proof_deps equal the union of step uses.
   The recorded transport and open-image steps match the Lean proof. The new node
   has the required source, creation, blueprint, searches and verbatim Lean
   statement fields, and its chapter and unit agree with the assigned node.

Changes by the second reader: appended this audit and recorded additional
searches; no Lean or DAG repair was necessary. The remaining openness theorem
requires the substantial affine Cohen-Macaulay locus argument and was not
closed in this review.
