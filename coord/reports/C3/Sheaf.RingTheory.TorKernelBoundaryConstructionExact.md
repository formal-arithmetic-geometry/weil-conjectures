## What changed

The unchanged statement `CategoryTheory.tor_kernel_boundary_construction_exact`
is reduced by conjunction introduction to two strict component assertions in
new modules `Sheaf.RingTheory.TorKernelBoundaryConstructionExactLeft` and
`Sheaf.RingTheory.TorKernelBoundaryConstructionExactRight`. Both imports are
proof-only. The existing public construction import is needed by the signature.
No definition or existing signature changes, and no change record is required.
The unchanged construction copy has been removed from the delivery.

## Proved and sorry left

Hole closed in the item: `CategoryTheory.tor_kernel_boundary_construction_exact`
(node `lem-sc-p1-tor-kernel-boundary-construction-exact`). Its proof assembles the
two component lemmas; it still depends on `sorryAx` through them.

Holes added, each in its own new module:
- `CategoryTheory.tor_kernel_boundary_construction_exact_left`
  (node `lem-sc-p1-tor-kernel-boundary-construction-exact-left`).
- `CategoryTheory.tor_kernel_boundary_construction_exact_right`
  (node `lem-sc-p1-tor-kernel-boundary-construction-exact-right`).

This is a decomposition, not a completed mathematical proof: one hole closed,
two added, net -1 hole reduction in the item import closure. Neither new hole
was closed during second reading. There are no other delivered holes or data
chosen from unproved existence statements. All three declarations' axiom checks
show only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.

## No longer needed

No imports or modules are pruned. Each old parent proof dependency is no longer
used directly by its conjunction proof, but remains part of both components'
independent proof plans:
- `def-sc-p1-tor-kernel-boundary-construction`;
- `lem-weil-pbc-free-resolution-ses-split`;
- `lem-weil-pbc-complex-ses-homology-long-exact`;
- `lem-weil-pbc-tensor-right-exact`;
- `lem-weil-pbc-tor-map-via-resolution-lift`.

The parent proof_deps now names exactly the two component nodes. Its signature
still needs the construction module. No old dependency is mathematically
rendered unnecessary by this decomposition.

## Where the brief, the DAG or earlier work was wrong

The initial report called the item proved without acknowledging the increase
from one hole to two. The initial new nodes incorrectly depended on their parent,
creating circular proof plans. Both faults have been corrected.

The original written comparison also asserted equality with the snake boundary
without checking its sign. For lifts b0 and b1 of the comparison, the factor
of dB b1 - b0 dP through A0 augments to minus the kernel restriction of e0 dP.
On tensor cycles it computes the snake boundary, hence that convention gives
the negative of the explicit boundary. Exactness survives this sign because
negation preserves kernel and image. The docstrings now explain this argument.
The exactness statements and the constructed map have not changed.

The relevant sources were checked at
[Stacks 00M0](https://stacks.math.columbia.edu/tag/00M0),
[Stacks 00LZ](https://stacks.math.columbia.edu/tag/00LZ), and
[Stacks 0111](https://stacks.math.columbia.edu/tag/0111).
Local literature source files named in the inherited records are absent on this
machine; the source pages provide the cited results.

## New nodes

`lem-sc-p1-tor-kernel-boundary-construction-exact-left` states only exactness
at Tor, with the original hypotheses and boundary. Its complete written proof
uses split free resolutions, homology exactness, resolution comparison, and
the explicit cycle comparison. It does not depend on the parent theorem.

`lem-sc-p1-tor-kernel-boundary-construction-exact-right` states only exactness
at the kernel tensor, using the same independent construction and comparison,
but the other adjacent position of the homology exact sequence. It does not
depend on the parent theorem. These are strict conjuncts, not renamed copies
of the whole parent assertion. No change records or forced adaptations.

## Second reading by C3

1. Compared every existing delivered module against the repository. The existing
   theorem signature is byte-for-byte unchanged; only its proof, proof imports,
   and explanatory docstring differ. The construction copy was identical and
   removed. No existing definition, visibility, hypothesis, or conclusion changes.
2. Compiled the delivered modules in import order with lcompile.py. Scratch
   copies with explicit #print axioms for all three declarations show only
   the permitted standard axioms and sorryAx from the two listed open lemmas.
   No axiom, unsafe, opaque, implemented_by, extern, or holed definition occurs.
3. Read both split assertions and their complete written proofs. Each is exactly
   one required conjunct. Zero M gives zero tensors and Tor; the identity
   surjection has zero kernel and identity Tor map; F -> 0 has zero Tor source
   and identity kernel inclusion. These cases satisfy both assertions. General
   F need not be projective: the chosen resolutions supply projectivity.
   Independent leanfinder, loogle and grep searches, plus local library searches,
   found homology exactness lemmas and TorLongExactFirstVariable, but no theorem
   identifying its existential boundary with this particular constructed map.
   They cannot close these comparison obligations by direct application.
4. Checked the top-down reduction, each import's role, old proof dependencies,
   and dag/units/sk-thm-picard-duality.json. The unit's realized entries do not
   name this auxiliary node; they are unchanged. Both components retain the
   original horseshoe route. No module is pruned. This is honestly reported as
   decomposition with net -1 hole reduction, rather than a proof of exactness.
5. Corrected parent proof/proof_deps/proof_origin to match conjunction introduction;
   corrected both new proof plans to remove circular parent dependencies and
   restore their actual horseshoe prerequisites. Verified new node metadata,
   exact Lean statements, source, chapter, unit, creation and search records.

Second reading changed: repaired circular DAG dependencies and missing parent
proof metadata; expanded both incomplete proof docstrings; corrected the snake
comparison sign; corrected progress accounting and pruning report; removed
unchanged construction and redundant misplaced node copies. No Lean statement
or definition was changed.
