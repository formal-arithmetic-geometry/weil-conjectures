## What changed

Added the additive comparison maps theorem as an intermediate interface, then assembled
its mutually inverse maps into the requested additive equivalence.

## Proved and sorry left

Closed `AlgebraicGeometry.Scheme.nonempty_open_h_addEquiv_injective_sections`.
The intermediate theorem `AlgebraicGeometry.Scheme.punctured_flasque_resolution_comparison_maps`
remains sorry and is the sole remaining hole.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The original proof plan requires the acyclic-resolution comparison as a single interface;
it was not available as a library declaration, so it is split into a named intermediate node.

## New nodes

`new-punctured-flasque-resolution-comparison` — additive comparison maps with left and right
inverse laws, used to construct the target equivalence.

## Earlier second reading (a previous round; superseded)

Pending independent second reading.

## Second reading by E1

1. Compared the delivered target module with the repository version. The target
statement and all existing declaration signatures are unchanged byte for byte;
the only target-module changes are the proof and a private import of the new
comparison module. Verdict: pass.

2. Compiled all three sandbox modules with `lcompile.py --all`. The target
proof has no `sorry`; the sole remaining `sorry` is the named intermediate
theorem `AlgebraicGeometry.Scheme.punctured_flasque_resolution_comparison_maps`.
There are no axioms, unsafe declarations, or hollow definitions in the
delivered files. The remaining theorem is intentionally split off with a
source, docstring proof, and DAG node. Verdict: pass subject to that open
interface theorem.

3. Checked the split-off statement against the acyclic-resolution comparison
argument and its edge cases, including arbitrary opens and degree zero. It
asserts exactly mutually inverse additive maps, which is strictly the data
needed to assemble the requested additive equivalence. No existing library or
Mathlib declaration provides this concrete comparison. Verdict: pass.

4. Read the proof route and imports. The target assembles the two maps by the
standard `AddEquiv` structure and retains the unit route through the
comparison interface; no shorter available library theorem was found. The
proof-only comparison import is non-public. Verdict: pass; no imports or
proof-dependency nodes can be pruned.

5. Checked the DAG records against the Lean declarations. The target node's
proof and dependency list name the comparison node, and the new node records
its exact theorem, source, proof steps, and module. The unit metadata is
unchanged. Verdict: pass.

Changed only the report by adding this review record; no Lean statements or
definitions were changed during second reading.
