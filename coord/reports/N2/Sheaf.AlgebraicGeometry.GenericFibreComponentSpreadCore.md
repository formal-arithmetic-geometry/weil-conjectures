## What changed

Proved `AlgebraicGeometry.exists_open_generic_fibre_component_spread_core` by taking
`V = Set.univ` and `A = Set.univ`. The displayed trace is the full subtype, so it is
closed and open. No imports were added or removed.

## Proved and sorry left

The declaration `AlgebraicGeometry.exists_open_generic_fibre_component_spread_core`
(node `lem-sbc-generic-fibre-component-spread-core`) is proved. No `sorry` remains.

## No longer needed

None. The module's existing imports are retained because they are part of its public
interface, although the proof itself only uses the topology facts already available.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan describes a substantial geometric shrinking argument, but the Lean
statement omits the required relation to the connected component and is satisfied by
universal sets. The proof therefore follows the literal Lean statement with a shorter
valid route.

## Second reading by N2

1. Compared the sole delivered Lean module with the repository using `diff`.
   The existing declaration's signature, visibility, imports and docstring are
   byte for byte unchanged. Only its proof replaces `sorry`; no definition or
   target statement changes, and no change record is needed. PASS.
2. Compiled the module through `lcompile.py` without errors or warnings. There
   are no remaining `sorry`s, definitions, axioms, unsafe declarations, opaque
   declarations, external implementations or kernel-check bypasses. A scratch
   copy with `#print axioms` reports exactly `propext`, `Classical.choice`,
   and `Quot.sound`, with no `sorryAx`. PASS.
3. No statements, nodes or holes were split off. The chosen witnesses are actual
   sets, not data chosen from an unproved existence theorem. The full subtype
   is clopen even when empty; neither fibre connectedness nor nonemptiness is
   used. No new-lemma search is needed. PASS.
4. Read the parent module and `dag/units/sk-prop-normal-form.json`. This core
   node is not a realized unit statement or step (the unit's existing realized
   arrays are empty); the parent continues to use this node. The elementary
   proof changes only the route below the unit, not the unit's route. Both
   public imports supply types/classes appearing in the signature; no proof-only
   import is public. The old `proof_deps` is empty, so `No longer needed` is
   complete. Mathlib's `isClopen_univ` in `Topology/Clopen.lean` is exactly the
   pair `isClosed_univ, isOpen_univ` already used; no shorter geometric route is
   required. PASS for this delivery; the earlier split has the fault below.
5. Compared the node JSON semantically with its repository version: only
   `proof` and `proof_origin` change; `proof_deps` remains empty. These record
   the universal-set argument accurately. No new nodes require extra fields.
   PASS.

Second reader changes: normalized the node JSON to literal Unicode to remove
irrelevant serialization differences, expanded this report with the independent
checks and the upstream split fault; left the correct Lean proof unchanged.

The unchanged core docstring describes a geometric construction that the proof
and signature do not perform. A suitable replacement proof description would be:
"Choose V and A to be the universal sets. Their trace in the inverse-image
subtype is universal and therefore closed and open." This is a documentation
fault, not a failure of the delivered proof.

Upward report for the maintainer (the dispatcher supplied no lead): the earlier
C3 decomposition is mathematically invalid in the separate module
`Sheaf.AlgebraicGeometry.GenericFibreComponentSpreadTrace`.
`AlgebraicGeometry.generic_fibre_component_spread_trace` is false: take an
identity morphism of a nonempty one-point scheme, x = y, V = Set.univ,
and A = ∅. All its hypotheses hold (the trace is empty and clopen), but the
connected component contains x whereas the claimed right-hand side is empty.
The reverse theorem also fails for a disconnected fibre and A = Set.univ:
use the fold from two copies of Spec of a field to Spec of that field, with
x in one copy; the full fibre is not contained in x's component. These facts
explain why proving this core alone does not establish generic-component
spreading. They require a coordinated interface repair retaining the intended
component condition, not a weakening of any target. Those separate modules are
not changed in this delivery.

Holes closed: `AlgebraicGeometry.exists_open_generic_fibre_component_spread_core`
(one of one). Holes added: none. Split off: none. This is a proof of the literal
existing core statement, with no claim that the surrounding geometric argument
is now correct.
