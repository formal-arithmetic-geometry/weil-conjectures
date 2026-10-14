## What changed

Proved `perfect_hom_open_restricted_core_exists` by a strict two-part decomposition. Added
`PerfectHomOpenRestrictedEquivFields` for the restricted Hom equivalences and their testing-object
naturality, and `perfect_hom_open_restricted_maps_exists` for assembling transition and cocone
compatibility. The two component theorems remain explicit named `sorry` obligations.

## Proved and sorry left

Closed `perfect_hom_open_restricted_core_exists`. Added `perfect_hom_open_restricted_equiv_fields_exists`
and `perfect_hom_open_restricted_maps_exists`, each with its own DAG node.

## No longer needed

None; both original proof-dependency imports remain semantically relevant.

## Where the brief, the DAG or earlier work was wrong

The one-step DAG proof plan omitted the separate construction of Hom equivalences and the separate
compatibility of transition and cocone maps. These are recorded as strict intermediate statements.

## New nodes

`new-perfect-hom-open-restricted-equiv-fields` and `new-perfect-hom-open-restricted-maps`.

## Earlier second reading (a previous round; superseded)

The decomposition was checked against the unchanged target signature. The first new theorem contains
only the restricted Hom equivalences and testing-object naturality; the second adds only transition,
cocone, and QCoh packaging. Both are strictly smaller than the target and have matching node records.

## Second reading by R2

1. **Statements and signatures.** Compared the delivered core module with the repository version.
The target declaration `perfect_hom_open_restricted_core_exists` has the identical signature; its
proof only invokes the two newly named component results. The new structures and theorem signatures
are internally consistent with their uses.

2. **Proof checks.** Compiled all three sandbox modules with `lcompile.py --all`. There are no
anonymous `sorry`s, axioms, unsafe declarations, or hollow definitions. The two explicitly named
component theorems are the only remaining `sorry` obligations and are listed in the report above.

3. **New statements.** Checked that `PerfectHomOpenRestrictedEquivFields` contains only the Hom
equivalences and their testing-object naturality, while `perfect_hom_open_restricted_maps_exists`
contains only assembly of transition, cocone, and QCoh fields. Each is a strict sub-obligation of
the target and has a corresponding node; no existing library declaration duplicates them.

4. **Pruning and imports.** The proof uses both original public imports and the proof-only import of
`PerfectHomOpenRestrictedMaps`; no import can be removed without losing a declaration used in the
types or proof. The unit route remains the two component constructions followed by the core result.

5. **DAG agreement.** The node records and declarations agree on names, modules, statements, and
proof dependencies. The new nodes are marked split and carry their literature sources and proof
origins.

Changed only this report section during second reading; no Lean statement or proof was altered.
