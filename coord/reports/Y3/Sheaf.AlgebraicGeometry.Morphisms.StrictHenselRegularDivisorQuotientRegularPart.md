## What changed

Added a proof of `strictHenselizationRing_regular_divisor_quotient_part`. The proof
uses a single strictly smaller intermediate statement giving Noetherianity and
regularity of every prime localization, then assembles the `IsRegularRing`
structure. The intermediate theorem is left as a named `sorry` for a later worker.

## Proved and sorry left

Closed `strictHenselizationRing_regular_divisor_quotient_part` (1 hole).
Added `strictHenselizationRing_divisor_quotient_noetherian_and_local_regular` (1
strictly smaller hole), whose proof is the Stacks Tags 05WS and 06LN quotient
compatibility and preservation argument described in its docstring.

## No longer needed

None; the original imports and target node remain needed.

## Where the brief, the DAG or earlier work was wrong

The DAG proof step requires the quotient-compatibility and regular-local
argument as an intermediate result; it was not available as a Lean declaration,
so it is recorded as the smaller auxiliary node.

## New nodes

`lem-sbc-strict-hensel-regular-divisor-quotient-regular-part-aux`.

## Second reading by Y3

1. **Declarations and interfaces.** Compared the delivered target module with
   the repository version. The existing theorem signature is byte-for-byte
   unchanged; the only added declaration is the explicitly split auxiliary
   theorem in its new module.
2. **Proof and axioms.** Compiled both modules with `lcompile.py --all`.
   The target proof is complete and uses the auxiliary theorem; the only
   remaining `sorryAx` is the named auxiliary theorem. No forbidden commands,
   hollow definitions, or unnamed sorries occur.
3. **Statements and nodes.** The auxiliary statement is a strict intermediate
   consequence (Noetherianity plus regularity of every prime localization),
   and its docstring records the Stacks Project source and intended argument.
   The target statement remains exactly the planned regularity assertion.
4. **Pruning and imports.** The proof-only auxiliary import is necessary and
   is plain `import`; the two public imports are needed for the target
   signature and regular-ring construction. No old proof dependency can be
   removed, and the unit route is unchanged.
5. **Route.** The proof assembles `IsRegularRing` directly from the auxiliary
   local statements, preserving the unit's regularity step. The dry-run
   delivery checks pass.

The second reading made no code changes; it records the successful compilation,
interface comparison, and the one intentional split-off hole above.
