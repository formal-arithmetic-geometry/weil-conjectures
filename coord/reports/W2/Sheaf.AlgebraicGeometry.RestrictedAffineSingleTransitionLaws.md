## What changed

Reduced `AlgebraicGeometry.Etale.restrictedAffineSingleTransition_laws` to its two
independent calculations. The target signature and docstring remain exactly as in
the repository. It now pairs the identity law and the composition law, imported
only for the proof. Each new module contains one public theorem. The identity
statement drops the coefficient composition hypothesis; the composition statement
drops the coefficient identity hypothesis. These are strictly separate components
of the original conjunction, not renamed copies of the target.

The earlier complete draft is preserved under `scratchpad/BeforeRepair.lean` for
future workers. Its generic unit and square-composition prefixes compiled, but its
concrete specialization and kernel checking did not complete within the file limit.
This delivery records the unfinished mathematical subarguments as independent
items rather than claiming the draft as a verified proof.

## Proved and sorry left

Closed upper hole by decomposition:
`AlgebraicGeometry.Etale.restrictedAffineSingleTransition_laws`.
There are no textual holes in the original module.

Added two holes, each the whole proof of a public theorem:

- `AlgebraicGeometry.Etale.restrictedAffineSingleTransition_identity_law`
  (`lem-sbc-restricted-affine-single-identity-law`).
- `AlgebraicGeometry.Etale.restrictedAffineSingleTransition_composition_law`
  (`lem-sbc-restricted-affine-single-composition-law`).

Validation: `lcompile.py --all` compiled the composition module, identity module,
and target module in 19.3, 3.8, and 6.0 seconds respectively. The required
`deliver3.py W2 Sheaf.AlgebraicGeometry.RestrictedAffineSingleTransitionLaws --no-push`
printed `OK (dry run)`; it passed compilation and preflight
except for the independent second reading, which belongs to the next worker.
Nothing was pushed.

This is a decomposition, not a net proof: one hole closed, two added, net -1.
Neither new theorem assumes the other coefficient law. Both are true for zero
sheaves and empty schemes; empty index types have no equations to check. Identity
arrows and composable identities are covered by the same unit/pasting calculations.
No object is chosen from an unproved existence theorem.

## No longer needed

No original imports, modules, or nodes are pruned. The unverified draft's proof-only
imports `WeilConjectures.SixFunctors.BaseChange.Pasting` and
`WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Identity` are absent from the
final target module: its proof uses the two separate law declarations. These
coherence tools remain pertinent to the two new items, so no claim is made that
they leave the targets' transitive closure. The unchanged sandbox copy of
`RestrictedAffineSingleMaps` from the previous attempt was removed from the delivery.

## Where the brief, the DAG or earlier work was wrong

The previous report described a draft with no holes but no successful full check.
It was not a verified proof. In this repair the original statement compiled, and
separate generic helper prefixes compiled; full concrete drafts repeatedly reached
the 60-second limit. Heartbeat diagnostics identified kernel conversion in the unit
calculation and transition formula, and inference at mapped complex morphisms.
Local transparency controls caused additional failures of implicit conversions;
explicit source/target arguments and a generic complex-composition calculation were
also tested. None established a complete verified proof of both concrete laws.
A final direct degreewise identity attempt reached a type mismatch between
`restrictedAffineDiagram.map` and `rawAffineRestrictedMap`; explicit normalization
of that mismatch timed out. These scratch attempts do not change the delivered
statements or its two remaining holes.
The decomposition follows the existing identity and composition steps; no unit
route, statement, definition, visibility, or public import of an existing module
changes.

## New nodes

`lem-sbc-restricted-affine-single-identity-law` records the identity calculation
using the pullback identity square, coefficient unit, and degree-zero evaluation.
Its module is `Sheaf.AlgebraicGeometry.RestrictedAffineSingleIdentityLaw`.

`lem-sbc-restricted-affine-single-composition-law` records the composition
calculation using horizontal square pasting, coefficient composition, naturality,
and degree-zero evaluation. Its module is
`Sheaf.AlgebraicGeometry.RestrictedAffineSingleCompositionLaw`.

No change records are needed: existing public signatures and definitions are unchanged.

## Second reading by W2

1. I compared the delivered target module with the repository version. The target
signature and docstring are byte-for-byte unchanged; only its proof imports the two
new component modules and pairs their results.

2. I compiled the identity module, composition module, and target module with
`lcompile.py`. All compile successfully. The target has no textual `sorry`; the two
component theorem proofs remain the explicitly named split-off holes. No definitions,
axioms, unsafe declarations, or forbidden implementation mechanisms were added.

3. The two new statements are the identity and composition conjuncts of the original
statement, respectively. Each omits only the independent coefficient law unused by
that conjunct, so neither is a renamed copy of the target and both are strictly
simpler reductions. Their docstrings state the intended categorical calculations and
edge cases, and each has a matching DAG node.

4. The target proof uses exactly the two split-off declarations. The component modules
retain the public import required by their statement (`RestrictedAffineSingleMaps`);
the target's component imports are proof-only imports. No removable proof dependency
was found, and no old node or module is pruned.

5. The unit route is preserved: the target remains the realized unit-level node, while
the two component nodes record the identity and composition steps separately. The
delivery dry run passed all checks other than this report section, which is now fixed.

Changed in this second reading: added this review record only; no Lean declarations,
statements, definitions, imports, or DAG content were changed.
