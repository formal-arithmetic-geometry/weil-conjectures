## What changed

Restored `lean/Sheaf/AlgebraicGeometry/ProperOpenAlphaPasting.lean` in the
sandbox from the current quarantine archive, preserving every declaration,
its signatures, and its proof dependencies. Reapplied the returned packet's
removal of unused `Functor.map_id` rewrites. Simplified each theorem's three
termwise equality transports to `all_goals rw [hm]`; the module-sheaf identity
and derived-pasting argument remain unchanged.

Preserved main's comments explaining the two distinct restriction identities.
No other existing module or node is delivered. The three `import all` lines
remain necessary because the derived-pasting component lemmas are private.

## Proved and sorry left

Zero holes closed and zero holes added. The restored module contains zero
`sorry`s. The three existing complete proofs remain:

- `AlgebraicGeometry.ProEtale.StrictTower.alpha_vertical_beforeDerivation`
- `AlgebraicGeometry.ProEtale.StrictTower.alpha_horizontal_beforeDerivation`
- `AlgebraicGeometry.ProEtale.StrictTower.alpha_baseChange_beforeDerivation`

They realize `lem-cbc-proper-open-alpha-pasting`. This repair claims no new
mathematical proof or decomposition.

## No longer needed

No imports, nodes, or modules are pruned. Removed only unused simplification
rules and repetitive equality-transport proof terms. Unchanged dependency
source copies used for compilation were removed from the delivery sandbox.
The quarantine archive and the node's Lean attachment are preserved.

## Where the brief, the DAG or earlier work was wrong

Addressed the returned head `b337f86b89c`: its old base preceded quarantine.
Read the current rework row, return, claim, archive, and complete build error.
A4 already held the item claim; it was renewed for this repair.

The actual global-build failure was a collision between different declarations
named `singleAlpha_restriction` in `ProperOpenAlphaRestriction` and
`SingleAlphaRestrictionNormalization`. Main's maintenance commit
`da43a480b5f` renamed the latter to `singleAlpha_restriction_normalized` and
adapted its vertical callers. Those current sources must be used together;
a check against older compiled dependencies does not validate the combined
imports. This session does not overwrite that repair or redeclare either
restriction theorem.

After the return was written, commit `8275ec6796d` automatically restored the
module and its importer cluster on main. Consequently the new packet updates
the restored source, preserving the archive's import comments and incorporating
the returned cleanup plus the equality-transport simplification. It is not an
unchanged re-push of the old packet.

Validation: copied the current sources of
`ProperOpenCompositeTransformation`, `SingleAlphaRestrictionNormalization`,
`ProperOpenAlphaVerticalModules`, `ProperOpenAlphaRestriction`, and
`ProperOpenAlphaHorizontalModules` into the sandbox. `lcompile.py --all`
compiled that set and the restored item in dependency order with exit code 0;
the item took 9.1 seconds. All five unchanged dependency copies were checked
byte-for-byte against main and removed afterward. No signatures, public
imports, instances, or attributes were changed, so no consumer adaptations
are required. The proof route and DAG dependencies are unchanged.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
