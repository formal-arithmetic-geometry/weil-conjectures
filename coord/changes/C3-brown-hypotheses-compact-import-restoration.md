# CategoryTheory.BrownHypothesesFor

## Reason

Restore the assigned quarantined module at its recorded Lean path. The current
`coord/rework.tsv` row names `quarantine/Sheaf/SixFunctorsBasics/BrownHypotheses.lean`;
`coord/queue.md` lists this one-module cluster after its failed global-build restore.
The archived source no longer compiles: `IsCompactObject` is unknown in the public
bundle and the private assembly lemma. Its old Sheaf import was withdrawn when the
compact-object definition moved to the adopted source module. The current
`def-pc-compact-object` node records that exact upstream definition.

## Old

The live Lean path is absent. The archived module has:

```lean
public import Sheaf.CategoryTheory.CompactObject
```

The imported module is now an empty withdrawn module. Compiling the unchanged archive
reports `Unknown identifier IsCompactObject` at lines 65 and 178 and a consequent
application mismatch at line 190.

## New

Restore the entire archive, replacing exactly that one import with:

```lean
public import WeilConjectures.CategoryTheory.CompactObject
```

No declaration, definition body, theorem signature, proof, or visibility changes.
The compactness notion is the canonical definition already named by its DAG node;
there is no replacement notion or changed target meaning. The existing disputed
`CategoryTheory.brownHypotheses` hole remains exactly as archived. The new source
compiles cleanly through the required `lcompile.py` (3.8 seconds).

## Users

`tools/downstream.py Sheaf.SixFunctorsBasics.BrownHypotheses --allow-missing
--uses brownHypotheses BrownHypothesesFor` reports zero current downstream modules.
Without `--allow-missing` it rejects this absent module. Searching both `lean/` and
`quarantine/` finds the four archived direct importers below. The two theorem calls
are in `LocalizingExceptionalAdjoint`; their arguments and conclusions are preserved.
No archived consumer is withdrawn, restored, or edited by this packet. No target
signature or mathematical definition changes, and no forced adaptation is needed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctorsBasics.BrownHypotheses | C3 | Restore archive with corrected canonical public import. |
| Sheaf.Paper.BrownExceptionalAdjoint | quarantined; not adapted | Same Brown bundle and theorem interface. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | quarantined; not adapted | Both existing theorem calls retain exactly their signatures. |
| Sheaf.Paper.ExceptionalInverseImageExistence | quarantined; not adapted | Same public interface. |
| Sheaf.Paper.MateOpenRestriction | quarantined; not adapted | Same public interface. |

## Status

landed 20261022T002349-L-1920406 2026-10-22 (merge of deliver/C3/Sheaf.SixFunctorsBasics.BrownHypotheses)
