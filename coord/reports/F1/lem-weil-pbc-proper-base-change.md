Files written:
- `dag/nodes/sec-curve-estimates/lem-weil-pbc-proper-base-change.json`: statement, Mathlib leaf.
- No new nodes.

Attachments:
- None.

WANTED:
- None.

What was checked:
- The item node and its imported proof were read. Its statement is the usual pullback projection form of properness stability under arbitrary base change, with properness interpreted through `def-weil-pbc-scheme-conventions` and hence `def-weil-proper-morphism`.
- I searched the DAG for the statement and for its ingredients. The existing node `lem-weil-pbc-proper-fp-permanence` contains the same base-change clause as part of a broader imported Mathlib leaf; no narrower existing node was found.
- I read Mathlib `Mathlib/AlgebraicGeometry/Morphisms/Proper.lean`, lines 65--84. The `IsProper.isStableUnderBaseChange` instance (lines 72--75) proves stability of the property, and the instance at lines 83--84 states exactly that `Limits.pullback.snd f g` is proper when `f` is proper. This matches `X ×_Y Y' → Y'` after renaming `S := Y`, `Y := Y'`.
- I recorded LeanSearch, LeanFinder, source grep, and local-search checks. The statement is therefore marked `status: "mathlib"` with the direct pullback instance as `mathlib_match`; there are no proof steps or new nodes.
- I checked small edge cases conceptually: identity base change gives `f` itself, and base change along an arbitrary morphism is exactly the pullback projection covered by the instance. No hypothesis beyond properness of `f` is introduced.

## Review by F1
I reviewed the copied node against the imported blueprint paragraph and the Mathlib source. The source's separatedness, finite-type, and universally-closed clauses are precisely the components of Mathlib's `IsProper` class, whose stability-under-base-change instance is used to build the explicit pullback projection instance. The arbitrary morphism `g : Y' → Y` is represented by the second pullback projection, so the object and codomain agree exactly. I verified the Mathlib file and line range, recorded all required search kinds, searched for duplicate DAG statements, and changed the imported node from `status: "imported"` to a Mathlib leaf with no invented proof or dependencies.
