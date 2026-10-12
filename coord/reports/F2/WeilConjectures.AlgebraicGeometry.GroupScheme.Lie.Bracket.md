## What changed

Proved `toMixed_bijective`, `commutator_mem_mixedPoints`, `infPointsMap_infBracket`,
and `infBracket_mem_range_infPointsMap`. The inverse extracts the constant and mixed
coefficients, respects restriction maps, is local on stalks, and lies over the base.
Cancellation and group homomorphism laws prove commutator membership and functoriality.
All original signatures and definitions are unchanged. The second reader changed the
presheaf-differentials import from public to proof-only.

## Proved and sorry left

Four of nine original sorry occurrences are closed, in the four theorems above.
Unchanged sorries: `instance instance : LieRing (Lie G)`
(`AlgebraicGeometry.GrpObj.instLieRingLie`: fields `add_lie`, `lie_add`, `lie_self`,
`leibniz_lie`) and `instance instance : LieAlgebra Γ(S, ⊤) (Lie G)`
(`AlgebraicGeometry.GrpObj.instLieAlgebraLie`: field `lie_smul`). Their blueprint reference
is `sk-d-tangent`; ancestor `def-wf-lie-algebra-derivation` records the open declarations.
No new sorry was introduced.

## No longer needed

None. No imported module was removed, no existing node is bypassed, and the unresolved
Lie-ring route remains. The four completed proofs need no Sheaf statement imports.

## Where the brief, the DAG or earlier work was wrong

No node has this module as its principal `lean.module`; search hits are open-declaration
audit entries of ancestors, whose proof routes remain unchanged. The existing matrix-group
Sheaf statements assume a field and a matrix embedding and do not cover arbitrary bases.

The preflight requires a completed second reading section, whereas the worker brief reserves
that section for the independent second reader. The worker has not supplied that section.


## Second reading by F2

1. Compared the full module against the repository with `diff` and the declaration
   parser: no existing statement signature or definition changed, no new sorry.
   The only import change is the proof-only downgrade described below. The public-import removal is recorded in
   `coord/changes/bracket-proof-only-differentials-import.md`.
2. Read all four proofs and their private helpers. Local compilation passed without
   warnings. There is no forbidden declaration or attribute, and no sorry in a
   definition. The five unchanged proof holes are exactly the four fields of
   `AlgebraicGeometry.GrpObj.instLieRingLie` and the `lie_smul` field of
   `AlgebraicGeometry.GrpObj.instLieAlgebraLie`, already listed above. Explicit
   scratch-copy `#print axioms` checks cover the four completed theorems and the
   two remaining instances; the delivery additionally probes all declarations.
3. No new split-off statement or node exists. Checked coefficient extraction:
   eliminating both pure coefficients makes the mixed coefficient obey the
   Leibniz rule, with no division or nonzero-ring assumption. Thus zero rings,
   characteristic two, and identity points cause no exceptional case. Restriction
   compatibility and locality are proved, rather than assumed. Independent
   LeanFinder/Loogle searches for the dual-number product embedding and an `rg`
   search of the library found no existing scheme-level inverse replacing this
   construction. The three other proofs use group homomorphism laws and mono
   cancellation directly.
4. The route starts with the target holes and uses coefficient extraction and
   elementary group laws; it does not move a target into a renamed open theorem.
   Reviewed all three imports: Lie.Basic supplies the Lie structures;
   InfPointsEquiv supplies the signature's objects; the local differentials
   extension supplies only proof lemmas. Changed that last import to plain
   `import`, as required. No dependency module is removed or bypassed, so the
   No longer needed list remains empty. Inspected `dag/units/sk-d-tangent.json`:
   its definition unit has no proof steps, and its existing realized fields are
   untouched.
5. Searched all DAG node principal Lean records: none has this module as its
   principal module. The hits are ancestor audit records, including
   `def-wf-lie-algebra-derivation`, with the unchanged open Lie instances.
   Their proof/proof_deps/proof_origin routes are not replaced by these local
   proofs, so no node edits are appropriate. No new nodes. The import change record lists all 186 downstream modules;
   none uses either lemma from the removed reexport.

Changes by the second reader: made the local presheaf-differentials import
proof-only, removed two surplus blank lines, wrote `coord/changes/bracket-proof-only-differentials-import.md`, and completed
this review report.
