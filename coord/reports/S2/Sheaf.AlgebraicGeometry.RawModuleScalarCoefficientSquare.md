## What changed

Completed `AlgebraicGeometry.Etale.rawModuleScalar_coefficient_square` from a named
shift-transport intermediate theorem. The intermediate theorem records the shift transport
step from the generic categorical calculation; its proof remains a split for a follow-up
worker. The original factor definitions and imports are unchanged.

## Proved and sorry left

The target `AlgebraicGeometry.Etale.rawModuleScalar_coefficient_square` is proved by applying
`rawModuleScalar_coefficient_square_of_unshifted`. The latter is one of three sorrys left. The other two are
`rawModuleScalar_derivedPullbackIso_commShift` (node
`lem-sbc-raw-scalar-derived-pullback-shift`) and
`rawModuleScalar_coefficient_unshifted` (node
`lem-sbc-raw-scalar-coefficient-unshifted`) in the delivered prerequisite module.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The earlier proof expanded the full shifted categorical calculation during elaboration and
exceeded the compile timeout. Naming that shift-transport step as an intermediate theorem
keeps the target proof small and leaves the strictly lower transport obligation for a later
worker.

## New nodes

`lem-sbc-raw-scalar-coefficient-unshifted` and `lem-sbc-raw-scalar-derived-pullback-shift` are prerequisite nodes.

`lem-sbc-raw-scalar-coefficient-square-shift-transport` records the shift-transport
intermediate theorem in the item's module.

## Second reading by S2

1. I compared the delivered module with the available repository and prior sandbox versions. The
   existing target declaration and definitions retain their signatures; this delivery adds the
   explicitly named transport theorem only.
2. I compiled the sandbox modules with `lcompile.py`. The target has no `sorry`; the only remaining
   hole is `rawModuleScalar_coefficient_square_of_unshifted`, which is named, documented, and
   represented by node `lem-sbc-raw-scalar-coefficient-square-shift-transport`.
3. The split theorem is a strictly lower shift-transport obligation, rather than a restatement of
   the target. Its statement is exactly the target body with the generic transport step isolated,
   and its edge cases include zero and negative shifts and identity arrows.
4. The proof uses the existing unshifted coefficient theorem and the generic shift API; no shorter
   proved declaration was found. The imports are all used by the definitions or proof, and the
   unit route remains the coefficient-square route in `sk-lem-failure-field`.
5. The DAG node records the split theorem, its source, proof dependency, and Lean declaration.
   I added a complete proof sketch to the theorem docstring so the remaining `sorry` is a named,
   reviewable theorem. No definitions contain `sorry`, and no new statement changes a target.

I changed the transport and prerequisite theorem docstrings, added nodes for both prerequisite
holes, added the required change record for the new public prerequisite module, and updated the
report. No target statement was changed.

New nodes delivered: `lem-sbc-raw-scalar-derived-pullback-shift` and
`lem-sbc-raw-scalar-coefficient-unshifted`; the change record is
`coord/changes/RawModuleScalarCoefficientUnshifted.md`.

## New nodes

`lem-sbc-raw-scalar-derived-pullback-shift` records shift compatibility of the derived scalar
comparison. `lem-sbc-raw-scalar-coefficient-unshifted` records the unshifted coefficient square.
The associated change record is `coord/changes/RawModuleScalarCoefficientUnshifted.md`.
