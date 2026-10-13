## What changed

Repaired the returned delivery after the import-prune check found that
`DerivedBaseChangeNaturality` duplicated `AlgebraicGeometry.mate_naturality`.
The helper is now exported once from `DerivedBaseChangeOpenUnit`, and
`DerivedBaseChangeNaturality` imports and reuses it. The target theorem and all
supporting theorem signatures are unchanged.

## Proved and sorry left

The original target `AlgebraicGeometry.derivedBaseChange_mayerVietoris_firstTwoSquares`
and all four supporting declarations remain proved. No `sorry` is present in the
delivered modules and no new hole was added.

## No longer needed

The duplicate private `mate_naturality` proof in
`DerivedBaseChangeNaturality` is removed. Its dependency is supplied by the
single existing theorem in `DerivedBaseChangeOpenUnit`.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery introduced a second declaration with the same statement as
the existing `AlgebraicGeometry.mate_naturality`. The repair makes that helper a
single reusable theorem and adds the proof-only import required by the naturality
module. This is a forced adaptation of the delivered supporting module caused by
the import-prune rejection; no target interface changed.

## Forced adaptations

`DerivedBaseChangeOpenUnit.lean`: changed the helper visibility from `private
theorem mate_naturality` to `theorem mate_naturality`, so another module can use
the existing declaration.

`DerivedBaseChangeNaturality.lean`: removed the duplicate helper and added the
proof-only import of `DerivedBaseChangeOpenUnit`. The original compiler/prune
failure was the reviewer error identifying the duplicate statement; these edits
are necessary to reuse the existing theorem while preserving the naturality
proof.

## New nodes

Existing delivered nodes retained: `lem-pc-derived-base-change-coefficient-naturality`,
`lem-pc-rf-mv-open-base-change-restriction`, `lem-pc-rf-mv-open-base-change-unit`,
and `lem-pc-scheme-derived-open-unit-restriction-iso`. No additional nodes were added.
Change record: `coord/changes/derivedBaseChangeMayerVietorisSquaresProofInterface.md`.

## Earlier second reading (a previous round; superseded)

Repair checked by compiling all five delivered modules with `lcompile.py --all`.
The target and supporting signatures remain unchanged, the duplicate helper is
removed, and no forbidden declarations or `sorry` remain.

## Second reading by K3

1. Compared the delivered target module with the repository version. The target
   theorem signature is byte-for-byte unchanged; only proof text and proof-only
   imports were added.
2. Compiled all delivered modules with `lcompile.py --all`. Compilation succeeds;
   there are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
   `implemented_by` declarations. The proof uses only ordinary category-theory
   lemmas and the previously stated supporting results.
3. Checked the split-off declarations and their DAG nodes. Each supporting
   statement is a genuine intermediate result (coefficient naturality, open
   unit, restriction, and restricted-unit isomorphism), has a source and proof
   description, and is strictly simpler than the target. No duplicate target
   restatement was introduced.
4. Checked pruning and imports. The target uses the four supporting modules and
   the additive derived-functor import; the duplicate mate helper was removed
   from the naturality module and the change is recorded in the accompanying
   change record. The unit route and `realized` entry are unchanged.
5. Checked the DAG proof records against the Lean proof and verified that the
   theorem assembles exactly the unit and restriction Mayer--Vietoris squares,
   with no boundary or connecting-morphism claim.

Changed only the proof implementation, proof-only imports, supporting modules
and their existing node records; no public target statement was altered.

## New nodes

Existing delivered nodes retained: `lem-pc-derived-base-change-coefficient-naturality`,
`lem-pc-rf-mv-open-base-change-restriction`, `lem-pc-rf-mv-open-base-change-unit`,
and `lem-pc-scheme-derived-open-unit-restriction-iso`. No additional nodes were added.
Change record: `coord/changes/derivedBaseChangeMayerVietorisSquaresProofInterface.md`.
