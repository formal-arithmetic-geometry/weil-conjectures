## What changed

Removed the duplicate declaration
`AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap_of_isClosedImmersion` from
`Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso` as required by the
upstream-review #1424 repair queue. Its DAG node now points to the existing
`AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap` in
`WeilConjectures.ConstructibleSheaf.UniversalHomeomorphism`.
The empty retired module has no imports. Both
`Sheaf.AlgebraicGeometry.FieldPointFactorsThroughClosedImmersion` and
`Sheaf.AlgebraicGeometry.FieldPointFactorsThroughImmersion` replace their
private import and their single theorem application. All caller signatures
and definitions are byte-for-byte unchanged.
Change record: `coord/changes/isIso_residueFieldMap_of_isClosedImmersion.md`.

## Proved and sorry left

Holes closed: none. Holes added: none. The repository already proved
`AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap_of_isClosedImmersion`;
this delivery retires that duplicate rather than claiming new proof progress.
`AlgebraicGeometry.field_point_factors_through_closed_immersion` and
`AlgebraicGeometry.fieldPoint_factorsThrough_immersion` remain proved by their
existing proofs using the generic theorem directly. No sorry remains in any
of the three delivered modules. No declarations are added or split off.

## No longer needed

`Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso` is removed from both
callers' imports and becomes unreachable through them; its declaration and
all three imports (Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion,
Mathlib.AlgebraicGeometry.ResidueField,
WeilConjectures.ConstructibleSheaf.UniversalHomeomorphism) are removed.
The closed-immersion DAG node remains needed as a specialized mathematical
fact, realized by the generic theorem. Its only old proof dependency,
`lem-weil-pbc-surjective-stalks-residue-field-iso`, remains used. No proof
dependency node is pruned; the retired wrapper module is pruned from the
callers' import closure. The sk-thm-p1 unit realization is unchanged.

## Where the brief, the DAG or earlier work was wrong

Upstream review #1424 correctly identified the closed-immersion theorem as a
wrapper around the existing generic theorem. The saved repair removes that
wrapper and redirects its only two callers. The node statement is unchanged;
its Lean record now identifies the existing generic theorem specialized using
`IsClosedImmersion`'s `SurjectiveOnStalks` instance. No unit route changes.

The current worker independently compared both caller diffs with the repository,
read the generic theorem, and confirmed that the node changes only its `lean`
record. Each caller changes only its private import and one theorem application;
all existing caller signatures and visibility remain unchanged.

## Forced adaptations

`Sheaf.AlgebraicGeometry.FieldPointFactorsThroughClosedImmersion` changes lines
9 and 54. `Sheaf.AlgebraicGeometry.FieldPointFactorsThroughImmersion` changes lines
10 and 59. Each replaces only the retired module's private import and the removed
wrapper's application with the generic theorem. The removed declaration forces
both edits; all caller signatures and visibility remain identical. The change
record lists both callers and their holders.

Verification (2026-10-14): `lcompile.py --all` compiled all three repaired
modules without warnings (exit code 0; 0.3 s, 2.6 s, 4.1 s). Both replacement imports pass
`import_direction.py may`. The prescribed delivery dry run compiles the three
repaired modules, probes their axioms, and compiles each original caller against
the repaired dependencies to establish that its adaptation is forced.

The original closed-immersion caller fails at line 54 with
`error(lean.invalidField): Invalid field
isIso_residueFieldMap_of_isClosedImmersion`, because the environment no longer
contains `AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap_of_isClosedImmersion`.
The original immersion caller fails at line 59 because the same removed
constant is unavailable. The delivery tool appends both actual compiler
outputs to the delivered report.

The previous attempt was blocked by the diagnostic parser in `deliver3.py`.
The current script now accepts `error(` diagnostics, so that earlier tool
failure no longer applies. No tool was modified or bypassed by this worker.
The reserved second-reading section is left for the independent reader.

The prescribed `deliver3.py ... --no-push` printed `OK (dry run)`: the
compiled delivery passes preflight except for the second reading, which the
second reader writes. Nothing was pushed. The empty retired module has no
declarations to probe; the tool reports its axiom-probe note and accepts it.

## Second reading by C3

1. PASS: Independently diffed all three delivered modules against the repository.
   The only removed declaration is the duplicate named in the repair queue and
   change record. Each caller changes exactly its private import and theorem
   application; all surviving signatures, visibility and definitions are byte
   for byte unchanged. No target statement or definition changes. A source scan
   of lean/ finds exactly these two callers of the removed name and module.
2. PASS: Independently ran lcompile.py --all: all three modules compiled without
   warnings. No delivered module contains sorry or forbidden declarations.
   A scratch module importing the sandbox-compiled callers printed axioms for
   the generic residue-field theorem and both caller theorems: each uses only
   propext, Classical.choice and Quot.sound. No data construction changes.
3. PASS: No statements or nodes are split off or newly added. Read the existing
   generic theorem and its surjectivity proof: stalk surjectivity descends to
   residues, and a surjective unital field map is injective and thus an
   isomorphism. Mathlib's IsClosedImmersion class extends SurjectiveOnStalks,
   so specialization supplies precisely the removed conclusion. Empty schemes
   have no chosen point; at every chosen point the residue ring is a field.
4. PASS: Both callers take the existing generic theorem directly, eliminating
   the redundant wrapper. Replacement imports are private proof imports. The
   retired module has no imports, and No longer needed lists all three removed
   imports and the pruned wrapper module. The sole old proof dependency remains
   used. Read dag/units/sk-thm-p1.json, including realized: no unit statement,
   step, realization or route changes; this repair is below the unit level.
5. PASS: Independently diffed the node JSON: only lean changes, redirecting to
   the existing generic theorem. Its unchanged proof, proof_deps and
   proof_origin already describe exactly this specialization; the mathematical
   statement is unchanged. The generic theorem's section parameters supply
   its recorded W, Z, p and SurjectiveOnStalks context.

Second-reading changes: appended this independent review and added an axiom
probe under scratchpad/ only. No Lean, node or change-record repair was needed.
This is pruning with zero holes closed and zero holes added, not new proof
progress. The delivery tool independently checks the original callers against
changed dependencies to confirm that both adaptations are forced.

## Forced adaptations

### Sheaf.AlgebraicGeometry.FieldPointFactorsThroughClosedImmersion
Original against changed dependencies failed:
```
/tmp/forced-adaptation-3jm17_mf/lean/Sheaf/AlgebraicGeometry/FieldPointFactorsThroughClosedImmersion.lean:54:6: error(lean.invalidField): Invalid field `isIso_residueFieldMap_of_isClosedImmersion`: The environment does not contain `AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap_of_isClosedImmersion`, so it is not possible to project the field `isIso_residueFieldMap_of_isClosedImmersion` from an expression
  i
of type `Z.Hom X`

(with the modules compiled into /tmp/forced-adaptation-3jm17_mf/.lbuild) [2.6 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.AlgebraicGeometry.FieldPointFactorsThroughImmersion
Original against changed dependencies failed:
```
/tmp/forced-adaptation-ngknxxh1/lean/Sheaf/AlgebraicGeometry/FieldPointFactorsThroughImmersion.lean:59:4: error(lean.unknownIdentifier): Unknown constant `AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap_of_isClosedImmersion`

(with the modules compiled into /tmp/forced-adaptation-ngknxxh1/.lbuild) [2.5 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
