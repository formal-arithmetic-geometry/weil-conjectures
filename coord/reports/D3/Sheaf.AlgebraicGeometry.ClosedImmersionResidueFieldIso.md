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

The prescribed `deliver3.py ... --no-push` printed `OK (dry run)`: compile and
preflight pass except for the independent second reading. Nothing was pushed. The empty retired module has no
declarations to probe; the tool reports its axiom-probe note and accepts it.


The earlier D3 attempt saw the C3 repair in its local snapshot, but the freshly
fetched delivery base contains the duplicate and its old callers again. This
delivery restores the requested repair against that base, without adding a
proof obligation or changing any surviving signature.

## Second reading by D3

1. Compared all three delivered modules with the repository using unified diffs.
   PASS: the only removed declaration is the duplicate expressly named in repair
   queue upstream review #1424 and the change record. Both surviving caller
   signatures, visibility, definitions, and docstrings are byte-for-byte unchanged;
   their edits are limited to one private import and one theorem application each.
   The repository-wide name search finds no other caller of the removed name.
2. PASS: independently ran `lcompile.py --all`; all three modules compile without
   warnings. Scanned the delivered Lean for sorry and forbidden declarations:
   none occur. Compiled the scratch axiom probe for the existing generic theorem
   and both caller declarations: each depends only on propext, Classical.choice,
   and Quot.sound. No data construction changes and no hollow definition occurs.
3. PASS: no statements or holes are split off and no new node is introduced.
   Read the generic theorem and its surjectivity proof in UniversalHomeomorphism:
   surjectivity on stalks gives surjectivity on residue fields, and a field map is
   injective, hence bijective. Checked Mathlib's IsClosedImmersion declaration
   extends SurjectiveOnStalks. Thus the specialization has exactly the removed
   theorem's strength. The empty-source case is vacuous and the identity case
   has the expected isomorphism; no extra surjectivity-on-points hypothesis enters.
4. PASS: the repair uses the already proved generic theorem directly, without a
   replacement wrapper. Both replacements are private proof imports. The empty
   retired module has no unused imports. The report lists all three removed
   imports and the retired module, and correctly records that the only old
   proof dependency remains used. Read sk-thm-p1's realized record: none of its
   statement or step nodes is bypassed or changed by this specialization.
5. PASS: parsed and compared the node records; only the lean record changes.
   Its statement, proof, proof_deps, and proof_origin remain identical and still
   describe application of the generic theorem with the closed-immersion
   instance. The new lean record identifies that existing declaration and its
   module correctly. The change record documents the removal and both forced
   caller adaptations; no target meaning changes.

Second-reading changes: restored the existing node's two-space JSON formatting
so its diff shows only the lean-record redirection, and appended this review.
No Lean proof or declaration needed repair. This is a duplicate-removal repair:
zero holes closed, zero holes added, zero statements split off.

## Forced adaptations

### Sheaf.AlgebraicGeometry.FieldPointFactorsThroughClosedImmersion
Original against changed dependencies failed:
```
/tmp/forced-adaptation-5z99uqzo/lean/Sheaf/AlgebraicGeometry/FieldPointFactorsThroughClosedImmersion.lean:54:6: error(lean.invalidField): Invalid field `isIso_residueFieldMap_of_isClosedImmersion`: The environment does not contain `AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap_of_isClosedImmersion`, so it is not possible to project the field `isIso_residueFieldMap_of_isClosedImmersion` from an expression
  i
of type `Z.Hom X`

(with the modules compiled into /tmp/forced-adaptation-5z99uqzo/.lbuild) [2.1 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.AlgebraicGeometry.FieldPointFactorsThroughImmersion
Original against changed dependencies failed:
```
/tmp/forced-adaptation-d5yytjw4/lean/Sheaf/AlgebraicGeometry/FieldPointFactorsThroughImmersion.lean:59:4: error(lean.unknownIdentifier): Unknown constant `AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap_of_isClosedImmersion`

(with the modules compiled into /tmp/forced-adaptation-d5yytjw4/.lbuild) [2.1 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
