## What changed

Repaired return X-725aa without changing any dependency module. Proved
`AlgebraicGeometry.Etale.rawModuleScalar_source_class_formula` using the original
plain proof imports `RawModuleScalarSheafComposition` and
`RawModuleScalarSourceSquareCore`, and the original public signature imports.
The theorem statement, visibility and existing docstrings are unchanged.

The proof attaches the free abelian source map to the proved sheaf-composition
square, applies the existing generic single-complex source-square theorem,
and attaches the raw class by inverse-comparison naturality. Three proved private
helpers package only elementary associativity, functoriality and naturality.
The canonical comparison remains the definition in
`RawModuleScalarCoefficientUnshifted`.

Removed all three files rejected by A3 from this delivery's changed-file set:

- `lean/Sheaf/AlgebraicGeometry/RawModuleScalarSourceSquare.lean`;
- `dag/nodes/sec-smooth-base-change/lem-sbc-raw-scalar-source-square.json`;
- `coord/changes/raw-module-scalar-source-square-comparison.md`.

Their removal removes sandbox overrides, not repository files; `deleted.txt`
is neither needed nor supplied. Removed the obsolete compiled SourceSquare
overlay too. The comparison cleanup is outside this delivery. The repaired
proof uses its existing core directly, so it requires no cleanup to land first.
Only the item's Lean module, its existing DAG proof record, and this report
are included. The obsolete second reading of the rejected version is removed
so that the independent reader can review the repaired version.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.rawModuleScalar_source_class_formula`
(node `lem-sbc-raw-module-scalar-source-class-formula`).

No `sorry` remains in the delivered module. No hole, split-off theorem,
public declaration, new module or new node is added. The three private helpers
are fully proved. This is a proof, not a decomposition. The single-complex and
class steps are combined generically before specialization, avoiding a second
large concrete source-square conversion.

## No longer needed

The repaired proof does not import
`Sheaf.AlgebraicGeometry.RawModuleScalarSourceSquare`
(node `lem-sbc-raw-scalar-source-square`) or its implementation dependency
`Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso`
(node `def-sbc-raw-scalar-derived-pullback-iso`). Both stay unchanged in the
repository. These imports occurred only in the rejected delivery; neither
was in the original item's closure, so no net target-closure pruning is claimed.

Both original proof imports are used: the sheaf-composition theorem supplies
the sheaf equation, and the generic source-square core derives it.
No original import or required unit step is removed. The unit
`sk-lem-failure-field` has empty realized statement and proof-step records;
its route is preserved.

## Where the brief, the DAG or earlier work was wrong

A3: the previous comparison cleanup was incorrectly packaged as an adaptation.
The reviewer compiled original SourceSquare unchanged against its dependencies
in 40.2 seconds, so there was no forced adaptation. A diagnostic import confirms
that importing unchanged SourceSquare alongside the required coefficient module
fails because both declare
`AlgebraicGeometry.Etale.RawModuleScalarComparison.derivedPullbackIso`.
The repaired proof avoids that import and uses the existing generic core with
the canonical comparison; it does not alter either declaration.

F: added the required Forced adaptations section below and removed all claims
that the cleanup was forced. No original compiler error is asserted: no other
module is adapted in this repair.

## Forced adaptations

None. No module other than the claimed item is changed. There are no original
compiler errors or forced changed lines to report.

Validation: the repaired module compiled cleanly in 54.6 seconds with the
unchanged repository dependencies and no SourceSquare sandbox overlay. Checked
that its public theorem statement and all imports are byte-identical to the
original item, that all Lean lines are at most 100 characters, and that the three
rejected files are absent from the delivery set. The fully generic helpers
require no nonzero-class, positive-degree or extra scheme hypothesis.

## Second reading by W3

1. **Signatures and visibility.** Compared the delivered module with the
repository version. The theorem statement, its public imports, and the existing
declarations are unchanged byte-for-byte outside the proof; the three helpers
are private. Verdict: pass.

2. **Proof and axioms.** Compiled the module with `lcompile.py`; it compiles
without errors, warnings, or local `sorry`. A scratch import reports only the
allowed `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` inherited from
still-open imported declarations. No forbidden declaration or hollow definition
is present. Verdict: pass.

3. **Statements and edge cases.** No split-off statement or new public node was
introduced. The generic helper equalities are direct associativity,
functoriality, and inverse-natural-isomorphism naturality calculations. The
specialization has no extra hypotheses and covers zero classes, degree zero,
identity arrows, and empty objects. Verdict: pass.

4. **Pruning and route.** Both plain proof imports are used: the sheaf
composition theorem and the generic source-square core. The two public signature
imports remain required. No unit step is bypassed; the assigned unit has no
realized route entries. Verdict: pass.

5. **DAG agreement.** The node proof and `proof_deps` describe the repaired
generic source-square and class-naturality route, and `proof_origin` records W3's
second-reading repair. The node statement and Lean statement agree, with no
added holes or nodes. Verdict: pass.

Changed after reading: added this review record only; no Lean declaration,
statement, import, or DAG statement was changed.
