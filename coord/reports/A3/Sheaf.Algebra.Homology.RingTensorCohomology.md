## What changed

Repaired the returned delivery: removed the duplicate private theorem
`RingTensorCohomology.scalarExtension_quasiIso_of_kFlat` and its entire proof.
`RingTensorCohomology.spanLeft_isIso` now applies the existing proved theorem
`CochainComplex.scalarExtension_quasiIso_of_kFlat` directly. Its private visibility
is handled by `import all Sheaf.Algebra.Homology.KFlatScalarExtensionDerivedIso`,
as already done by `KFlatScalarExtensionCounit`. This is a proof-only import;
all existing signatures, definitions, visibility and public imports remain unchanged.
Removed the helper's additional namespace opens. The DAG records the reused
module's node and identifies precisely which helper supplies the step.

## Proved and sorry left

Closed the single original hole `RingTensorCohomology.spanLeft_isIso`
(node `def-pc-ring-tensor-cohomology`). Added zero holes and zero declarations.
No `sorry` remains in the delivery. The scalar-extension helper used from the
existing library is already proved. This is a proof, not a decomposition.

## No longer needed

Removed the previous delivery's direct proof import of
`Sheaf.Algebra.Homology.MixedTensorKFlatQuasiIso` and the duplicate private helper.
The node no longer directly depends on `lem-pc-mixed-tensor-kflat-quasi-iso`:
that theorem remains a transitive dependency of the reused scalar-extension helper,
so this repair does not claim that its module leaves the targets' closure.
No original public import is removed, and no new node is needed.
The empty unit realization lists and the unit route are unchanged.

## Where the brief, the DAG or earlier work was wrong

The previous delivery and its second reading incorrectly treated a private theorem
as inaccessible across modules. Lean's module-system `import all` permits direct
reuse without changing its visibility or adapting its module. This repairs the
landing refusal from `import_prune_check.py`: the duplicate statement is removed,
rather than renamed or repackaged. The helper applies to the exact map needed,
unlike the public existence-of-equivalence theorem in the same module.

The borrowed helper's node `lem-sc-kflat-scalar-extension-derived-iso` belongs to
another unit and is used only as a proved scalar-extension tool; our unit route
is not replaced. No statement or definition correction is needed.
The original second-reading section was removed because it described the returned
version and claimed this reuse was impossible. The independent reader must record
fresh checks of the repair. The fresh independent second reading is recorded below.

Validation: `lcompile.py` compiles the repaired module cleanly. The landing
`import_prune_check.py` passes against the current base. A dry run with
`WEIL_SERVER_COMPILE=1` rebases onto current `sheaf-dag`, compiles locally and
on the server, runs the axiom probe, and prints OK except for the reserved
independent second reading. Nothing was pushed.

Change record: `coord/changes/spanLeft_isIso-proof-import.md`.


## Second reading by A3

1. PASS: Read the complete module and compared it with the repository using
   `diff -u` and the declaration comparison used by stage-3 delivery. Every existing
   signature, definition body, visibility and public import is unchanged. The only
   Lean edits are the proof of `RingTensorCohomology.spanLeft_isIso` and a plain
   `import all` needed by that proof. No target statement changes.
2. PASS: `lcompile.py` compiled the delivered module without errors or warnings.
   A fresh scratch copy of this repaired version printed the axioms of the reused
   `CochainComplex.scalarExtension_quasiIso_of_kFlat`, `spanLeft_isIso`,
   `flatResolution` and `comparison`: only `propext`, `Classical.choice`,
   `Quot.sound`, with no `sorryAx`. No forbidden declarations or `sorry` occur
   in the delivered source. The existing resolution choice is backed by a proved
   instance, and comparison inverts its specific proved-isomorphic span map.
3. PASS: There are no split-off statements, new declarations, new nodes or added
   holes to validate. Read the existing helper's proof: mixed total tensor with
   the coefficient ring in degree zero is naturally termwise scalar extension.
   Its hypotheses fit both resolved endpoints and do not require B to be R-flat.
   Identity coefficient maps, zero complexes and zero rings require no exception.
4. PASS: Read the proof from `spanLeft_isIso` downward. Restriction preserves the
   A-augmentation quasi-isomorphism; naturality and two-out-of-three prove that
   its R-resolution is a quasi-isomorphism; the existing helper then preserves
   this exact map. The final `change` checks it is precisely the span component.
   Searched the library by scalar-extension and quasi-isomorphism concepts: the
   sheaf change-of-rings theorem has a different category, and the reused helper
   is the direct ring-complex API. Its single added import is proof-only and used;
   the original imports support unchanged constructions. The repository node had
   empty `proof_deps`, so no original dependency was omitted from pruning. No
   module leaves the targets' closure. Read `dag/units/sk-thm-picard-semicon.json`:
   its empty realization lists are untouched, and no unit step is bypassed.
5. PASS after metadata correction: The node's three proof steps follow the Lean
   argument, its sole dependency names the node of the reused helper's module,
   and the text explicitly distinguishes that helper from the module's public
   existence theorem. The source and proof origin agree with the argument.
   Changed the helper-application step's `elementary` flag to false, since it
   invokes a substantive recorded dependency.

Second reading changed only that DAG flag, refreshed the stale scratch axiom
probe to check the repaired source, and added this independent report. The Lean
proof needed no repair. Closed one original hole, added zero: proved 1 of 1;
zero split off; no original module pruned.
