## What changed

Proved `AlgebraicGeometry.normalizedTensorHomCochains_component` with its original
signature, using the normalized global-component formula, the existing degreewise
pure-tensor specification, and the upstream sheafification and tensor-Hom APIs.
There are ten proved private helpers, no dependency-module edits, and no new definitions.

Repair H10, returned head 38e645d99: the main cochain calculation is now performed
by `tensor_hom_global_component` over an abstract site and ring sheaf, with an arbitrary
degreewise map satisfying `HomTensorCurryCondition`. The public theorem specializes
that proved calculation. This avoids repeated rewriting with the scheme's concrete
instances. The generic proof eliminates the input cochain using surjectivity of the
normalized global equivalence, so its section is an abstract variable rather than an
expanded inverse construction. The final step directly applies `curry_condition_reindex`.
The redundant local aliases for P, L, I, c and the duplicated final evaluation terms
have been removed.

The proved bridge `normalized_projection_eq` identifies the two existing projection
APIs once with abstract arguments. Both definitions are locally irreducible during
subsequent calculation. Its reflexivity proof explicitly retains the right-hand
projection constant, and the normalized-factor evaluation proof also keeps its
definition folded. No public signature, public import or definition changes.

Artifact-producing verification uses `lcompile.py --all` on a two-module set containing
this exact repaired file and the unchanged direct importer
`Sheaf.AlgebraicGeometry.NormalizedHomotopyTensorHom`. Under the unchanged 60-second
limit, `scratchpad/repair-generic-right` compiled the repaired module in 51.0 seconds
and the importer in 10.9 seconds. The independent fresh-output repeat in
`scratchpad/verify-final` compiled the repaired module in 45.7 seconds and the
importer in 9.6 seconds, again without warnings. All generated module companions are written to each set's
`.lbuild`; the importer reads those local artifacts. The SHA256 of the repaired source checked in both sets is
`e08c670503a1e105ea6b6b69ee328868568487052fa81d07c7bd9e832d7de22f`.
The importer and all diagnostic scratch files are outside the delivery. No profiling options or skipped checks are
present in delivered Lean code.

Repair H9 remains in force: the used proof imports
`Sheaf.Algebra.Homology.HomTensorDegreewise` and
`Sheaf.Algebra.Homology.NormalizedHomComplexGlobalCochains` are both retained.
The scoped context and compilation evidence are documented in
`coord/changes/normalized-tensor-hom-local-proof-context.md`.

## Proved and sorry left

Closed the one original hole, `AlgebraicGeometry.normalizedTensorHomCochains_component`
(node `lem-pc-normalized-tensor-hom-cochain-components`). Added zero holes and split off
zero admitted statements. No `sorry` remains in delivered Lean code. All ten private
helpers, including `normalized_projection_eq` and `tensor_hom_global_component`,
are proved. This is a proof from the existing dependency declarations, not a
reduction into new admitted statements.

## No longer needed

Removed the direct proof import `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed`
and proof dependency `lem-pc-sheaf-modules-tensor-closed`: its existential wrapper is
not used. The proof uses the upstream `tensorHomEquiv` API directly. The statement
dependencies remain unchanged. This removes a direct import and proof dependency;
it does not claim the wrapper module is unreachable through other imports.

The proof imports `Sheaf.Algebra.Homology.HomTensorDegreewise` and
`Sheaf.Algebra.Homology.NormalizedHomComplexGlobalCochains` are needed and retained.
No other imports, nodes or modules are pruned. Neither `TensorHomPureTensorExt` nor
`HomTensorCurryZero` is modified or imported. The invalid earlier core theorem and
its node remain absent from this delivery.

## Where the brief, the DAG or earlier work was wrong

The earlier H10 timing and second-reading entries did not establish artifact-producing
compilation within the limit; the maintainer independently reproduced the timeout.
An intermediate repair in this session compiled once in 54.5 seconds but timed out
on a fresh repeat, so it was replaced by the generic calculation above. The old
second-reading entry concerns the returned file and has been removed; the independent
reader supplies the new entry.

The earlier claim that the two Homology proof imports were redundant was incorrect;
H9 restored them. Dependent projection indices are still reindexed by substitution
before applying the degreewise specification. The mathematical argument and unit
route are unchanged. No consumer adaptation, new node, target change or dependency
definition change is needed.

## Second reading by G1

1. Compared the delivered module and node with the repository versions. The public theorem
   signature and all existing declaration signatures are unchanged; the node records the proof
   and dependency pruning.
2. Compiled the delivered module with `lcompile.py`; it succeeds without warnings. The file has
   no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`, and the proof uses only
   the permitted upstream declarations.
3. Checked the proof route and helper statements. The ten private helpers are true equalities or
   direct reindexings, introduce no admitted statements, and are strictly internal reductions;
   no split-off node was added.
4. Checked pruning and imports. `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed` is unused
   and removed; the two Homology imports remain necessary. The normalized tensor-Hom unit route
   and its realized steps are preserved.
5. Checked the DAG and report against the Lean proof. The node's proof, `proof_deps`, and
   `proof_origin` match the implementation, and the original target statement is unchanged.

Changed only the proof module, its proof metadata, and this second-reading record; no definitions,
public interfaces, consumer modules, or new holes were introduced.
