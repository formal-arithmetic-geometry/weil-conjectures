## What changed

Restore the three returned scalar comparison modules. The repository snapshot has
none of their Lean source files, but retains their three DAG nodes and statements.
The external theorem unfolds externalCup, applies scalar cup compatibility on the
fibre product, and rewrites both arguments using scalar/module pullback comparison.

Second reading removed the duplicate IsModuleCupProduct definition from
ScalarCupModuleCupCompatibility and publicly imports its canonical definition from
Sheaf.Paper.ModuleCohomologyCupProduct. The external module publicly imports that
same definition module; both comparison-theorem imports are plain, proof-only imports.
No target statement or existing definition is changed.

Change record: coord/changes/scalar-external-cup-module-comparison.md.

## Proved and sorry left

One of the three delivered theorem bodies is proved:
AlgebraicGeometry.Scheme.Modules.scalarExternalCup_moduleComparison.
Its proof still depends on open prerequisites and therefore has sorryAx in its
transitive axioms; this is a reduction, not an axiom-free completion of the target.

Two named prerequisite holes are restored with the modules:

- AlgebraicGeometry.Scheme.Modules.scalarCup_moduleCup_compatibility,
  node lem-sc-scalar-cup-module-cup-compatibility;
- AlgebraicGeometry.Scheme.Modules.scalar_moduleCohomologyPullback_comparison,
  node lem-sc-scalar-module-cohomology-pullback-comparison.

No hole is added by the second reading, and neither prerequisite was closed.
Relative to the current source snapshot, the modules and these two holes are restored;
there is no existing source-file hole closed. Relative to the returned proof, the
upper comparison is reduced to these two strictly smaller component comparisons.
The ledger, not this restoration, determines net closure progress.

## No longer needed

No library module is claimed pruned. In particular ModuleCohomologyCupProduct is
needed for the canonical IsModuleCupProduct appearing in the signatures.
The target node's old direct proof dependencies def-sc-module-cohomology-cup-product
and def-weil-pbc-module-cohomology-fmap are no longer direct proof steps: their
interfaces remain statement dependencies, and their use is carried by the two
component comparison nodes. All three current proof dependencies are used explicitly.

## Where the brief, the DAG or earlier work was wrong

The earlier report claimed that a local copy of IsModuleCupProduct safely removed
a derived cup import closure. That definition already exists publicly in the
library, so its copy would collide in combined imports and violate the one-definition
rule. The current compiled canonical cup module imports successfully with the scalar
operations and GlobalTensorPullbackMonoidalNormalization. The previous global failure
recorded in coord/returns/D4.md is not reproduced by this combined-import check.

The old report also described forced adaptations of existing modules, whereas all
three source modules are absent from this repository snapshot. This is restoration,
not a forced adaptation. The change record already describes that current baseline.

The two prerequisites are existing DAG statements, not new nodes. Their full
resolution-comparison arguments remain open; searches did not expose a theorem that
would close either in a short repair.

## New nodes

None. All three delivered node identifiers already exist in the repository.
Their statement and stmt_deps fields are unchanged. Only stage-3 proof fields and
Lean records differ.

## Second reading by D4

1. Compared each delivered source path with the repository: all three source files
   are absent after the returned landing. Compared each theorem signature with its
   retained repository DAG Lean record: the external signature is byte-for-byte
   identical; the two prerequisite signatures differ only in whitespace, with the
   same binders, types and conclusions. Sandbox Lean records contain the exact
   multiline signatures. No hypotheses, conclusions or definitions were weakened.
   Removed the local IsModuleCupProduct copy; the imported canonical definition has
   the same resolution-pairing formula and is the recorded definition node's object.

2. All three modules compiled with lcompile.py --all. Inspected every declaration:
   only the two listed public named theorems contain sorry, and no forbidden axiom,
   unsafe/opaque implementation, or hollow definition occurs. A scratch copy of the
   external module compiled against the sandbox overlay while also importing
   GlobalTensorPullbackMonoidalNormalization. Explicit #print axioms checks on all
   three theorems showed only propext, Classical.choice, Quot.sound and sorryAx;
   IsModuleCupProduct showed only the three permitted axioms. The final delivery
   tool separately probes every delivered declaration.

3. Read both prerequisite statements, their docstrings and their nodes. Cup comparison
   concerns one scheme and no pullback; pullback comparison concerns one morphism and
   no cup. Neither restates the external product. For the pullback step, the
   moduleCohomologyPullback definition uses precisely the tensor-pullback adjunction
   unit that characterizes scalarPullbackCoefficient. The normalization in
   exists_moduleExtEquiv evaluates unit-module morphisms at 1. The cup statement
   compares the signed tensor of those classes with the same sectionwise tensor
   pairing quantified by canonical IsModuleCupProduct. Checked the natural-number
   degrees, degree-zero tensor of sections, zero coefficients, empty schemes and
   arbitrary (not necessarily quasicoherent or flat) coefficients; no extra hypothesis
   is needed in those cases. Read Stacks 01F7, especially Remark 20.14.2's resolution
   diagram, and 0FKV's compatibility with the derived cup; 0BED motivates external
   products rather than supplying these project-specific scalar comparison statements.
   The documented arguments are mathematical comparisons still awaiting formalization.
   Fresh msearch LeanFinder search for acyclic-resolution cup versus Yoneda tensor
   returned Ext/cocycle equivalences, not either comparison. Loogle search for extMk
   and comp returned mk-zero/Ext composition formulas; grep returned exact-functor
   composition laws, not these comparisons. Searched lean/Sheaf and the upstream
   AlgebraicGeometry tree for scalar comparison and cup comparison names. No shorter
   existing theorem was found; neither open comparison was replaced by an alias hole.

4. Read the proof top down. hx uses the first projection with reflexive structure-map
   equality; hy uses the second projection with pullback.condition.symm, whose
   orientation is snd followed by g = fst followed by f. Unfolding externalCup leaves
   exactly the scalar cup of those pullbacks. Cup compatibility supplies the first
   equality, and congrArg₂ cup hx hy supplies its second equality. There is no missing
   coefficient transport because externalCupCoefficients is the tensor of the two
   pulled-back modules. Both comparison imports are now proof-only, and the canonical
   cup definition import is public because hcup uses it. Checked the complete old
   proof_deps list and recorded the two definitions no longer used as direct proof
   steps above. Read dag/units/sk-prop-av-cube.json: its fixed unit statement and face
   cancellation route are unchanged; its realized entries are already empty. This
   local comparison reduction bypasses no realized unit step and does not alter the
   unit record.

5. Read all three delivered nodes against the Lean. The target's new proof describes
   unfolding, the two projection equalities and cup congruence exactly; proof_deps is
   the union of the three used nodes. The prerequisite proof_deps name the scalar
   operations and respectively the canonical cup interface or module cohomology fmap.
   Their Lean module paths, declaration names and exact signature records match the
   restored modules. No new nodes require stage-3 creation fields, and no statement
   or unit field changes are delivered.

Changed in this second reading: removed the duplicate public cup definition, restored
its canonical public import, made the two external comparison-theorem imports
proof-only, and replaced stale restoration/progress/forced-adaptation claims in this
report. The existing external proof was kept unchanged.
