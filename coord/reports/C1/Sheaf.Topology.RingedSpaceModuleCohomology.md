## What changed

Filled both theorem proofs in `Sheaf.Topology.RingedSpaceModuleCohomology`.
`moduleCohomology_iso_resolution` installs the existing enough-injectives instance and
uses Mathlib's `InjectiveResolution.isoRightDerivedObj` for global sections.
`moduleCohomology_independent` composes the inverse comparison for I with the comparison
for J. All statements, definitions, docstrings and imports are unchanged.

## Proved and sorry left

Proved `AlgebraicGeometry.RingedSpace.moduleCohomology_iso_resolution` and
`AlgebraicGeometry.RingedSpace.moduleCohomology_independent`, both belonging to
`def-sc-ringed-space-module-cohomology`. No sorry remains in the delivered module;
no new sorry or declaration is added. The proofs continue to depend on the existing
`AlgebraicGeometry.RingedSpace.moduleSheaves_abelian_enoughInjectives` theorem.

## No longer needed

None. Both original public imports are required by the unchanged definitions and
statements. No additional proof import was introduced. The second reading records the existing
enough-injectives theorem as the actual proof dependency in the DAG. Mathlib's
comparison theorem packages the homotopy-comparison argument already described in the
existing docstrings; no unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The node is a definition node with empty proof and
proof_deps; its Lean realization also contains two comparison theorems, whose existing
docstrings already name the precise Mathlib comparison API. This API proves the first
comparison directly, and ordinary symmetry and composition prove independence.
Searches through the prescribed msearch tools (LeanFinder, Loogle and grep) all located
`CategoryTheory.InjectiveResolution.isoRightDerivedObj`; its full source signature was
checked in Mathlib/CategoryTheory/Abelian/RightDerived.lean, lines 114–121.
The existing enough-injectives signature and the curve-estimate unit's realized record
were checked. The degree p is arbitrary, including zero; neither argument needs any
nonempty-space or nonzero-module assumption.

## Second reading by C1

1. PASS: compared the sole delivered Lean module with the repository using `diff -u`.
   Only the two `sorry` proof bodies change; existing signatures, definitions, docstrings,
   declaration visibility and imports are byte for byte unchanged. No change record is needed.
2. PASS: the module compiles locally without errors or warnings. A scratch copy with
   `#print axioms` for all six declarations compiles: the global-sections functor,
   its additive instance and global-sections complex use only `propext`, `Classical.choice`
   and `Quot.sound`; module cohomology and both comparison theorems additionally use
   `sorryAx` from the still-open imported enough-injectives theorem. No local `sorry`,
   hollow definition, axiom, unsafe, opaque, implemented_by or extern is introduced.
3. PASS: no new declaration or split-off statement. Read Mathlib's exact comparison
   signature and implementation and independently searched `lean/Sheaf`, the upstream
   Lean sources, and Mathlib for homotopy-category comparison and homology factorization.
   The proof works uniformly for p = 0, the empty space and the zero module, and for
   I = J; no extra hypothesis is used.
4. PASS: Mathlib's direct comparison and inverse/composition give the shortest route.
   Both public imports supply API used in existing definitions and remain required.
   The old proof_deps was empty, so no old dependency is pruned. Inspected
   dag/units/sk-thm-curveestimate.json: its realized statement and steps are preserved.
5. REPAIRED: the definition node's empty proof record omitted the comparison theorems
   in its Lean realization. Recorded the Mathlib computation and isomorphism composition,
   the existing enough-injectives proof dependency, and the source/proof origin. The
   node's statement, stmt_deps, lean realization and every other field stay unchanged.

Changes by the second reader: DAG proof metadata and this report only. The Lean proofs
were correct and are delivered as written by the first worker. No new node or change record.
