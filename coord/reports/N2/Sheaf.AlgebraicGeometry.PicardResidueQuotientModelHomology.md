## What changed
Replaced the original sorry in `Sheaf.AlgebraicGeometry.PicardResidueQuotientModelHomology` with a complete proof. The original theorem signature and docstring are unchanged. Added two proof-only imports: `Sheaf.AlgebraicGeometry.AffineResidueScalarTransport` and `Mathlib.Algebra.Homology.ShortComplex.ModuleCat`.

The proof identifies the affine chart prime using hp, applies the existing proved scalar-transport natural isomorphism, constructs compatible additive equivalences of terms and cycles, proves that incoming boundary subgroups correspond in both directions, descends with `QuotientAddGroup.congr`, and composes with `ShortComplex.moduleCatHomologyIso` and `HomologicalComplex.homologyIsoSc'`. The unused-variable linter is disabled only for this declaration because the original interface contains the unused E; no binder is changed.

Removed the first worker's unlanded `PicardResidueQuotientModelHomologyCore.lean` and `new-picard-residue-quotient-model-homology-core.json`. Updated the existing item's node proof, proof_deps, and proof_origin to describe the actual proof.

## Proved and sorry left
Closed: `AlgebraicGeometry.Scheme.picard_residue_quotient_model_homology` (1 of 1 original holes).
Added: none. Split off: none. No sorry remains in the delivered module.

The rejected proposed hole `AlgebraicGeometry.Scheme.picard_residue_quotient_model_homology_core` is removed together with its unlanded module and node; it was not in the library baseline. This is a full proof, not a decomposition. Local scratch-copy `#print axioms` reports exactly `propext`, `Classical.choice`, and `Quot.sound`, with no sorryAx. The final module compiles locally without errors or warnings, within the default heartbeat and single-file time limits.

## No longer needed
No existing imports or modules were pruned. The original node's proof_deps was empty, so there are no old proof dependencies to list as unused. The first worker's unlanded Core proof import, module, and proposed node are removed, not counted as library pruning.

## Where the brief, the DAG or earlier work was wrong
The first worker's helper was a restatement of the entire comparison, with E, hU, and hp removed. It was not a strictly smaller intermediate result. Removing hp makes it false: take W = Spec Z, U = top, w = (2), p = (3), and a complex with the associated sheaf of Z/2 only in degree one. The p-residue quotient is zero, whereas evaluation at w followed by scalar extension has degree-one homology F_2. The original theorem avoids this counterexample through hp.

The proposed helper docstring had no complete natural-language proof. Its node's lean.statement still named the original theorem and included the omitted binders, rather than matching the helper. Its copied review fields also described an earlier N1 landing rather than this new declaration. All of these defects disappear by removing the proposed helper.

The claim that no existing declaration supplied the needed comparison missed `AlgebraicGeometry.Scheme.affine_residue_scalar_transport`. Independent LeanFinder search for module-complex homology as a kernel/range quotient and Loogle search for `CategoryTheory.ShortComplex.moduleCatHomologyIso` confirmed Mathlib's concrete quotient API; rg searches of residue scalar transport and affine chart evaluation found the proved upstream library comparison. No new theorem is needed.

## Second reading by N2
1. Interface: PASS after repair. Compared the delivered module with the repository using diff and checked the theorem signature byte-for-byte, including its letI binders. No existing statement, definition, visibility, or public import changed. No change record is needed.
2. Proof: PASS after repair. Single-file lcompile succeeds with no warnings. The delivered source contains no sorry, axiom, unsafe, opaque, implemented_by, or extern. A scratch-copy #print axioms check reports only propext, Classical.choice, and Quot.sound. All local data is concretely constructed or obtained from the already proved scalar-transport theorem; there is no choice from an unproved existence statement.
3. Split-off statements: FAIL for the first worker's Core, repaired by removal. The counterexample above tests its missing hp hypothesis. The helper merely relocated the full argument and had an incorrect node and incomplete proof documentation. The final delivery adds no statements and no holes. The completed proof retains nonzero incoming boundaries and handles the zero complex without freeness, boundedness, or rank assumptions.
4. Route and pruning: PASS after repair. The shorter route uses the existing scalar-transport theorem and Mathlib's quotient homology comparison. Both added imports are proof-only; all three original public imports support the unchanged signature. No original proof dependency is discarded. The unit sk-prop-av-cube and its realized record are unchanged; this algebraic node-level proof does not replace any step of the cube theorem's route. Its existing realized entries are empty, a pre-existing bookkeeping gap rather than a change in this delivery.
5. Nodes: PASS after repair. Read the item's node and the scalar-transport dependency node. Updated only the permitted proof, proof_deps, and proof_origin fields of the existing item node. The proof_deps union is exactly lem-sc-affine-residue-scalar-transport; the remaining steps use elementary algebra and named Mathlib APIs. No new node remains, and all existing statements and lean records are unchanged.

Second reading changed the invalid Core restatement to a complete proof of the original theorem, removed its proposed module and node, restored exact signature text, added only necessary proof imports, and corrected the DAG and report.
