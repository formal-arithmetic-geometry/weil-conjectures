## What changed

Proved `AlgebraicGeometry.Scheme.picard_residue_homology_source_fibre_comparison` with its complete original signature and docstring unchanged. The proof compares the derived residue fibre of a line-bundle direct image with ordinary cohomology of its pulled coefficient. It explicitly constructs the residue-field isomorphism, the projection-preserving fibre scheme isomorphism, and the coefficient trivialization, then transports cohomology using structure-sheaf pullback functoriality.

All helpers are private and fully proved in the item module. No new modules, statements with holes, interface changes, or forced adaptations are delivered. Added proof imports for tensor-pullback adjunction uniqueness, the invertibility bridge, structure-sheaf cohomology functoriality, and Mathlib pullback pasting/isomorphisms. The node now describes the actual Lean proof.

The complete file compiled without warnings in 49.5 seconds using lcompile.py. Profiling an experimental direct construction of the cohomology equivalence exposed expensive kernel reduction of the concrete cohomology pullback maps. The delivered version keeps that definition locally irreducible and uses a generic proved additive-equivalence constructor; no external definition or compilation limit changed.

## Proved and sorry left

Closed the one existing hole: `AlgebraicGeometry.Scheme.picard_residue_homology_source_fibre_comparison` (node `new-picard-residue-homology-comparison-source-fibre`). No sorries remain in the delivered module; zero new holes. This is a proof from existing dependencies, not a decomposition; their pre-existing obligations are unchanged.

The residue-field argument applies at nonclosed points of nonreduced schemes. Pullback and unit comparisons also apply to empty fibres. The ordinary geometric helper does not require properness, flatness, or invertibility away from the specified fibre. No arbitrary existence witness defines data: the adjunction comparisons and inverses are determined by their universal properties.

## No longer needed

Removed direct proof imports `Sheaf.AlgebraicGeometry.TensorPullbackCompositionIso` and `Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf`. The geometric calculation uses ordinary module pullback composition and unit isomorphisms after adjunction uniqueness. Their nodes `def-pc-tensor-pullback-composition-iso` and `lem-weil-pbc-module-pullback-structure-sheaf` are no longer direct proof dependencies of this node.

No whole module leaves this module's transitive import closure: both removed direct imports remain through existing dependencies. No pruning of a unit statement or proof step is proposed. Removed the prior sandbox's unused AddEquivNonemptyTrans module and its undelivered node; neither was in the library and neither contributes to the pruning count.

## Where the brief, the DAG or earlier work was wrong

The previous attempt's claim that no smaller geometric step could be completed was incorrect. The existing base-change, single-pullback, and affine-section comparisons suffice for the derived part. Mathlib residue-point naturality and pullback pasting give the geometric fibre identification. The ordinary module pullback API transports tau directly, and existing structure-sheaf cohomology functoriality supplies the final transport. No statement is disputed.

The original node omitted the invertibility bridge, tensor-pullback adjunction, and cohomology functoriality from its explicit proof dependencies; these are now recorded. Ordinary pullback composition/unit comparisons replace its direct tensor-composition/unit dependencies below the unit level. The unit route and target statements are preserved.

Searches made with msearch.py: LeanFinder for the derived fibre of a direct image of an invertible sheaf (generic sheaf-cohomology hits); Loogle for IsIso and residueFieldMap (open-immersion residue-field instance); grep for the affine higher-direct-image and derived single-object homology comparisons (no endpoint hits). Direct rg inspection of both library roots located the base-change examples, invertibility bridge, derived homology computation, and cohomology functoriality actually used.

## Earlier second reading (a previous round; superseded)

The delivered item module and its proof-dependency node were reread. The target
signature is unchanged. The derived comparison uses the stated base-change,
single-pullback, affine-sections, and source-library homology declarations. The
private fibre helper is strictly smaller: it only constructs the residue-field
and pullback isomorphism and a coefficient unit isomorphism. The cohomology helper
is strictly smaller: it only transports structure-sheaf cohomology along a scheme
isomorphism. The unit route is retained.

Change record: `coord/changes/picard-residue-proof-imports.md`.

## Second reading by N1

1. **Visible declarations and statements.** Compared the delivered module with the repository version. The target theorem signature and docstring are byte for byte unchanged; only proof imports, private helpers, and the target proof body changed. Verdict: pass.

2. **Proof validity.** Compiled the complete module with `lcompile.py` (57.0 s). There are no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` declarations in the delivered file. The private helpers construct their data from explicit isomorphisms and universal-property comparisons. Verdict: pass.

3. **Split-off statements.** No new public theorem or split-off hole was added; the one target hole is closed directly. The existing node remains the exact statement and its proof dependencies describe the declarations actually used. Verdict: pass.

4. **Shortest route and pruning.** The proof uses the existing derived base-change, canonical single-pullback, affine sections, tensor-pullback adjunction, and structure-sheaf cohomology functoriality results. The direct tensor-composition and tensor-structure-sheaf imports are removed from the module's proof dependencies; no unit statement or route step is bypassed. Verdict: pass.

5. **DAG agreement.** The node's proof, `proof_deps`, and `proof_origin` match the final Lean proof, and the change record documents the proof-only imports. Verdict: pass.

Changed during this second reading: appended this review record only; no Lean code, node, or change record required repair.
