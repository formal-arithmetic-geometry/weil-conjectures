## What changed

Added a proof of `AlgebraicGeometry.rhom_supported_quasiCoherent_perfect_part` using the derived internal-Hom adjunction, perfect RHom tensor comparison, and canonical derived tensor quasi-coherence preservation. Added `Sheaf.AlgebraicGeometry.PerfectImpliesQCoh` for the strictly simpler perfect-implies-quasi-coherent component, now proved from finite-free refinement and pseudo-coherent quasi-coherence.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.rhom_supported_quasiCoherent_perfect_part`.
Also proved the new helper `AlgebraicGeometry.schemeDerivedQCohProperty_of_isPerfect`
(node `lem-sc-perfect-qcoherent`); no holes are added or left in the delivered modules.
One original hole closed, zero new holes: a net reduction of one local hole, subject to
the maintainer's closure ledger. Both declarations still depend on imported open theorems.

## No longer needed

`Sheaf.AlgebraicGeometry.DerivedPullbackTensorQCoh` (and its node
`lem-pc-derived-pullback-tensor-qcoh`) is not used directly by the proof.
The old proof dependency `def-pc-perfect-complex` is now a statement dependency,
not a directly used proof lemma of the target. No globally pruned module is claimed:
DerivedTensorQCohClosure still imports DerivedPullbackTensorQCoh transitively.

## Where the brief, the DAG or earlier work was wrong

The DAG omitted the necessary intermediate statement that perfect objects have quasi-coherent cohomology; it is added as `lem-sc-perfect-qcoherent`.

## New nodes

`lem-sc-perfect-qcoherent`: `Sheaf.AlgebraicGeometry.PerfectImpliesQCoh`.

## Earlier second reading (a previous round; superseded)

A second worker should verify the target proof and the new helper statement; the helper is strictly the perfect-implies-quasi-coherent subclaim used to construct the QCoh subtype required by tensor-Hom comparison.

The associated change record is `coord/changes/rhom-perfect-proof-imports.md`.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered item module with the repository version. The target
   declaration is byte-for-byte unchanged; only proof text, proof-only imports,
   and the required helper module were added.
2. Compiled both sandbox modules with `lcompile.py --all`. There are no
   forbidden declarations or hollow definitions. The target's only remaining
   `sorryAx` comes through the explicitly named helper theorem.
3. Checked the split statement against the Stacks references and searched the
   library/DAG for duplicates. The helper is the strictly smaller
   perfect-implies-quasi-coherent claim and has its own node and docstring.
4. Read the proof top-down. It uses the internal-Hom adjunction, the perfect
   RHom/tensor comparison, and canonical tensor quasi-coherence preservation;
   no shorter existing theorem was found. All imports are used, and no old
   proof dependency is pruned.
5. Updated the target node's proof and proof dependencies to match the Lean
   route. The unit route is not altered.

Changed the target DAG proof metadata and added this second-reading record;
the Lean proofs and helper statement were otherwise left intact.

## Second reading by X2

1. Compared the target module against the repository with diff: the existing theorem
   signature and docstring are byte-for-byte unchanged. No existing definition or public
   import changed; added imports serve proofs only. The helper is the only new declaration.
2. Compiled both modules locally in import order. The only explicit sorry originally was
   the named helper; this reading closed it. No axiom, unsafe, opaque, extern,
   implemented_by or hollow definition is present. A scratch-copy axiom probe for the
   target reports only propext, Classical.choice, Quot.sound and sorryAx through imported
   unfinished results; the delivery tool probes every declaration again.
3. Read Scheme.IsPerfect and IsStrictlyPerfect and Stacks Tags 08C4, 08CM and 0A6H(2)
   (https://stacks.math.columbia.edu/tag/08C4,
   https://stacks.math.columbia.edu/tag/08CM,
   https://stacks.math.columbia.edu/tag/0A6H).
   The helper is true on arbitrary schemes, including the empty scheme, zero complex,
   nontrivial finite-projective summands and disconnected schemes with no uniform global
   bound. A pointwise finite-free refinement provides an upper bound locally, exactly
   what IsPseudoCoherent needs. Searches with different wording found no exact theorem;
   rg found StrictlyPerfectFiniteFreeRefinement and PseudoCoherentQCoh, which suffice to
   prove the helper. No arbitrary witness is used to define data.
4. The target proof forms the QCoh subtype, obtains the perfect dual and comparison,
   applies tensor QCoh closure, and transports along homology of the comparison iso.
   Its orientation is correct and L needs no boundedness. The helper's shorter route is
   now implemented. Every import is needed for the statements or a directly used lemma.
   The removed old proof dependencies are listed above. The unit's realized record is
   unchanged (this node is not a realized unit statement or step); no unit is bypassed.
5. Moved the target node metadata into dag/nodes, where deliver3 actually reads it.
   It records the adjunction, comparison, helper and canonical tensor closure used by
   Lean. Replaced the helper's definition-only proof plan with its actual finite-free
   refinement and pseudo-coherence route, and recorded the four searches run here (LeanSearch unavailable).

Changed: proved the split helper, corrected node placement and proof metadata, completed
pruning accounting, and corrected the report's hole counts. The target proof is unchanged.
