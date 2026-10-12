## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.AffineFlatConnectiveTruncation`
with a complete Lean reduction. The signature and public imports are unchanged.
Proof-only imports add the existing quasi-coherent cokernel theorem, the existing
finite-presentation cokernel theorem, the new affine flat-opcycles step, and the
new right exact truncation comparison.

The proof treats degrees below zero, zero, and above zero separately. At zero it
identifies the term with a cokernel and applies the two existing closure theorems.
Zero modules are identified with the free module on an empty generating family.
Flatness transfers through explicitly restricted-scalar section isomorphisms.
For base change, the new comparison isomorphism of complexes is mapped by the
homology functor, then composed with the inverse of Mathlib's homology isomorphism
for the canonical truncation projection.

`Sheaf.Algebra.Homology.RightExactTruncGEIso` is fully proved from Mathlib. Its
component isomorphisms commute with the two projections; cancelling their mapped
epi components proves the differential squares. The only new unfinished theorem
is the flatness of the degree-zero opcycles on an affine scheme. It assumes only
universal vanishing in degree -1, and needs no boundedness or finite presentation.

## Proved and sorry left

Hole closed in the item:
`AlgebraicGeometry.Scheme.Modules.affine_flat_connective_truncation`
(node `lem-pc-affine-flat-connective-truncation`). Its proof is complete from the
named dependencies; this is a decomposition, not a proof free of sorry dependencies.

New theorem fully proved from Mathlib:
`CochainComplex.nonempty_map_truncGE_iso`
(node `lem-pc-right-exact-truncge-iso`). All private helpers are proved as well.

One new hole remains:
`AlgebraicGeometry.Scheme.Modules.affine_opcycles_flat_of_universally_exact`
(node `lem-pc-affine-universally-exact-opcycles-flat`), in
`Sheaf.AlgebraicGeometry.AffineUniversallyExactOpcyclesFlat`. Its proof is exactly
`:= by sorry`, with its source and full argument in its docstring and node.
There are no sorries remaining in the item or the right exact comparison module.

Existing unfinished dependency used without modification:
`AlgebraicGeometry.RingedSpace.isFinitePresentation_cokernel_of_both_isFinitePresentation`
(node `lem-weil-pbc-module-finite-presentation-cokernel`, module
`Sheaf.AlgebraicGeometry.ModuleFinitePresentationCokernel`). That module's other
existing hole is `AlgebraicGeometry.RingedSpace.isFinitePresentation_cokernel_of_isFiniteType`.
These are not new holes created by this delivery.

Counts: one original hole closed, one new hole added; one decomposition and a
separate fully proved generic comparison theorem. No claim of positive net progress
in the targets' import closure is made.

## No longer needed

No original imports or planned mathematical dependency modules are pruned.
The original affine tilde equivalence and module flat-opcycles criterion remain
needed below the new affine flatness step, so moving them there is not pruning.
The boundedness hypotheses hCge and hCle are retained with the exact original
signature; the proof needs neither bound.

Removed redundant candidate imports from the new right exact comparison module:
`Mathlib.Algebra.Homology.Additive`, `Mathlib.CategoryTheory.Abelian.Basic`, and
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels`. Its sole import
`Mathlib.Algebra.Homology.Embedding.CochainComplex` already provides the interfaces
used. This does not prune existing library nodes or modules.

## Where the brief, the DAG or earlier work was wrong

The original node classified finite-presentation cokernel closure and truncation
commutation after pullback as elementary steps, but they require named categorical
interfaces in Lean. Finite-presentation closure already has a suitable statement
for arbitrary ringed spaces; the source-library cokernel finite-presentation theorem
alone would incorrectly require a locally Noetherian base. The right exact comparison
has now been proved generically, without a flatness hypothesis on the functor.

Mathlib searches: LeanFinder and Loogle found truncGEXIsoOpcycles, truncation-map
interfaces, and opcyclesIsoCokernel, but no affine universal-testing criterion or
right exact truncation comparison. Source and Mathlib rg searches found the module
opcycles criterion and the existing cokernel closure modules. Both natural-language
LeanSearch queries returned Internal Server Error, recorded as unavailable rather
than evidence of absence.

Sources read online: [0653](https://stacks.math.columbia.edu/tag/0653),
[0654](https://stacks.math.columbia.edu/tag/0654),
[0118](https://stacks.math.columbia.edu/tag/0118),
[01IB](https://stacks.math.columbia.edu/tag/01IB), and
[0H96](https://stacks.math.columbia.edu/tag/0H96).
The square-zero testing argument is the agent-written specialization already
planned by the original node. The new opcycles statement was checked on the empty
scheme, zero complex, complexes already concentrated in nonnegative degrees, and
unbounded complexes: only exactness of each tensor complex at -1 enters the Tor
criterion. The comparison statement was checked on arbitrary integer cutoffs and
on zero categories, and its full Lean proof verifies all differential squares.
No target or definition changed. The unit statement and its route are retained.

## New nodes

`lem-pc-affine-universally-exact-opcycles-flat` states strictly the flatness step:
no termwise truncation properties, no finite presentation, and no homology
comparison conclusion. It carries the square-zero testing and Tor criterion proof
and retains the two original planned dependencies below it. Its module has one sorry.

`lem-pc-right-exact-truncge-iso` states the generic complex comparison used in the
base-change step. It is fully proved from Mathlib, with no new unfinished statements.
Both nodes inherit chapter `sec-picard-framework` and unit `sk-thm-picard-coherence`.
The existing node's proof, proof_deps and proof_origin now follow the actual Lean
reduction. No change records or forced adaptations are needed.

## Second reading by U2

1. Compared the delivered affine truncation module with the repository version. The theorem signature and all existing declarations are unchanged; the added imports are proof-only. The two auxiliary modules are new declarations, and their signatures match their DAG nodes. Verdict: pass. The pre-existing `created.item` metadata in the truncation node names `Sheaf.AlgebraicGeometry.ProperFlatFinitePresentationModel`; this immutable provenance field is outside this delivery.

2. Compiled all three delivered modules with `lcompile.py --all`; they compile without errors or warnings. The truncation target has no `sorry`; the only remaining `sorry` is the explicitly named theorem `affine_opcycles_flat_of_universally_exact`, with a matching node and source/docstring proof. No forbidden declarations or hollow definitions occur. Verdict: pass, with the documented split-off hole.

3. Checked the split-off opcycles statement on zero and empty schemes, zero complexes, complexes already concentrated in nonnegative degrees, and unbounded complexes; it is strictly the needed flatness step and adds no hidden boundedness or finite-presentation assumptions. The right-exact truncation statement is generic and exactly matches its use. Searches recorded in the node found no existing duplicate. Verdict: pass.

4. Read the proof from the target downward. It uses the affine opcycles step, the existing quasi-coherent and finite-presentation cokernel closures, and the proved right-exact truncation comparison. The zero, degree-zero, and positive-degree cases follow the canonical truncation isomorphisms; no shorter available declaration was found. Imports removed from the comparison module are recorded above, and no old target dependency is pruned. Verdict: pass.

5. The node proof/proof_deps/proof_origin fields agree with the Lean proof, and the unit route remains through `sk-thm-picard-coherence`. The auxiliary nodes carry their modules, declarations, source, searches, and split status. Verdict: pass.

Changed: no Lean code or theorem statement was changed during second reading; the immutable provenance metadata discrepancy is recorded above.
