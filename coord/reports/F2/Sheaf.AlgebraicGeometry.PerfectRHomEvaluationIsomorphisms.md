## What changed

Replaced the sorry in `AlgebraicGeometry.perfect_rhom_evaluation_isomorphisms` by a
complete Lean reduction, without changing its signature or its existing docstring.
Two proved private helpers handle the change from the canonical tensor-Hom family
to the arbitrary natural family in the statement. `changeAdjunction` constructs the
endomorphism representing the change and proves it is invertible by Yoneda.
`evaluationIso_changeAdjunction` proves the comparison equation using associator
naturality and cancels these isomorphisms.

For the canonical family, the proof unpacks the perfect neighbourhoods, proves they
cover X, uses the new local computation, and descends invertibility through all
homology sheaves. It uses `mapDerivedCategoryHomologyFunctorIso`,
`DerivedCategory.isIso_iff`, and the existing sheaf-module open-cover criterion.
No local morphisms are glued, and no quasi-coherence assumption on N is used.

Added `Sheaf.AlgebraicGeometry.StrictlyPerfectRHomEvaluationLocal`, containing only
the canonical evaluation calculation on an open with a strictly perfect
representative. Updated the original node's proof and dependencies. Added proof-only
imports of this module, `Sheaf.Topology.SheafIsomorphismLocalOpenCover`, and
`Mathlib.CategoryTheory.Yoneda`. Both original public imports are preserved.
The theorem-scoped transparency options and heartbeat allowance address elaboration
of the shared derived tensor instances; they do not affect importers.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.perfect_rhom_evaluation_isomorphisms`
(node `lem-pc-perfect-rhom-evaluation-isomorphisms`). The assigned module has no sorry.
The private helpers `changeAdjunction` and `evaluationIso_changeAdjunction` are proved.

Added one hole:
`AlgebraicGeometry.strictlyPerfect_rhom_evaluation_isIso_on_open`
(node `lem-pc-strictly-perfect-rhom-evaluation-local`), in its own new module.
This is a decomposition: one upper hole closed and one strictly local, canonical
hole added, net zero holes. The new theorem does not assume global perfectness and
proves only the restriction on the specified strictly perfect neighbourhood; the
arbitrary-adjunction argument and descent to the whole scheme are proved here.

Both modules compile through lcompile.py. The new statement was checked against
Stacks Tags 08DQ and 08DM, read from their Stacks pages. Its edge cases include an
empty open, the zero complex, a finite free module in one degree, a retract of a
finite free module, and an unbounded second argument: the bounded first complex
ensures only finitely many summands in each Hom degree, and its bounded flat dual
computes the derived tensor without boundedness on N.

## No longer needed

Removed these direct proof imports from the assigned module:

- `Sheaf.Paper.DerivedInternalHomRestrictOpen`
- `Sheaf.AlgebraicGeometry.StrictlyPerfectDerivedInternalHom`
- `Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat`

These are not claimed as eliminated mathematical work: RHom restriction and the
strictly perfect Hom computation remain in the new local node's plan. That plan
uses the bounded-above flat SITE lemma (`lem-pc-bounded-above-flat-kflat-site`),
which fits the localized-site category directly, in place of the ringed-space
wrapper (`lem-pc-bounded-above-flat-kflat`). The latter wrapper is not needed on
this proof branch. The original top-level proof no longer directly needs
`lem-sc-derived-internal-hom-restrict-open`, `lem-pc-rhom-strict-perfect-hom`,
`lem-pc-bounded-above-flat-kflat`, `lem-sc-derived-internal-hom-adjunction`, or
`def-pc-tensor-complex-sheaves`: the updated node records its actual dependencies.
The tensor-complex definition is still needed by the local node. The adjunction
module remains a public import, preserving the existing interface. No entire
module is claimed pruned from the target closure; final pruned count: none.

## Where the brief, the DAG or earlier work was wrong

The stated lower interfaces do not themselves close the evaluation calculation.
`derivedInternalHom_restrict_open` gives only a Nonempty object isomorphism, with
no equation identifying the evaluation morphism. The strictly-perfect Hom theorem
computes RHom but does not identify the tensor-Hom evaluation chain map. In addition,
its current wrapper assumes the open is affine, although the source Tag 08DM is
valid on any ringed space. The new local statement follows that source directly;
its proof plan explicitly avoids applying the affine wrapper on a non-affine open.
These compatibility calculations are the remaining hole, rather than a claim that
an arbitrary isomorphism of the two objects identifies the displayed morphism.

The canonical adjunction definition is useful here: its representative equation
pins down evaluation, while the new proved helpers handle the arbitrary adjunction
in the original statement. Explicit derived-universe arguments are necessary when
selecting that canonical family. No existing definition or statement was changed,
no forced adaptation was needed, and the unit's route is preserved.

## New nodes

`lem-pc-strictly-perfect-rhom-evaluation-local` is the local canonical computation
from the original node's first proof step, sourced to the strictly perfect case in
Stacks Tag 08DQ and to Tag 08DM. Its Lean module is
`Sheaf.AlgebraicGeometry.StrictlyPerfectRHomEvaluationLocal`. It deliberately omits
global perfectness and arbitrary adjunctions, and concludes only local invertibility;
thus it is strictly a part of the argument. Its docstring and node give the full
termwise proof plan, including compatibility with the actual canonical evaluation,
finite projective retracts, differential signs, and K-flatness of the dual.
Searches found the generic dual-pair Hom equivalences and upstream bounded-complex
dualizability, but no theorem identifying this restricted scheme evaluation.
LeanSearch was unavailable; LeanFinder, Loogle and local grep were also used.
There are no change records because every existing public signature is unchanged.

## Second reading by F2

1. **Statements and interfaces.** Compared the delivered item module with the repository version. The existing target theorem signature and all existing declarations are byte for byte unchanged; the added local theorem is a new, strictly narrower statement with no altered definitions.

2. **Proof and axioms.** Compiled both delivered modules with `lcompile.py`; the target theorem has no `sorry`, while the only remaining `sorry` is the named local theorem listed above. No forbidden declarations or hollow definitions were introduced. The target proof uses only the existing canonical adjunct facts, Yoneda comparison, local invertibility, and open-cover descent.

3. **New statement.** Checked `strictlyPerfect_rhom_evaluation_isIso_on_open` against the strictly perfect local case in Stacks Tags 08DQ and 08DM. Its hypotheses and conclusion are exactly the local calculation needed by the global proof, and it is strictly weaker than the original global target. The theorem is documented and has the matching DAG node.

4. **Pruning and imports.** The proof-only imports removed from the target module are not used by the delivered proof. The remaining imports are used by declarations or proof elaboration, and the local module retains its required public imports. The original target node's proof and dependency metadata were updated to match the written route; no whole module is claimed pruned.

5. **Unit route.** The global proof still follows the unit route: perfect neighbourhoods, strictly perfect local computation, then homology-sheaf open-cover descent. The local split is a required lower step and does not bypass the unit's realized statement or steps.

Changed in this second reading: added this verification record only; no Lean statements, proofs, imports, or DAG nodes were changed.
