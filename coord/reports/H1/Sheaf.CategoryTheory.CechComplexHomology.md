## What changed

Replaced the proposed equivalent componentwise restatement with a complete proof of
`CategoryTheory.cechComplexFunctor_homology`. Its existing signature and docstring are
unchanged. The new proof-only import `Sheaf.CategoryTheory.FormalCoproductEvaluationHomology`
provides exactness of evaluation on a formal coproduct, proved using Mathlib's exact
products of abelian groups. A private constructed `evalHomologyIso` identifies
presheaf homology with objectwise homology. Canonical short-complex homology comparisons
and naturality of the Čech differential assemble the requested isomorphism.

Added the proved helper module and its DAG node. Mathlib's AB import is plain `import`,
since only its proof needs the AB4* instance. Removed the undelivered Components module
and node, and the unchanged duplicate CechResolutionDoubleComplex file from the sandbox.

## Proved and sorry left

Closed the sole original hole: `CategoryTheory.cechComplexFunctor_homology`.
Added holes: none. Sorry left: none. This is a full proof, not a decomposition.

The new theorem `CategoryTheory.formalCoproductEval_preservesHomology`
(node `lem-sc-formal-coproduct-evaluation-homology`) is also proved, as is its
`CategoryTheory.formalCoproductEval_preservesZero` supporting instance.
The private `CategoryTheory.evalHomologyIso` is a real construction with fully proved
naturality; no data is chosen from an unproved existence theorem.

Local compilation of both delivered modules passes without warnings.
Explicit scratch `#print axioms` for the parent theorem, helper theorem, supporting
instance, and private construction gives only `propext`, `Classical.choice`, and
`Quot.sound` for each.

## No longer needed

No original proof-dependency nodes or imports were removed: the repository node had
empty `proof_deps`. No target-reachable module is claimed pruned. The proposed
`Sheaf.CategoryTheory.CechComplexHomologyComponents` and
`lem-sc-cech-complex-homology-components` were never landed and are not delivered.

## Where the brief, the DAG or earlier work was wrong

The first worker called differential-compatible component isomorphisms a strictly
smaller statement. That assertion is equivalent to the entire complex-isomorphism
conclusion and merely relocates its hole. Removed that restatement. The original
parent DAG proof text did not describe the Lean reduction, and its steps did not name
the claimed dependency; rewrote the proof and dependency fields to match the actual
complete argument. The replacement uses existing Mathlib exact products instead of
leaving their homology comparison open.

## New nodes

`lem-sc-formal-coproduct-evaluation-homology` records exactness of evaluation on a
formal coproduct. It is proved by identifying that functor with restriction to a
discrete diagram followed by its limit; Mathlib exact products are the existing
leaf `lem-pc-abelian-groups-exact-products`. This is an ancillary tool within the
unit's Step 2, without changing the unit or chapter route. No change records are
needed because no existing signature or definition changed.

## Second reading by H1

1. Compared both originally supplied existing modules with the repository by `diff`.
The parent theorem signature is byte-for-byte unchanged; no existing definition or
public import changed. The other supplied existing module was identical and was
removed from the delivery. Only the proof and new private construction change in
the parent module. Verdict: pass.

2. Compiled both final modules through `lcompile.py` in import order, without errors
or warnings. There are no sorries or forbidden declarations. Explicit scratch axiom
checks on every delivered declaration, including the private construction, give
only the three permitted axioms. Verdict: pass.

3. Removed the equivalent componentwise restatement. No statement is now split off
with sorry. Checked the new exactness theorem against Mathlib AB4*, searched via
LeanFinder, Loogle, LeanSearch (unavailable), and grep with different queries, and
searched the local and upstream libraries. Mathlib supplies the exact-product piece;
our helper supplies the formal-coproduct identification. Empty products are zero
and exact; singleton products are evaluation; arbitrary products are covered by
Mathlib's discrete-limit exactness. The parent proof also covers q=0 via K.sc q,
and uses no nonempty-cover assumption. Verdict: pass.

4. The final proof takes the shorter Mathlib route, with no new holes. The new proof
imports are plain imports. Public imports in the helper supply only types, products,
zero morphisms, and the homology-preservation class appearing in its interface.
The old node had no dependencies to prune. Read dag/units/sk-thm-picard-cech.json:
its realized entries are currently empty; the proof still carries exactly Step 2's
product-cohomology comparison and does not bypass or replace a unit step.
Verdict: pass.

5. Updated the parent's proof, proof_deps, and proof_origin to describe the three
actual Lean steps. The new node records the exact helper signature, source, complete
argument, existing exact-product leaf, search records, module, chapter, and unit.
Verdict: pass.

Second reading changed: removed the equivalent restatement and closed its mathematical
content using Mathlib exact products; wrote the complete canonical assembly proof,
a proved formal-coproduct exactness helper, matching DAG records, and this report.
