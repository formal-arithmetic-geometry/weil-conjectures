## What changed

Completed the proof of
`AlgebraicGeometry.Etale.isIso_strictHenselization_baseChange_modelGlobalHomology`
in `Sheaf.AlgebraicGeometry.StrictLocalBaseChangeModelGlobalHomology`, preserving its
signature and existing docstring. Added proof-only imports of
`WeilConjectures.SixFunctors.BaseChange.DerivedComparison`,
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology`, and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections`.

Five proved private helpers implement the existing node's steps: identification of the
mate, transport of that identification through global homology, invertibility for squares
with isomorphic horizontal edges, invariance of global homology under an isomorphic base,
and transport to an arbitrary cartesian model by horizontal pasting. The last helper
constructs the lift to the canonical square, proves its invertibility by pullback
cancellation, and checks all four factors of the pasted mate. The final theorem applies
these helpers to the canonical strict-henselization square and the existing strict-local
global-homology theorem. No arbitrary data are chosen from an unproved existence theorem.

The earlier sandbox attempt was incomplete and did not compile. Local aliases for the
coefficient category, structural map and canonical square caused expensive kernel
comparisons in the final specialization. Explicit arguments in the final application
avoid those expansions without changing any shared definitions or splitting files.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.Etale.isIso_strictHenselization_baseChange_modelGlobalHomology`
(node `lem-weil-pbc-strict-local-base-change-model-global-homology`).
No sorry remains in the delivered module. No holes were added and none were split off.
The proof uses existing library declarations, including the existing canonical
strict-local global-homology theorem; it does not establish that theorem's dependencies.
All five private helpers are proved.

## No longer needed

None. All original imports remain necessary for the statements or the planned proof.
The node's proof dependencies and unit route are retained; no node or module is pruned.
The three added imports supply precisely the mate calculation, acyclic-complex unit
calculation, and global-sections comparison used in the proof.

## Where the brief, the DAG or earlier work was wrong

No statement or DAG correction was needed. The earlier attempt stopped before proving
the four-factor pasting composite. The existing theorem
`isIso_derivedBaseChangeMapPlus_of_etale` is restricted to module sheaves, so it cannot
replace the general comparison-square proof for the abelian-group coefficients here.
Similarly, `baseChange_eq_derivedBaseChangeMapPlus` needs additional monoidal hypotheses;
the proof instead uses the generic derived-mate characterization from the node's plan.
The new helpers cover all integer degrees and arbitrary complexes, including zero
complexes and empty total spaces; they assume no torsion, properness or new ring condition.

## Second reading by B2

1. The delivered module compiles against the repository baseline, and the target
   declaration retains its exact signature and docstring. Verdict: pass.
2. The target proof has no `sorry`, hollow definition, forbidden declaration, or
   extra axiom source. The five private helpers are genuine intermediate results;
   no new public statement was split off. Verdict: pass.
3. The proof follows the node's stated mate identification, canonical pullback,
   horizontal pasting, homology transport, and global-sections comparison. The
   existing strict-local global-homology theorem is used as the canonical factor.
   Verdict: pass; no shorter applicable library theorem was found.
4. All imports are used by the proof or by the target statement. The three added
   imports are proof-only and are not public. No import or module was pruned.
   Verdict: pass.
5. The unit route is preserved: the canonical strict-henselization square and its
   global-homology theorem remain the central factor, and the node's statement and
   proof dependencies are unchanged. Verdict: pass.

Changed only the target proof and its proof-only imports; no statement, definition,
DAG node, or dependency record required repair.
