## What changed

Proved `TopCat.closedPushforwardAbelianStalks` in
`Sheaf.Topology.ClosedPushforwardAbelianStalks`, with its signature unchanged.
Outside the closed subset, `exists_le_germ_eq` shrinks a representative into the
open complement; its inverse-image open is empty, so the sheaf axiom makes its
section group terminal and hence zero. On the subset, Mathlib's
`stalkPushforward_iso_of_isInducing` gives the canonical isomorphism.
Naturality follows by `stalk_hom_ext` and the two germ-composition formulas.
Added proof-only imports `Mathlib.Algebra.Category.Grp.Zero` and
`Mathlib.Algebra.Category.Grp.FilteredColimits` for the zero-object criterion and
germ representatives. Updated the existing node's proof and proof dependencies.
Local compilation succeeds without warnings. The source read was Stacks Tag 00AE,
https://stacks.math.columbia.edu/tag/00AE (the local literature text is absent).
LeanFinder and Loogle searches both found the inducing-map isomorphism and germ API;
ripgrep located the empty-section and abelian-group zero criteria.

## Proved and sorry left

Proved `TopCat.closedPushforwardAbelianStalks`
(node `lem-sc-closed-pushforward-abelian-stalks`): 1 of 1 original sorries.
No sorry remains in the delivered module; no new declarations or nodes are added.
The proof uses only Mathlib and does not rely on any project's admitted theorem.
The cases C empty and C equal to X are covered: on-image or off-image clauses are
vacuous as appropriate, and the empty-section argument applies without any
nonemptiness assumption on the space or subset.

## No longer needed

Removed proof-only import `Sheaf.Topology.PresheafModuleStalkFunctor`.
Removed proof dependency `def-weil-pbc-module-stalk` from this node: its underlying
abelian-group germ facts are used directly from Mathlib, while its project's
linear module-stalk functor is unnecessary. Its statement dependency remains,
since it specifies the meaning of stalks in the mathematical statement.
Consequently this proof does not need the module's admitted
`PresheafOfModules.stalkMap_linear`, `PresheafOfModules.stalkMap_id`, or
`PresheafOfModules.stalkMap_comp`, nor the functor packaging built from them.
No other planned nodes or imports are pruned. The unit's realized statement
`thm-sc-proper-cohomology` is unaffected; no unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original dependency import provided linear stalk-map packaging, whereas
this abelian-sheaf argument needs only Mathlib's existing stalk and germ API.
The stated argument itself and the theorem signature are correct. Mathlib already
proves the planned on-image cofinality argument, so it need not be reconstructed.

## Second reading by U1

1. **Visible declarations.** Diffed the delivered module against the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only proof-only imports and the proof body differ. Verdict: pass.
2. **Proof and axioms.** Compiled the module with `lcompile.py` without errors or warnings. The theorem has no `sorry`, and a probe with `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. The forbidden declaration forms are absent. Verdict: pass.
3. **Split statements and searches.** No statement was split off and no node was added. The proof uses the existing Mathlib APIs `exists_le_germ_eq`, `isTerminalOfEqEmpty`, `isZero_iff_subsingleton`, `stalkPushforward_iso_of_isInducing`, and germ naturality lemmas; the recorded searches support these uses. Verdict: pass.
4. **Pruning and imports.** The two added imports are proof-only and required: removing `FilteredColimits` breaks germ representative elaboration, while removing `Zero` breaks the zero-object criterion. The removed project import and dependency are unused by the proof. The unit route remains intact because the realized unit statement is unchanged. Verdict: pass.
5. **DAG agreement.** The node's proof steps, empty `proof_deps`, and `proof_origin` describe the delivered proof, and the theorem's node and unit are unchanged. Verdict: pass.

No code repair was necessary after this reading; only this review record was appended.

The existing theorem docstring still describes the original five-step mathematical
argument and mentions the former module-stalk dependency. Those references are
historical: the completed proof implements the same argument directly with Mathlib,
as the updated node records. No declaration docstring was rewritten.
The empty subset, the whole space, and the empty ambient space introduce no hidden
nonemptiness requirement: the on-subset clause is vacuous for the empty subset,
and the off-subset clause is vacuous for the whole space. All germ and empty-section
arguments used here apply uniformly.
