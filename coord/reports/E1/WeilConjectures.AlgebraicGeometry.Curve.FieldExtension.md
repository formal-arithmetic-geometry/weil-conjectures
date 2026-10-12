## What changed

Replaced the invalid `sepClosed_passage_comparison` with
`AlgebraicGeometry.IsCurve.sepClosed_geometric_comparison` in
`Sheaf.AlgebraicGeometry.Curve.SepClosedComparison`. The new statement constructs the
geometric square over algebraically closed fields and its universal-homeomorphism vertical
maps; it has no sheaf, degree, or algebraically closed cohomology hypothesis.

Added and proved `AlgebraicGeometry.Etale.pullback_forget_modules_iso` in
`Sheaf.AlgebraicGeometry.EtalePullbackForgetModules`, using Mathlib's left-Kan-extension and
sheafification comparison isomorphisms. Its imports are only the public modules needed for
its signature and coefficient instances; redundant Mathlib imports were removed.

Rewrote the proof of
`AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isSepClosed_of_isAlgClosed`:
choose the geometric square, pull back the torsion module sheaf, apply the hypothesis H to
the bottom proper curve, transport coefficients by the proved isomorphism, use the existing
`Etale.cohomologyPullbackFunctorial` and `upperStarComp` to identify the two composites,
and cancel the bijective vertical maps from `Etale.cohomologyMap_bijective`.
All three added imports in the source module are plain proof-only imports. Every existing
signature, definition, public import, and docstring is unchanged.

## Proved and sorry left

One of one previously open declarations in the repository's version of the item now has a
proof body with no direct sorry:
`AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isSepClosed_of_isAlgClosed`
(node `lemma-weil-pbc-curve-separably-closed-passage`). All three original theorem bodies in
the item contain no sorry; the other two bodies were already proved in the repository.

The new `AlgebraicGeometry.Etale.pullback_forget_modules_iso` is proved and its printed
axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`.

Exactly one new sorry remains:
`AlgebraicGeometry.IsCurve.sepClosed_geometric_comparison`
(node `lemma-weil-pbc-curve-separably-closed-passage-comparison`). It is a public named
theorem with a complete natural-language construction in its docstring, sourced to
[Stacks Tag 0A5E](https://stacks.math.columbia.edu/tag/0A5E).
The item remains dependent on this obligation and on existing open dependencies, including
the library's functoriality and algebraically closed core; its printed axioms include
`sorryAx` as well as the three permitted axioms. This is a reduction, not a fully
axiom-closed proof of cohomological invariance.

All three delivery modules compile together locally, with no errors or warnings.
Scratch-copy `#print axioms` checks were run for all three original theorems and both new
theorems: no other axioms occur, and the scratch files are removed from the delivery.

## No longer needed

The invalid declarations `sepClosed_passage_injective`, `sepClosed_passage_surjective`,
and `sepClosed_passage_comparison` and the former component-node proposals are absent.
The replacement is a genuine geometric obligation, not arbitrary bijections of the
cohomology groups. No existing library module or unit realization is pruned.

Every old dependency removed from the passage node's direct `proof_deps` is listed here:
`def-pc-separably-closed`, `def-weil-algebraic-closure`,
`def-weil-relative-algebraic-closure`, `lem-weil-pbc-relative-algebraic-closure-algclosed`,
`lem-pc-kbar-pure-insep`, `def-pc-base-change`, `def-weil-universal-homeomorphism`,
`lem-weil-pbc-cartesian-square-pasting`, `lem-pc-homeo-pure-insep`,
`def-weil-pbc-cohomology-pullback`, `lem-weil-pbc-proper-base-change`,
`def-kun-topological-krull-dimension`, and `def-pc-fibre-product`.
The geometric ingredients remain dependencies of the new geometric node or of its
statement; the definitions remain in statement dependencies as appropriate. Thus their
removal from the parent's direct edges does not assert they are globally unreached.

Removed the three redundant explicit Mathlib imports from the new coefficient module
(`ModuleCat.Colimits`, `Sites.PreservesSheafification`, and
`Functor.KanExtension.Preserves`): the two public imports already provide them.
No original public import was removed or changed.

## Where the brief, the DAG or earlier work was wrong

The first worker's replacement was still equivalent to the entire original conclusion:
an arbitrary bijection g with bijective g composed with the original map exists precisely
when the original map is bijective (the identity supplies the reverse implication).
Its signature did not specify any algebraic closure, scheme map, or comparison square,
so its docstring's claimed geometric content was not present in the Lean statement.
This second reading removed that restatement and wrote the actual cohomological reduction.

The existing repository already proves the algebraically closed theorem using the reduced,
constructible core; that proof was retained unchanged and its unchanged node is omitted
from this delivery. The unit `sk-thm-p1` still passes through the curve calculations and
then the separably closed passage, exactly as its `realized` record requires.

## New nodes

`lemma-weil-pbc-curve-separably-closed-passage-comparison`: a geometric comparison square
with universal-homeomorphism projections and an algebraically closed proper curve as its
bottom left object. This is the sole new open proof. Its proof steps use the existing
algebraic-closure, pure-inseparability, pullback-pasting, and proper-base-change nodes.

`lemma-weil-pbc-etale-pullback-forget-modules`: the proved isomorphism between module
pullback followed by forgetting and abelian pullback. It applies to every scheme morphism
and module sheaf; it has no curve or torsion assumptions. The proof specializes Mathlib's
Kan-extension and sheafification comparison isomorphisms. The source is
[Stacks 03D3](https://stacks.math.columbia.edu/tag/03D3) and
[Stacks 03D7](https://stacks.math.columbia.edu/tag/03D7).

Searches were independently repeated using LeanFinder, Loogle, and Mathlib grep, and the
upstream and Sheaf sources were searched for alternative names. No complete existing
geometric-square or coefficient-comparison declaration was found. LeanSearch was called
for both new nodes and returned Internal Server Error; this is recorded as unavailable,
not as a no-match result. The generic Mathlib comparison isomorphisms found are used.
No existing statement or definition changes, and no change record is required.

## Second reading by E1

1. Compared the source module with the repository by diff and by raw declaration-signature
   slices: all three existing signatures are byte for byte unchanged. No definition or
   public-import change; the additions are proof-only imports. Verdict: pass.
2. Compiled all three modules in import order. Checked every theorem with scratch-copy
   `#print axioms`, scanned the delivery for forbidden declarations and for sorry in data,
   and removed the scratch copies. Only the named geometric theorem has a new direct
   sorry; no extra axioms beyond the three allowed and existing/open `sorryAx`. Verdict:
   pass as a partial reduction, with the remaining dependency explicitly reported.
3. The geometric statement is independent of the target cohomology theorem and true by
   the compatible algebraic-closure construction in 0A5E. Checked characteristic zero
   (closures give identity comparisons), positive characteristic (pure inseparability),
   identity field extension, empty curves, dimension-zero curves, and arbitrary torsion
   coefficients/degrees. The coefficient statement is fully proved for arbitrary scheme
   morphisms, independently of all curve/cohomology hypotheses. Repeated searches find
   no duplicate declaration. Verdict: pass after replacing the equivalent restatement.
4. Kept the repository's existing shortest algebraically closed reduction. Used the
   existing functoriality declaration instead of splitting another cohomology obligation,
   and proved the coefficient comparison from Mathlib. Removed redundant new imports.
   Listed every old direct proof edge replaced; no unit or module was bypassed. Read
   `dag/units/sk-thm-p1.json` and its preserved `realized` route. Verdict: pass.
5. Checked the two new nodes against their exact Lean signatures, sources, recorded
   searches, and proof steps; each `proof_deps` is the union of the steps' uses. Updated
   the parent node to describe the actual bottom-map/vertical-map reduction and its
   named dependencies. No new helper cites the parent as a proof dependency. Verdict:
   pass after repairing the previous comparison node and adding the proved coefficient
   node.

Second reading changed the equivalent helper into a geometric square theorem, added and
proved the coefficient isomorphism, wrote the real cohomological comparison and cancellation
in the original theorem, minimized the new imports, and repaired the nodes and this report.
