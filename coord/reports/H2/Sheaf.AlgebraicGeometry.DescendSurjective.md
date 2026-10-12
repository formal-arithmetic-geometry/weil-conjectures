## What changed

Proved `AlgebraicGeometry.exists_surjective_of_isLimit` in
`Sheaf.AlgebraicGeometry.DescendSurjective`, with its signature unchanged.
The proof obtains the constructible image by Mathlib Chevalley, computes base-change
images using `Scheme.Pullback.range_map`, constructs the upper-tail equivalence to
`Over (op i₀)`, and applies the existing constructible-containment theorem to the
base-change limit cone. The final pointwise range calculation proves surjectivity.

Added the proof-only import `Mathlib.AlgebraicGeometry.PullbackCarrier`.
Replaced the public import `Sheaf.AlgebraicGeometry.LimitAffineTransition` with
`Mathlib.AlgebraicGeometry.Morphisms.Affine`: the statement needs `IsAffineHom`,
while the limit API is available through the existing proof-only imports. The proof
does not use the project's limit-existence theorem. No definitions or theorem statements changed. The static import-pruning
check found no downstream uses lost by this replacement.
Updated the node's proof, proof dependencies, and proof origin to follow the Lean proof.
The unit's own statements and realized steps remain intact.
The import change is recorded in
`coord/changes/H2-descend-surjective-prune-limit-import.md`; both direct
importers already import the removed module themselves and need no adaptation.

## Proved and sorry left

Proved the item's only sorry: `AlgebraicGeometry.exists_surjective_of_isLimit`
(node `lem-weil-pbc-descend-surjective`). There is no sorry in the delivered module,
and this delivery adds no sorry declarations or modules.

The proof uses the existing theorem
`AlgebraicGeometry.exists_eventually_range_subset_of_isConstructible` in
`Sheaf.AlgebraicGeometry.LimitContainedInConstructible`
(node `lem-weil-pbc-limit-contained-in-constructible`), whose proof is still sorry.
Thus this is a complete reduction to the existing planned dependency, rather than a
claim that the target's full transitive closure is already free of sorry.

Local compilation passed without warnings. The upper-tail and base-change argument
is a fully proved local fact inside the original theorem; no new statement is deferred.

## No longer needed

Removed the direct import `Sheaf.AlgebraicGeometry.LimitAffineTransition`.
The theorem `AlgebraicGeometry.exists_limit_affine_transition` and node
`lem-weil-pbc-limit-affine-transition` are not used in this proof: the limiting cone
and its universal property are already hypotheses. This module remains a transitive
import of the existing constructible-containment dependency, so no claim is made
that it is globally unreachable yet.

Removed `lem-weil-pbc-cartesian-square-pasting` from this node's proof dependencies.
`Scheme.Pullback.range_map` gives the required base-change image directly, so the
separate pasting step and any module implementing it are unnecessary for this proof.
All other original proof dependencies remain used as definitions, Mathlib instances,
or the explicit scheme-over-limit and constructible-containment declarations.

## Where the brief, the DAG or earlier work was wrong

The plan was mathematically sound. Its separate cartesian-pasting step is unnecessary
because Mathlib has the range formula for a pullback map over a monomorphic base map.
The base-change limit API is indexed by `Over (op i₀)`, whereas the containment theorem
requires a directed preorder; the proof explicitly constructs the equivalence from
the opposite of the directed upper tail, rather than assuming these index types coincide.
The local literature tex is absent on this machine; the node's detailed source citations
and proof text supplied the source argument.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered module with the repository version. The theorem signature and all
   existing declarations are unchanged; only the proof, proof-only imports, and matching DAG
   proof metadata differ.
2. Compiled the module with `lcompile.py`; it is clean, has no local `sorry`, forbidden
   declarations, or hollow definitions. The theorem's only transitive `sorryAx` is the already
   open constructible-containment dependency.
3. Checked the route against Mathlib and the library. The direct `Scheme.Pullback.range_map`
   calculation is valid, and the upper-tail equivalence is explicit. No new statement or node
   was added, and the existing split theorem remains exactly the target statement.
4. Verified pruning: `LimitAffineTransition` and the cartesian-pasting node are unused by the
   proof; the unit's realized route remains represented by the limit and constructible-containment
   dependencies. The module's proof docstring was updated to describe the implemented route.
5. Checked the node's `proof`, `proof_deps`, and `proof_origin` against the Lean proof. The
   changed public import is recorded in the existing change record and its downstream importers
   were checked.

Changed the proof docstring to remove the obsolete pasting route and align its numbered steps
with the direct pullback-image and upper-tail-equivalence proof. Corrected the DAG step
numbering and cross-references after the two image steps were combined. An independent
Mathlib grep and library search found no direct theorem replacing the complete argument.


## Second reading by H2

1. **Declarations preserved — pass.** Diffed the sole delivered module against the
   repository version and compared the theorem signature byte for byte. It is identical;
   no definitions or other declarations changed. The public import change has its record
   at `coord/changes/H2-descend-surjective-prune-limit-import.md`. Both direct importers
   already import `LimitAffineTransition` themselves.
2. **Proof and axioms — pass, with an existing open dependency.** Compiled the module
   locally without warnings. It contains no sorry or forbidden declarations. Compiled a
   scratch copy containing the actual proof and explicit `#print axioms` commands: the
   target uses `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The existing
   constructible-containment theorem has `sorryAx`; `isLimitBaseChangeCone` uses only
   standard axioms. No new deferred result or hollow definition is introduced.
3. **Split statements and mathematical validity — pass.** No statements are split off.
   Checked the local containment reduction and the pullback range identity against their
   upstream declarations. The upper tail is nonempty even for a singleton index; its
   directedness needs only a preorder, not antisymmetry. Empty schemes and empty images
   cause no exceptional step: all image arguments are pointwise or vacuous. Independent
   Mathlib grep and library searches found no direct replacement. The upstream
   `exists_range_map_subset_range_app_of_surjective_isLimitMap` requires an open image,
   which finite presentation alone does not supply, so it cannot replace this argument.
4. **Route and pruning — pass after import repair.** The proof uses Chevalley, the direct
   pullback image formula, the proved base-change limit API, and the planned constructible
   containment dependency. The old proof dependency removed is exactly
   `lem-weil-pbc-cartesian-square-pasting`, as the pruning section records. Limit existence
   is supplied by the hypotheses. Read `dag/units/sk-thm-p1.json`: none of its realized
   statements or steps is bypassed or modified. Replaced the unnecessarily broad public
   Mathlib limit import with `Mathlib.AlgebraicGeometry.Morphisms.Affine`; this exposes
   what the statement needs and compiles with the existing proof-only imports.
5. **DAG agreement — pass.** Only `proof`, `proof_deps`, and `proof_origin` differ in the
   node. The dependency list equals the union of the steps' `uses`. The six steps track
   the implemented proof, including transport at the upper tail's initial stage and
   specialization of eventual containment at the supplied stage itself.

Changed only the public Mathlib import and its report/change-record descriptions.
The mathematical proof required no repair; no new statement or node was added.
