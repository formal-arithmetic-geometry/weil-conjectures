## What changed

`Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalk` combines the new injectivity and
surjectivity component theorems by the constructor of `Function.Bijective`. Its existing
signature and docstring are unchanged. Two new modules state the component obligations.
The second reader expanded their proof docstrings and synchronized the parent node with
the actual constructor proof. The parent no longer imports `PerfectDirectImageBaseChange`
or `PerfectFiniteFreeResidueModel` directly; both remain ordinary proof imports in the
component modules. No statement, definition, public import or existing visibility changed.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.bijective_structureSheafMap_stalk_of_proper_flat_fiber`.
Its body now combines two genuine logical parts of the required conclusion.

Holes added (both public named theorems, each with an entire natural-language proof):

- `AlgebraicGeometry.injective_structureSheafMap_stalk_of_proper_flat_fiber`, node
  `lem-sc-proper-flat-structure-sheaf-stalk-injective`.
- `AlgebraicGeometry.surjective_structureSheafMap_stalk_of_proper_flat_fiber`, node
  `lem-sc-proper-flat-structure-sheaf-stalk-surjective`.

This is a decomposition, not a completed proof of the geometric criterion: one hole closed,
two added, net minus one. No geometric declaration becomes sorry-free in its axiom closure.
The original module contains no remaining `sorry`; the two new modules each contain exactly
one, as `:= by sorry`. The existing choice in the signature chooses a canonically specified
adjunction, whose sectionwise unit formula determines the map; this delivery introduces no
object construction or arbitrary witness chosen from an unproved existence theorem.

## No longer needed

The parent removes the direct imports `Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange`
and `Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModel`. All three old direct proof
nodes (`lem-pc-rf-perfect-base-change`, `lem-sc-perfect-finite-free-residue-model`, and
`lem-pc-module-pullback-adjunction`) are replaced in its `proof_deps` by the two component
nodes. The adjunction module remains a public signature dependency.

These original nodes are still needed by the component obligations; no module or node is
pruned from the transitive target closure. The unit route is retained.

## Where the brief, the DAG or earlier work was wrong

The first worker left the parent DAG describing the full derived argument even though its
Lean proof only combined two components, and called the result proved without clearly
accounting for the additional holes. The split-off docstrings compressed the entire
geometric argument into one sentence. This review repairs that metadata and documentation.
The existing derived interfaces still require substantial comparison work to complete
these obligations; neither has been closed in this review.

The source is the argument of Stacks [Tag 0E62](https://stacks.math.columbia.edu/tag/0E62)
localized at one fixed point, using the local rank-minimal model of
[Tag 0BCD](https://stacks.math.columbia.edu/tag/0BCD). The source's displayed global theorem
assumes the functions condition at every point; these obligations use only the local
argument at the specified point and assert no arbitrary-base-change conclusion.

## New nodes

`lem-sc-proper-flat-structure-sheaf-stalk-injective` records injectivity of exactly the
same chosen stalk map under the original assumptions. It is strictly one component of
bijectivity, and its docstring and node spell out the perfect-model argument and cancellation
of the local unit. Its Lean record reproduces the delivered signature verbatim.

`lem-sc-proper-flat-structure-sheaf-stalk-surjective` records the other component. The
rank-one local unit provides each preimage after the cohomology and adjunction identifications.
Its Lean record also reproduces the delivered signature verbatim. No change record is needed.

## Second reading by X2

1. Compared the delivered original module with the repository by `diff`: the existing
   declaration's signature is byte for byte identical. Only private proof imports and its
   proof body change. The two component modules are new; no definition or target statement
   is altered. Verdict: pass.
2. Compiled every module in dependency order using `lcompile.py`. Checked the two exact
   named holes, absence of forbidden declaration forms and absence of data definitions.
   Explicit `#print axioms` probes permit only the standard axioms and `sorryAx`; the
   parent still depends on the component holes. Verdict: pass as a decomposition only.
3. Read the two source tags and tested the argument on identity morphisms, on a morphism
   over a field with the assumed global-functions isomorphism, and on the empty-fibre
   boundary (the hypothesis cannot hold since the residue field is nonzero). The negative
   fibre cohomology vanishes without conditions on other fibres. Properness plus local
   finite presentation gives finite presentation; the rank-minimal model reduces the
   local degree-zero unit to multiplication by a unit. Each component is a strictly weaker
   conclusion, rather than a renamed bijectivity claim. Searches with different wording
   via leanfinder (flat morphism/nonempty fibre/local ring), loogle (stalk linear maps),
   and local `rg` found no existing component theorem. The search results about flat
   scheme stalk maps concern a different map and do not close the adjunction comparison.
   Verdict: true, necessary component obligations; neither completed.
4. Read the imported perfect-direct-image, finite-free-residue-model and tensor-adjunction
   declarations and the unit `sk-prop-av-cube`, including its `realized` field. The parent
   now has only its signature imports and the two component proof imports. Its removed
   direct imports remain available exactly where the planned geometric work is left.
   No realized unit step is bypassed or modified. Verdict: pass; transitive pruning none.
5. Checked all node identities, sources, statement dependencies, creation and blueprint
   records, and the new multiline Lean signatures. The parent proof and dependency list
   now cite precisely the two component applications; each new node retains the original
   geometric proof steps and their dependency union. Verdict: pass after repair.

Changes by this second reader: completed the new theorem docstrings, corrected the parent
proof/dependency/origin metadata, made the new Lean signature records verbatim, removed the
parent's unused direct proof imports, and replaced the report with explicit hole accounting.
