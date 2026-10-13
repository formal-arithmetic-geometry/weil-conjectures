## What changed

Reduced `AlgebraicGeometry.singleComplexBaseChange_openRestrictionComparison` without
changing its statement. The main proof now chooses original coordinates, obtains one
restricted coordinate presentation, applies the original stalk hypothesis, and uses
`isIso_stalkComparison_iff_coordinates` to establish the universal restricted condition.
For the arrow, it applies an identity-coefficient restriction calculation, proves by
unfolding that the general restricted coefficient is the identity coefficient followed
by restriction of φ, and uses functoriality and naturality of the target isomorphism.

The unchanged constructions `singleComplexOpenPullbackIso` and
`singleComplexRestrictedCoefficient` were moved verbatim to the new module
`Sheaf.AlgebraicGeometry.SingleComplexOpenRestrictionData` and publicly re-exported.
This avoids an import cycle. The change record is
`coord/changes/single-complex-open-restriction-data.md`. No other existing module is edited.
The two missing calculations are in separate modules, each with one named theorem.
All four modules were checked with lcompile.py. The dry run printed
`OK (dry run): commit ad6d8739de compiles and passes the preflight except for the second
reading, which the second reader writes; nothing pushed.` The sole downstream user,
`SingleComplexTargetLocality`, also compiled unchanged against the sandbox overlay.
The signature comparison found no changed theorem signature, and both moved definitions
have exactly their original signatures and bodies.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.singleComplexBaseChange_openRestrictionComparison`
(node `lem-pc-single-complex-open-restriction-comparison`). No sorry remains in the item.

Added two holes, both strictly smaller parts of the argument:

- `AlgebraicGeometry.singleComplexOpen_coordinates_transport`
  (`lem-pc-single-complex-open-coordinate-transport`): one coordinate presentation and
  pointwise comparison; no stalk-condition hypothesis or base-change-arrow conclusion.
- `AlgebraicGeometry.singleComplexOpen_baseChange_identity`
  (`lem-pc-single-complex-open-base-change-identity`): bare base-change arrow with identity
  coefficient and a natural target comparison; no arbitrary coefficient or stalk condition.

This is a decomposition: one hole closed, two added, net -1. It is not a claim that the
result is free of sorry dependencies. Both pre-existing data definitions remain complete.

Edge cases checked at the statement level: empty U' makes the coordinate conclusion
vacuous; the bare-arrow assertion still concerns zero derived objects. Top opens and
identity φ are covered by the same comparisons. The arbitrary-map case is derived in
Lean from naturality, rather than assumed in an intermediate statement. Neither lemma
adds affineness, boundedness, quasi-coherence, compactness or invertibility assumptions.

## No longer needed

The import-closure comparison found no module pruned from TargetsCheck as a whole.
Seven modules leave this item's own import closure, including the direct-image restriction
module and its K-injective/derived-composition support; they remain reachable elsewhere.
These are relocated planned dependencies of the bare-arrow calculation.
The now redundant public import of
`Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived` was removed from the item;
it is still publicly re-exported through the data module, where its construction is used.

Removed the main module's direct proof imports
`Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction` and
`Sheaf.Algebra.Homology.KFlatPullback`. The first remains a planned dependency of the
bare-arrow lemma; this is an import relocation, not a claim to prune its whole module
from the project's targets. The open-coordinate plan instead uses the more specific
`lem-pc-kflat-open-restriction` and `lem-pc-open-restriction-stalk-extension-iso`.
The generic `lem-pc-kflat-pullback-preservation` is not needed for this open calculation.
The K-injective-restriction step is not needed for transporting a given coordinate
system: Coordinates.N need not be K-injective; restrict its chain map directly.
K-injective restriction remains used by the existing direct-image comparison itself.
No unit statement or realized unit step is bypassed (this unit's realized arrays are empty).
No whole-module pruning beyond the removed direct import edges is claimed.

For completeness, the old proof_deps absent from the new main node are
`lem-pc-ringed-spaces-derived-pullback-composition` and
`def-pc-derived-open-restriction-maps` (now supplied by the shared data node),
`lem-pc-kflat-pullback-preservation` (replaced by specific open restriction),
`lem-sc-derived-k-injective-restrict-open` (not needed for coordinate transport),
and `lem-pc-restrict-derived-direct-image-open` (planned in the bare-arrow node).


## Where the brief, the DAG or earlier work was wrong

The imported dependencies do not themselves state the counit-compatible bare-arrow
restriction equation or the simultaneous four-ring stalk-comparison transport. These
are the missing calculations isolated here, not consequences of an arbitrary functor
isomorphism. The source-open lemma `singleComplexStalkCondition_open` keeps S and S'
unchanged and therefore does not cover this simultaneous target-open restriction.

The ancestor script cannot follow this recently created node's module-valued created.item;
it reports no ancestor, although the node's existing blueprint record explicitly names
`lem-pc-rf-perfect-base-change`. New records follow that recorded ancestor. Blueprint
searches for restriction, open, and base-change/open compatibility found no exact node.
Mathlib searches were run through msearch.py: LeanFinder found ordinary scheme stalk-map
restriction comparisons, Loogle found NatTrans.naturality, and grep found only unrelated
ring base-change results. LeanSearch was unavailable with an internal server error; its
records say unavailable. Sources were read at Stacks Tags 0DJ9, 08HY and 08FE.

## New nodes

`def-pc-single-complex-open-restriction-data` records the two relocated, fully constructed
comparisons, with no new mathematical data or proof hole.

`lem-pc-single-complex-open-coordinate-transport` records restriction of a single
coordinate presentation and the pointwise equivalence needed before coordinate invariance.
Its proof uses the specific existing K-flat open restriction and stalk-extension lemmas.

`lem-pc-single-complex-open-base-change-identity` records the counit calculation for the
bare arrow, with a natural target comparison so the general coefficient case follows by
naturality in the main module. Its proof is precisely the identity-coefficient portion
of the parent's last step.


## Second reading by Q3

1. **Visible declarations: PASS.** Read the repository/sandbox diff. The complete
   signature of `singleComplexBaseChange_openRestrictionComparison` is byte-identical.
   Both relocated definitions, including their signatures and bodies, are byte-identical
   to the original declarations. Their relocation and public re-export are covered by
   `coord/changes/single-complex-open-restriction-data.md`. No other existing Lean
   module changes. Searching both definition names confirms the sole direct user is
   `SingleComplexTargetLocality`; the original public import still supplies both names.

2. **Proof and axioms: PASS as a decomposition.** Independently compiled the four
   modules with `lcompile.py --all`: data 46.8 s, identity 6.5 s, coordinates 5.2 s,
   main theorem 26.9 s; no errors or warnings. Earlier data compiles hit the 60 s
   limit; import-only and original-context scratch checks passed, and the unchanged
   final data module subsequently passed without extra imports or definition edits.
   An independent scratch module printed axioms of all five public declarations.
   Both data definitions use only `propext`, `Classical.choice`, `Quot.sound`.
   The main theorem and the two named intermediate theorems additionally use `sorryAx`.
   Exactly the two reported intermediate theorems contain `sorry`; neither definition
   contains a hole. No forbidden declaration or compiler escape is present.

3. **Split statements: PASS.** Read the Coordinates fields, `stalkComparison`,
   `StalkCondition`, the specific K-flat restriction and stalk extension results,
   and the pinned pullback/base-change constructions. Coordinates.N has no
   K-injectivity field, so restricting its actual chain map suffices. The coordinate
   lemma asserts a pointwise equivalence for one supplied presentation, with no
   stalk-condition assumption or arrow assertion. The identity lemma asserts only
   the bare arrow, with a natural target isomorphism; arbitrary coefficients are
   handled by proved naturality in the main module. These are separate, strictly
   smaller calculations, rather than a renamed copy of the parent. Their docstrings
   describe representative construction, local-ring identifications, and the counit
   computation. Empty source opens make the pointwise statement vacuous; top opens,
   identity coefficients, zero complexes and unbounded complexes introduce no extra
   hypotheses. Read Stacks [0DJ9](https://stacks.math.columbia.edu/tag/0DJ9),
   [08HY](https://stacks.math.columbia.edu/tag/08HY), and
   [08FE](https://stacks.math.columbia.edu/tag/08FE): the last two provide the
   general counit description and derived open restriction used in the calculations.
   Independent msearch queries used “Beck Chevalley mate compatibility with exact
   restriction functors”, `Scheme.Hom.resLEStalkMap`, and derived naturality/tensor
   restriction patterns. Mathlib's derived counit factorization and mate composition
   lemmas are useful tools, but do not instantiate the scheme/open compatibility
   calculation. Searches of lean/ and upstream scheme/derived-category modules found
   no replacement. The existing source-open stalk theorem keeps the base schemes
   unchanged, so does not replace the four-ring target-open calculation. Neither
   remaining hole can be closed by a few-line application of the search results.

4. **Route and pruning: PASS.** Read the main proof from its conclusion downward:
   original coordinates, open transport, the given stalk condition, then existing
   coordinate invariance; identity arrow, definitional coefficient factorization,
   map_comp and b.inv.naturality. Proof imports of the new calculations are plain
   imports. The data module's public imports support its exposed constructions.
   No unused new proof import remains. Every old proof dependency absent from the
   new main node is now explicitly accounted for under No longer needed, including
   dependencies relocated into the data and identity calculations. No whole module
   is claimed pruned from targets. Read sk-thm-picard-semicon.json: its realized
   statement and step arrays are empty. The replacement retains the original
   target-locality argument and changes no unit statement, step, or chapter route.

5. **Nodes: PASS after metadata repair.** The existing node changes only lean,
   proof, proof_deps and proof_origin. Every node's proof_deps equals the union of
   its proof steps' uses; every referenced dependency exists. Checked new-node
   source, statement dependencies, searches, created.item/group, blueprint ancestor,
   chapter/unit and Lean records. Replaced the new nodes' compressed Lean signatures
   with the exact multiline signature text from the theorem/def keyword, as required
   by the signature checker. Corrected proof_origin to say existing
   coordinate invariance is applied, rather than proved anew in the main module.

Second-reading changes: corrected the main theorem's proof docstring to match the
actual coordinate reduction (no K-injectivity requirement on N), repaired the new
nodes' verbatim Lean statement fields and the main proof-origin description, and
completed the explicit removed-dependency list. No proof term, theorem signature,
definition body, or import changed. This remains one original hole closed and two
strictly smaller holes added, net -1; it is a decomposition, not a sorry-free proof.
