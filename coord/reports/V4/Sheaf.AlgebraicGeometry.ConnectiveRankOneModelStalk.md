## What changed

Replaced the sorry in `AlgebraicGeometry.surjective_stalk_homology_of_connective_rank_one_model`
with a complete Lean proof from a strictly smaller residue-component obligation.
Its signature and existing docstring are unchanged. The proof constructs the restricted
single complex, proves its strict perfectness, and uses the existing affine representative
theorem to produce an actual chain map. It then proves the outgoing stalk differential
vanishes, proves epicness of the induced homology map using cycles, and transports this
through localization, restriction and the specified derived isomorphisms.

Added `Sheaf.AlgebraicGeometry.LocalizedHomologyStalkComparison`: the localized additive
stalk functor is concretely constructed; its exactness and natural homology comparison
are proved using the existing forgetful-functor theorem and canonical Mathlib comparisons.
Added `Sheaf.AlgebraicGeometry.RankOneResidueStalkComponent`: the remaining residue
calculation states invertibility of the degree-zero component of an already fixed chain
representative, not surjectivity of the original homology map.

Rechecked the earlier attempt and repaired its delivery metadata: the two new nodes now
each record all three required search kinds. Restored the original `open` command and
qualified the proof-only functor name, so the item has no interface-command change.

All three delivered modules compile without warnings using lcompile.py --all
(5.9 s, 6.9 s, and 15.9 s respectively on the recheck).
The main theorem has a scoped heartbeat increase because composed homology and stalk
functors require substantial definitional-equality checking; each file remains below 60 s.
No existing public import, statement, definition, universe or visibility was changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.surjective_stalk_homology_of_connective_rank_one_model`
(node `lem-sc-connective-rank-one-model-stalk`).

Proved `AlgebraicGeometry.localized_homology_stalk_comparison`
(node `lem-sc-localized-homology-stalk-comparison`) with no new hole.
The private strict-perfectness, epic homology, and natural-isomorphism transport helpers
are fully proved.

Added exactly one hole:
`AlgebraicGeometry.isIso_localized_stalk_component_of_residue_homology`
(node `lem-sc-rank-one-residue-stalk-component`). Its proof is exactly `by sorry`,
and its source and complete proof in words are in its docstring and node.
There is no sorry in the original module or any definition.
This is a decomposition: one upper hole closed and one component hole added, net zero
before any effects of pruning. It is not claimed as a completed residue calculation.
The residue component is strictly part of the argument: it assumes an already supplied
chain map and concludes invertibility of its degree-zero stalk component. The original
module constructs that chain map and proves the differential, homology and transport
steps that convert this component fact to the requested conclusion.

## No longer needed

Removed direct proof imports `Sheaf.Algebra.Homology.ModuleStalkExact` and
`Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback` from the original module.
The original proof no longer uses nodes `lem-weil-pbc-module-stalk-exact` or
`def-pc-module-stalk-functor`: the new exact comparison uses additive stalks directly
and the forgetful-functor exactness result instead. No linear module-stalk functor or
its bundled kernel/cokernel/image characterization is needed for this argument.

`Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback` and its node
`lem-pc-flat-complex-derived-pullback` remain necessary for the new residue obligation,
which imports that module; this import was relocated, not globally pruned.
`Sheaf.AlgebraicGeometry.PerfectAffineMapRepresentative` and its node remain used.
The existing public imports are retained to preserve importer visibility.
Only removal from this argument is claimed: other target routes may still require
ModuleStalkExact and ModuleStalkFunctor.

## Where the brief, the DAG or earlier work was wrong

The listed lemmas do not directly identify the represented residue arrow with the
original one and extract its scalar coefficient. That component comparison is now
an explicit independent obligation; the representation and final transport steps
are actual Lean proofs. No original statement was found false or weakened.

The source references were rechecked at the official Stacks pages for
[Tag 0E62](https://stacks.math.columbia.edu/tag/0E62) and
[Tag 0BCD](https://stacks.math.columbia.edu/tag/0BCD).
The scalar-unit paragraph is the recorded agent elaboration of the residue-field
argument, not a verbatim paragraph of Tag 0E62. Edge cases: an empty open cannot
contain the supplied point; the source and degree-zero target have rank one; higher
terms are arbitrary. The exact localized comparison also covers empty opens whenever
there is a point to evaluate, and arbitrary integer degrees and derived arrows.
The generic epic-homology helper needs neither target connectivity nor boundedness.

The ancestor script cannot follow the old created.item module string and prints None.
The new nodes preserve the explicit old blueprint lineage to thm-sc-theorem-of-cube.
Blueprint searches for residue stalk component and homology stalk restriction returned
no matching imported nodes. The cube unit's realized statement/steps arrays are empty;
its route is unchanged by this local calculation.

## New nodes

`lem-sc-localized-homology-stalk-comparison` records the proved exact localized stalk
functor and the natural derived homology-stalk comparison. It depends on the existing
module-sheaf forgetful exactness result and canonical Mathlib comparisons.

`lem-sc-rank-one-residue-stalk-component` records the remaining component unit
calculation, with a fixed representing equality and no conclusion about the original
homology stalk map. It follows the flat termwise residue comparison and local-ring
unit argument. No change records or forced adaptations are required. The delivery tool permits a
worker dry run with only the second-reading section pending; that section is left
for the independent second reader, as instructed.


## Second reading by V4

1. Compared the original module in full with the repository by diff, and checked the
   entire original theorem signature byte for byte. Verdict: unchanged, including
   hypotheses, conclusion, universes, visibility, existing docstring and public imports.
   The delivery adds proof helpers and two new modules; no change record is needed.
2. Compiled all three files locally in dependency order without warnings or errors
   (6.4 s, 9.2 s, 16.4 s). Compiled scratch copies with explicit `#print axioms`:
   `localizedModuleStalk` and `localized_homology_stalk_comparison` use only `propext`,
   `Classical.choice`, `Quot.sound`; the original theorem and the residue-component
   theorem additionally use `sorryAx`, as expected. The sole literal proof hole is
   the public named residue-component theorem. No hollow definition, custom axiom,
   unsafe declaration or external implementation occurs. Verdict: valid decomposition,
   one original hole closed and one strictly smaller component hole added, net zero.
3. Read the residue lemma and its full verbal proof. Over the local ring, write the
   fixed degree-zero chain component in rank-one bases as multiplication by t.
   Negative terms vanish after termwise flat pullback, so residue H0 injects into
   the degree-zero residue term. Invertibility of residue H0 forces t mod m nonzero,
   hence t is a unit. Arbitrary c and e cause no issue: their residue images remain
   isomorphisms. A field and a complex supported only in degree zero reduce to the
   ordinary nonzero-scalar criterion; a nonunit scalar cannot satisfy ha. Empty U
   has no supplied point; higher differentials do not affect this implication.
   Repeated searches with a local-ring/finite-free-complex formulation in leanfinder,
   loogle for the unit criterion, and rg for stalk/component isomorphisms found only
   component APIs. `finiteLocallyFree_residueField_isIso` requires all points and
   an already computed residue map, so does not close the derived comparison.
   Verdict: true, needed and strictly part of the original argument; no duplicate
   or immediately closable remaining hole was found. Checked the official Stacks
   pages linked above; the scalar argument is an elaboration, as the report says.
4. Read the proof from its conclusion back through restriction, exact stalks,
   homology of cycles, the invertible component, and affine chain representation.
   The generic homology helper is justified by Mathlib's epic cycles-map lemma;
   `epi_homologyMap_of_epi_of_not_rel` cannot apply to the integer cochain shape.
   Public imports of the new modules supply their signatures or concrete definition;
   proof dependencies are plain imports. The two old stalk nodes are both listed
   under No longer needed; flat derived pullback is correctly described as relocated.
   The cube unit's realized statement and step arrays are empty and untouched;
   the local refinement preserves its general-cube route. Verdict: no further
   pruning or shorter applicable proof found; no global pruning is claimed.
5. Checked every delivered node's recorded Lean signature against the whole theorem
   signature, and each proof_deps against the union of its proof-step uses. Read
   the new-node source, search, creation and blueprint lineage fields. Verdict:
   the nodes match the actual reduction and remaining residue calculation.

Changes by the second reader: appended this independent review only. No Lean proof,
statement, definition, import or DAG record needed repair. The remaining residue
comparison is substantial and was not replaced by another hole.
