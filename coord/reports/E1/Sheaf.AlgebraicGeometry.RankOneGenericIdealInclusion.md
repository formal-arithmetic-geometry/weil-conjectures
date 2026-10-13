## What changed

Proved the unchanged `rank_one_generic_ideal_inclusion` by first identifying the
stalk of `i_*O_W` with the given residue-field line, then extending that prescribed
stalk embedding from a nonzero ideal. The extension's equality on stalks, the
integral-ideal generic-stalk theorem and natural closed-pushforward comparison
prove the resulting generic map invertible.

The new module `Sheaf.AlgebraicGeometry.RankOneGenericIdealInclusionAux` now proves
`rank_one_generic_structure_stalk_iso` using Mathlib residue-field lifting,
`Module.nonempty_linearEquiv_of_finrank_eq_one`, and the existing closed-pushforward
comparison. The returned duplicate private `unit_stalk_iso` has been removed.
The proof now imports `Sheaf.AlgebraicGeometry.IdealModuleProductStalk` and
extracts the structure-stalk identification from the existing public theorem
`AlgebraicGeometry.Scheme.ideal_module_product_stalk`, applied to the identity
inclusion. The reported existing helper is private, so it cannot be called
directly through an ordinary import. This uses its public containing theorem
without changing any library interface.

Added `Sheaf.AlgebraicGeometry.GenericIdealStalkEmbeddingExtension`, stating the
remaining prescribed-map extension step. All added imports in the existing target
module are proof-only. No existing signature, definition, visibility or public
import changed. Updated the target node's proof route and both new node records.

## Proved and sorry left

Closed the original hole:
- `AlgebraicGeometry.Scheme.Modules.rank_one_generic_ideal_inclusion`
  (`lem-pc-r2-rank-one-generic-ideal-inclusion`).

Also fully proved the new statement:
- `AlgebraicGeometry.Scheme.Modules.rank_one_generic_structure_stalk_iso`
  (`new-rank-one-generic-ideal-inclusion-aux`), with only `propext`,
  `Classical.choice`, and `Quot.sound`.

Added one hole, the only direct `sorry` in the delivered modules:
- `AlgebraicGeometry.Scheme.Modules.generic_ideal_stalk_embedding_extension`
  (`new-generic-ideal-stalk-embedding-extension`). It has a complete source-based
  natural-language proof in its docstring and its own module and node.

This is a decomposition: one original hole closed and one lower hole added, net
zero. The target still depends transitively on this extension hole. The first
worker's `rank_one_generic_ideal_inclusion_aux` restatement was removed entirely;
it is neither delivered nor counted as an original-library hole closed.

## No longer needed

Removed the copied private
`AlgebraicGeometry.Scheme.Modules.unit_stalk_iso` and its entire proof from the
auxiliary module. No new import is unused: `IdealModuleProductStalk` supplies
the existing public comparison.

The new target proof does not use these old proof dependencies:
- `lem-weil-pbc-coherent-generic-point-ideal-inclusion`, module
  `Sheaf.AlgebraicGeometry.CoherentGenericPointIdealInclusion`;
- `lem-pc-stalk-direct-sums`, module `Sheaf.Topology.StalkDirectSums`.

Neither module was originally imported directly by this target file, so no
existing import line was removed. They are pruned from this node's proof route;
this does not assert that they are unreachable from every other target.
The old closed-pushforward and integral-ideal generic-stalk dependencies remain
and are applied explicitly. No unit realization is bypassed: the unit record
`dag/units/sk-thm-picard-coherence.json` has empty realization lists.

## Where the brief, the DAG or earlier work was wrong

The landing return correctly identified the copied `unit_stalk_iso` as a
duplicate of the private library helper in `IdealModuleProductStalk`. Repaired
by deleting the helper and using `ideal_module_product_stalk` instead. The
auxiliary node now records `lem-weil-pbc-ideal-module-product-stalk` as a proof
dependency. All three repaired modules compile through `lcompile.py --all`.
The earlier second-reading text records the prior delivery; the current second reading below checks this repair.

The first worker's auxiliary had the original hypotheses and essentially the
entire conclusion, merely wrapped in a singleton-coproduct isomorphism. It was a
restatement, not a strict part of the argument, and its node did not update the
target's route. This delivery replaces it with a proved local linear-algebra
statement and a genuinely separate extension step taking an arbitrary prescribed
injective stalk map, with no target-rank or annihilation hypothesis.

Importing the existing generic-point inclusion theorem would create a cycle:
`CoherentGenericPointIdealInclusion -> CoherentGenericPointClosedDescent ->
ClosedImmersionPushforwardAnnihilated -> AffinePushforwardBaseChange ->
WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism ->
WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex ->
IntegralIdealProperCohomology -> IntegralIdealComparisonFiltrations ->
IntegralIdealCommonSubmodule -> RankOneGenericIdealInclusion`.
The existing integral ideal-map construction also reaches that cycle through
`CoherentHomsOverOpen`. Their declarations therefore cannot be imported here.
The new extension statement records the remaining source-based construction
without importing the cyclic cohomological route.

## New nodes

`new-rank-one-generic-ideal-inclusion-aux`: a fully proved identification of a
compatible generic residue-field line with the closed structure-pushforward
stalk. It constructs no global ideal inclusion and needs no coherence or
Noetherian hypothesis.

`new-generic-ideal-stalk-embedding-extension`: extension of a prescribed injective
stalk map by a nonzero ideal, with the equality on stalks. Its proof follows
[Tag 01Y4](https://stacks.math.columbia.edu/tag/01Y4),
[Tag 01YB](https://stacks.math.columbia.edu/tag/01YB), and the injection argument in
[Tag 01YE](https://stacks.math.columbia.edu/tag/01YE). No existing statement has
these inputs and the prescribed-map equality; the existing general lattice
construction instead constructs its own stalk map and has the import cycle above.

No change record is needed: no existing interface changed.

## Earlier second reading (a previous round; superseded)

1. Compared every delivered existing module with the repository using `diff`.
   The target signature is byte for byte unchanged, including `hGann` and
   `hGrank`. Its existing docstring, visibility, and public imports are unchanged.
   All other delivered modules and nodes are new. Verdict: pass.
2. Compiled all three modules locally through `lcompile.py`, in import order,
   without errors or non-sorry warnings. Explicit scratch `#print axioms` checks
   showed only the three standard axioms for the new residue-line theorem;
   the target additionally uses `sorryAx` through the named extension theorem.
   No forbidden declaration, hollow definition, or arbitrary data selected in
   a definition occurs. Verdict: pass as the reported decomposition.
3. Checked the extension statement against Tags 01Y4, 01YB, and 01YE and reviewed
   its complete docstring argument. Its prescribed map must be injective; thus
   zero G cannot satisfy its hypotheses. For identity i over a field, choose
   J = the unit ideal and recover the prescribed embedding. An empty W is
   excluded by integrality. For a target of rank greater than one the extension
   still works, with no generic-surjectivity conclusion. Searches with fresh
   leanfinder, loogle, and grep queries and searches of the project sources found
   no duplicate prescribed-map extension theorem; leansearch was unavailable
   and this is recorded honestly. The remaining statement is the geometric
   extension step only, not a renamed target. Verdict: pass.
4. Took the shorter rank-one route: prove the generic line identification first,
   without constructing or comparing finite direct sums. Removed the first
   worker's unproved singleton-coproduct restatement. Kept signature imports
   public and proof-only imports plain. Reported every unused old proof_dep,
   and checked the unit's realized fields. Verdict: pass.
5. Updated the target node to the proof actually written. Both new nodes have
   the exact Lean signatures, correct dependency unions, sources, searches,
   provenance, chapter and unit. The target's old statement and statement
   dependencies stay unchanged. Verdict: pass.

Changed in this second reading: replaced the restatement with a proved generic
stalk isomorphism; split off only the prescribed-map extension; wrote the real
stalk-composition proof; repaired the nodes, pruning list, and hole accounting.


## Second reading by E1

1. Compared the delivered target module with the read-only repository using diff;
   also compared its theorem signature byte for byte by script. Only four plain
   proof imports and the proof body differ. Existing public imports, signature,
   hypotheses, visibility and docstring are unchanged. The other two modules are
   new. No definition or target statement changes. Verdict: pass.
2. Independently compiled all three modules through lcompile.py --all, with no
   errors or warnings. Scratch copies with explicit #print axioms confirm that
   rank_one_generic_structure_stalk_iso uses only propext, Classical.choice and
   Quot.sound, including its use of ideal_module_product_stalk. The target and
   extension also use sorryAx, as reported. Exactly one direct sorry remains,
   in generic_ideal_stalk_embedding_extension. No forbidden declarations, hollow
   definitions or data chosen from unproved existence theorems occur. Verdict:
   pass as a decomposition, not a fully proved target.
3. Read Stacks Tags 01Y4, 01YB and 01YE independently. The extension's coherent
   source permits local stalk-map extension; Noetherianity permits clearing
   denominators globally, and the integral ideal source has no generic torsion.
   Thus its word proof establishes precisely the prescribed-map equality and
   monomorphism stated. Over an identity closed immersion of a field, take the
   unit ideal and the prescribed map. Zero G cannot admit the required injection;
   an empty W is excluded by integrality. Targets of higher generic rank remain
   allowed without an invertibility conclusion. This is the geometric extension
   step, strictly separate from the proved residue-line identification and final
   invertibility calculation. Fresh leanfinder, loogle and grep searches, and
   source inspection of CoherentStalkMapExtends, CoherentHomsOverOpen and
   CoherentIntegralGenericIdealConstruction, found no directly usable duplicate.
   The existing construction chooses its own finite-rank map and does not assert
   the prescribed-map equality. Its cyclic import route prevents a short closure
   of the remaining extension theorem in this item. Verdict: pass.
4. Read the proof from the target downward. The residue-line equivalence is
   proved using Mathlib and the existing public structure-stalk comparison,
   without duplicating the private unit_stalk_iso. The target correctly transports
   the ideal inclusion's bijectivity through the natural closed-pushforward
   comparisons and composes with the chosen isomorphism. Its four added imports
   and the auxiliary module's three proof imports are plain and used. Both unused
   old proof_deps are listed under No longer needed; the other two remain used.
   Checked sk-thm-picard-coherence.realized (empty statement and step lists);
   no realized unit route is bypassed. Verdict: pass.
5. Checked every delivered node's Lean signature against its source and every
   proof_deps list against the union of the proof steps' uses. The target route
   matches the actual reduction. The auxiliary route records the reused public
   ideal_module_product_stalk, not the deleted duplicate helper. Both new nodes
   have provenance, source, searches, chapter, unit, blueprint and exact Lean
   records. The extension's dependencies describe its outstanding word proof,
   rather than claiming those cyclic modules are imported already. Verdict: pass.

Changed in this second reading: refreshed the extension node's independent
Mathlib searches and the report's review of the repaired public-comparison route.
No Lean repair was needed. Hole accounting remains one original hole closed,
one new proved auxiliary and one split-off hole added: net zero.
