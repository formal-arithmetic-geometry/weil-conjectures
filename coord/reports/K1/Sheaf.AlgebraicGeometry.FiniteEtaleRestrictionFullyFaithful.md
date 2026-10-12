## What changed

Proved `AlgebraicGeometry.Scheme.fullyFaithful_pullback_finiteEtale_of_henselianRing`
with its original statement unchanged. Added proof-only imports of the existing
henselian clopen comparison and three new, completely proved geometric modules:
`Sheaf.AlgebraicGeometry.FiniteEtaleGraphClopen`,
`Sheaf.AlgebraicGeometry.FiniteEtaleGraphBaseChange`, and
`Sheaf.AlgebraicGeometry.FiniteEtaleClopenRestrictionRank`.
The target proof explicitly proves rank-one reflection, injectivity and surjectivity
on morphisms, and the conversion to a FullyFaithful structure. The existing docstring,
public imports and public interface of the item are preserved. Updated the item's
proof plan and added nodes for the three new proved lemmas; no statement or definition
of the existing library changed.

## Proved and sorry left

Closed the item's only sorry:
`AlgebraicGeometry.Scheme.fullyFaithful_pullback_finiteEtale_of_henselianRing`
(node `lem-weil-pbc-finite-etale-restriction-fully-faithful`). Also fully proved:
`AlgebraicGeometry.Scheme.finiteEtale_graph_clopen`,
`AlgebraicGeometry.Scheme.finiteEtale_graph_base_change`, and
`AlgebraicGeometry.Scheme.finiteEtale_clopen_restriction_rank`.
No sorry remains in any of the four delivered modules; none is split off.
The proof uses the existing theorem
`AlgebraicGeometry.Scheme.henselian_clopen_restriction`
(node `lem-weil-pbc-henselian-clopen-restriction`) as its sole remaining mathematical
proof gap below this delivery. The existing theorem is unchanged and is not copied
into the sandbox. All three new lemmas use only Mathlib. Empty schemes, empty clopens,
and a non-surjective closed-fibre map are included; the rank argument uses equality
of clopen inverse images rather than surjectivity on points.

## No longer needed

No imports removed from the original module and no mathematical nodes pruned.
The original proof dependencies for section immersions, composition, and closed
immersions are now used through the new graph and clopen-rank lemmas rather than
as direct edges of the item's node. The removed direct edges are
`lem-weil-pbc-etale-section-clopen-immersion`,
`lem-weil-pbc-etale-composition-cancellation`,
`lem-weil-pbc-closed-immersion-finite`, and `lem-weil-pbc-finite-composition`.
All four remain used transitively by the new proved nodes; no node or module is
claimed as pruned. During import minimization, omitted redundant proof imports of
Mathlib's Proper and Preimmersion modules from the new geometric modules; the
required instances are already available from their statement imports.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The DAG's corrected clopen/rank route works,
and no unit statement or realized unit step is bypassed. The closed fibre need
not be surjective; the explicit rank-one reflection proof compares its inverse
image with that of the whole base, as the corrected plan requires. LeanSearch
returned an Internal Server Error; this is recorded as unavailable, not as a
negative search result. LeanFinder, Loogle and Mathlib source searches supplied
the ingredients. No new lemma merely restates full faithfulness: each is a general
geometric lemma, independently proved from Mathlib.

## New nodes

`lem-weil-pbc-finite-etale-graph-clopen` records the proved equivalence between raw
morphisms over a base and clopen graphs projecting isomorphically. Its module is
`Sheaf.AlgebraicGeometry.FiniteEtaleGraphClopen`.

`lem-weil-pbc-finite-etale-graph-base-change` records the proved cartesian product
projection square and the exact equality of graph images under inverse image.
Its module is `Sheaf.AlgebraicGeometry.FiniteEtaleGraphBaseChange`.

`lem-weil-pbc-finite-etale-clopen-restriction-rank` records finiteness and etaleness
of clopen restrictions and their rank compatibility under an arbitrary cartesian
square. Its module is `Sheaf.AlgebraicGeometry.FiniteEtaleClopenRestrictionRank`.

No change record is needed: all existing signatures, definitions and public imports
are unchanged. The new results are proved, and no new sorry is introduced.


## Second reading by K1

1. Compared the target module with the repository using `diff -u`. The existing
   theorem signature and docstrings are byte-for-byte unchanged; the only additions
   are proof imports, the proved private rank-reflection helper, elaboration options,
   and the proof. There is no definition or target change and no change record needed.
2. Compiled all four modules in import order with `lcompile.py --all`: no errors or
   warnings. Scanned all delivered Lean for forbidden declarations and `sorry`: none.
   A scratch copy with `#print axioms` checked all four public theorems. The three
   new theorems use only `propext`, `Classical.choice`, and `Quot.sound`; the item also
   uses `sorryAx` through the pre-existing `henselian_clopen_restriction`. That gap is
   explicitly reported and has not been moved into a new theorem.
3. No statements were split off with sorry. Read the three new statements and their
   complete proofs: graph_clopen assumes only q finite étale, not p étale; the inverse
   restricted projection recovers a graph, including empty U and V. graph_base_change
   allows arbitrary i and proves both the product square and graph-image equality by
   pullback universal properties, without surjectivity on points. The restriction-rank
   lemma includes empty W and arbitrary base change, using the restricted cartesian
   square and `finrank_of_isPullback`. Source search with different graph/section/clopen
   words and an additional LeanFinder search found ingredients, not these combined
   statements. Inspected `etale_graph_clopen` and `etale_graph_preimage` in
   EtaleGraphSectionExtensionMap: these are still sorry and concern étale site objects
   or change of an object over a fixed base; they do not give the general equivalence
   or simultaneous base-change square here. The compactification graph compatibility
   theorem concerns compactifications and gives a morphism equality, not this range
   identity. None of the new results merely renames the item.
4. Read the corrected old DAG plan and compared it with the proof from the top down.
   The proof retains the clopen-graph/rank route; `rank_one_of_clopen_injective` compares
   the rank-one locus with the whole base, so a non-surjective closed fibre causes no
   false inference. The listed Mathlib matches supply section immersion, finite/étale
   composition, cartesian pasting and finite-flat rank criteria directly. All imports
   serve statements or proofs; the new helper imports into the item are plain imports.
   Checked sk-thm-p1.json `realized`: no listed unit statement or step is bypassed or
   removed. Expanded No longer needed to name all four removed direct DAG edges and
   explain their continued transitive use; no mathematical node is pruned.
5. Read all four delivered node files and the old dependencies' statements and
   Mathlib matches. Their proof steps and dependency unions describe the actual Lean
   constructions, including clopen comparison on both U and P, the restricted rank
   square, and conversion from raw over-base morphisms to FullyFaithful. New nodes
   have source, searches, creation/blueprint metadata and Lean records matching their
   declarations; the existing node changes only the permitted proof fields.

Repairs: added source and blueprint references to the three new module docstrings,
and clarified removed direct dependency edges in No longer needed. No Lean proof,
statement, definition, import or node needed correction.
