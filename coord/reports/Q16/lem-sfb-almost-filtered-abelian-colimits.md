# Q16 stage-1 delivery: lem-sfb-almost-filtered-abelian-colimits

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-almost-filtered-abelian-colimits.json`: statement node, now split in seven steps. The statement, statement dependencies and inherited blueprint ancestry are unchanged. The whole item is not a Mathlib leaf. No new nodes are needed; the split reuses two existing Mathlib leaves and the existing filtered-components node.
- `citations.json`: a verbatim statement quotation for every citation in every numbered proof step.
- `searches.jsonl`: actual Q16 msearch records. The item's earlier O4 searches remain unchanged in its JSON; Q16 searches were appended, not substituted for that history.
- `report.md`: this report. `write_split.py` is only a sandbox preparation script, not a delivery file.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint tag, almost-filtered terminology and categorical colimits did not find a declaration proving this item. Mathlib results are not project attachments.

## WANTED

None. All mathematical sources used here are available in `literature/stacks-project/`.

## Corrections and scope

The imported statement is correct, including the empty category. It had no proof. The split now supplies the argument of Algebra Tag 04B0 (lemma-almost-directed-colimit-exact), together with explicit additivity, existence and finite-limit checks. Neither nonemptiness nor connectedness of the whole category was introduced. No statement dispute, source error, route replacement, or Lean edit is involved.

I read the node's chapter record and unit `sk-thm-sf-ctf-stability`, SETUP's three levels, and the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/` section and direct-images proof. This is a generic prerequisite already on the lower-shriek chain, not the unit's key node. The blueprint ancestor tool prints `None`; I retain the inherited `blueprint.from.node = null` and its already specified place/via chain. Whole-blueprint searches for “almost filtered”, “filtered colimits”, “abelian groups” and “direct sums” found no equivalent blueprint theorem. `same_as` stays empty. Chapter and unit records are unchanged.

## Not duplicates

There are no new nodes. In particular I cite, rather than recreate, `lem-sfb-almost-filtered-components` (002X), `lem-weil-pbc-filtered-colimits-commute-finite-limits` (002W, including its explicit abelian-group clause), and `lem-weil-pbc-filtered-colimit-abelian-groups-exact` (00DB). The existing almost-filtered SET colimit node is not used to claim finite-product preservation in Ab: its conclusion is about fibre products and equalizers of sets and would not justify the present statement.

## Mathlib searches

All Q16 Mathlib searches ran through the required msearch command and their returned records are in searches.jsonl. I used LeanFinder with both a disjoint-union-of-filtered-categories phrasing and an almost-directed/empty/disconnected phrasing, Loogle with `"colim", "PreservesFiniteLimits"`, LeanSearch with the two span/coequalization conditions, and grep for componentwise filteredness and the AB axioms. I read Mathlib/Algebra/Category/Grp/AB.lean:29-30,32-66. The filtered-colimit instances at 36-56 require `IsFiltered J`; the generic colimit-additivity instance and AB4 do not give the decomposition from this item's hypotheses. `AddCommGrpCat.hasColimit` returned by the searches covers only existence. Thus the whole statement needs the decomposition and assembly argument and is not a one-line specialization of one of those hits. No search service was unavailable in this run.

## Review by Q16

I read Algebra Tag 04B0, label lemma-almost-directed-colimit-exact, from its statement through the full proof. It decomposes into filtered categories, uses exactness on each component, and finishes with coproduct exactness, even for an empty family. I also read Categories Tag 002X, label lemma-split-into-directed; Algebra Tag 00D5, label lemma-colimit, including its universal-property proof; Algebra Tag 00DB, label lemma-directed-colimit-exact, including the homology statement and element proof; and Categories Tag 002W, label lemma-directed-commutes. The latter source states the Set version, whereas the existing DAG node explicitly states the Ab version as well and is a reviewed Mathlib leaf. I checked that stronger clause against Mathlib's filtered finite-limit instance in AB.lean:54-56. I read every cited node's full statement, not just its source tag.

Step 1 uses only the colimit definition. It constructs a finite-support direct sum, quotients by the arrow relations, and explicitly factors each cocone by finite summation. This is the two-line quotient universal-property argument of 00D5, written with all category arrows instead of preorder relations; no theorem for arbitrary categories is silently inferred from a preorder theorem. The generators vanish exactly by the cocone equations, and uniqueness follows because the summand images generate. This establishes the existence clause directly, so making a new existence node would merely restate a clause of the item. Smallness ensures that all the tuples, generators and quotients belong to the stated coefficient universe.

Step 2 again uses exactly the uniqueness clause of the colimit definition. Both candidate maps have the same composites with every structure map; their equality and the analogous zero-map calculation prove additivity. No preadditivity theorem or left-adjoint exactness assertion is assumed.

Step 3 uses the statement of `lem-sfb-almost-filtered-components`: it actually supplies a small partition, no cross-part arrows, and nonempty filtered full subcategories. Its hypotheses are verbatim the item's (a) and (b). I do not apply a filtered-colimit theorem directly to the possibly empty or disconnected category I.

Step 4 uses just the colimit universal property to construct the direct-sum identification. The absence of cross-part arrows comes from step 3. Each cocone on I is one cocone on each part, and finite summation assembles their unique maps; this proves the comparison and its naturality on the structure maps. In particular the comparison respects the arrows of the finite-limit diagrams and short exact sequences later used. This is a routine universal-property calculation, not an uncited comparison lemma.

Step 5 uses precisely the Ab clause of `lem-weil-pbc-filtered-colimits-commute-finite-limits`. The necessary smallness and nonempty filteredness have already been established for each I_j. It gives zero, product and equalizer comparisons. The pointwise construction of these limits in the diagram category is written out: the unique objectwise factors are natural by uniqueness. No presheaf-on-a-site result with different hypotheses is substituted.

Step 6 uses no extra theorem: finite-support tuples identify the direct sum of pairwise products with the product of direct sums, since a union of two finite supports is finite; equalizer membership is checked coordinatewise. The zero group is also checked. A finite limit is then explicitly the compatible subgroup of a finite product, expressed as an equalizer of two finite-product maps over the arrows. This verifies preservation of all finite limits, rather than only kernels. In particular the empty limiting diagram is covered. The argument only asserts commutation with FINITE limits; an infinite product would invalidate the finite-union-of-supports argument.

Step 7 uses the statement of `lem-weil-pbc-filtered-colimit-abelian-groups-exact`, which asserts exactness at the middle of an arbitrary three-term sequence, not just a preservation-of-monomorphisms property. I apply it successively to the three positions of a short exact sequence with zeros at the ends. Component colimits of zero are zero by step 5. The remaining direct-sum exactness check explicitly proves injectivity, kernel-image equality and surjectivity with preimages supported on the tuple's finite support. Step 4 identifies the resulting maps with the actual colimit maps. Thus no right-exactness theorem for unspecified adjoints is needed.

I checked delivery-errors B–E against the files. B: there are no new nodes, no hidden sketches in statements, no altered notions, and all TeX is single-escaped on decoding JSON. C: all four cited node statements were opened and their precise used clauses copied into citations.json; `proof_deps` is exactly the union of uses. The two off-unit inputs are already Mathlib leaves, so they are generic tools permitted by the route rules; the component node is in the same unit. D: the proof carries the quotient, additivity, direct-sum comparison and element arguments; it does not transfer its clauses to new nodes. E: I checked the empty I (zero group, zero sequence), one-object identity category (ordinary Ab), two discrete objects (binary direct sum), an infinite discrete set (finite-support direct sum), and a nontrivial group as one-object category (fails (b), so its nonexact coinvariants are excluded). The branching span with no common successor fails (a), as required. All hypotheses used for the component theorems are verified in steps 3 and 5. All seven steps are below 2000 characters; none contains a hidden long lemma.

## Unfinished work

None in the stage-1 split. No new unsplit obligations were introduced. Maintainer independent review remains the standard delivery review.
