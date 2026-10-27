# Q100 stage-1 delivery: lem-sfb-group-tangent-dimension-smoothness

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-group-tangent-dimension-smoothness.json`: unchanged statement; five complete proof steps using existing nodes, status `split`; existing search records preserved and the five Q100 searches appended.
- `citations.json`: 17 step/node entries, each quoting the cited statement verbatim, including its hypotheses.
- `report.md`: this report. No new nodes, Mathlib leaves, definitions or Lean files.

## Attachments

None for the item. I searched `lean/WeilConjectures/` for the blueprint id and tangent/dimension/smoothness terminology and read `GroupScheme/Lie/Dimension.lean`, `LieLocalDimension.lean`, and the relevant smooth-morphism interfaces. `AlgebraicGeometry.GrpObj.topologicalKrullDim_le_finrank_lie` proves the inequality, while `finrank_lie_eq_topologicalKrullDim` assumes characteristic zero. `finrank_lie_eq_localKrullDim_of_smooth` assumes smoothness and gives only local dimension. None gives every clause, especially equality implying smoothness in positive characteristic. They therefore do not justify ATTACH. The item has no own upstream declaration recorded.

## WANTED

None. The Milne PDF and the Stacks sources needed here are present.

## Corrections and scope

The item itself is true as stated and is unchanged. Its empty proof is replaced by the cotangent/regularity/homogeneity proof of Milne Proposition 1.37. The existing dependency `lem-ag-group-identity-local-dimension` is the needed global-to-local identification; a general scheme dimension assertion would not suffice. All seven original statement dependencies are retained. The proof dependencies are exactly the union of step citations. No identity-component or reducedness hypothesis is introduced, and no SGA route is used.

I read `dag/chapters/sec-six-functors-basics.json`, `dag/units/sk-thm-sf-ctf-stability.json`, and the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`. This auxiliary algebraic-group result serves the recorded Milne 17.47 normalizer argument inside the inherited alteration/GIT ancestry; it does not replace a six-functor step. I also read the current `sk-p-geometry/lem-wf-same-lie-closed-subgroup.md` and its proof: its matrix groups over Q_l-bar are not the arbitrary-characteristic group schemes here. The blueprint ancestor command prints `None` for the inherited chain, so the item's existing `from.node: null`, detailed `from.place`, and `via` list are preserved. Whole-blueprint searches for `tangent dimension`, `cotangent`, `identity smooth`, `regular smooth`, and `smooth locus` did not find an equivalent blueprint statement; `same_as` is `[]`. Off-unit generic tools that are not Mathlib leaves or Lean-closed are declared in `split_report.tool_uses`.

## Source error

Milne Proposition 1.37 itself is the intended true group statement. Its proof's sentence beginning “In general” is too broad if read as an assertion about the global dimension of an arbitrary finite-type scheme. For example, let X be the disjoint union of Spec F and A^1_F, and take e in the first component. Then dim T_e X = 0 whereas dim X = 1. Appendix A.52 assumes irreducibility, and Milne's algebraic-scheme discussion uses classical closed points; neither authorizes identifying global dimension with the stalk dimension at every scheme point. Here I explicitly use the existing group identity-local-dimension theorem before invoking the local inequality. No statement correction is necessary for the assigned item.

## Not duplicates

No new nodes are proposed. I searched the whole DAG by statement and title for tangent dimension, cotangent regularity, identity dimension, smoothness at rational points, translations, and Noetherian permanence, and read all 17 cited node statements. The existing local-dimension, tangent-duality, finite-dual, regular-local, smooth-neighbourhood, Jacobson and affine-comparison nodes are reused. In particular a new smoothness-at-the-identity lemma would be unnecessary: the explicit translation argument is Step 4.

## Mathlib searches

The Q100 `searches.jsonl` records the exact five queries run with the required `msearch.py` command: two LeanFinder phrasings, Loogle `"tangent", "smooth"`, LeanSearch on the full dimension criterion, and the tangent/smoothness regex in `AlgebraicGeometry`. All services returned results. I read the displayed hits. The semantic hits concern standard smooth algebras and ranks of differential modules; the Loogle hits concern H1 cotangent vanishing and the naive cotangent criterion. The grep hit is an import in Etale.lean. These are ingredients, not the group-scheme theorem nor a one-line specialization of it. The alternative phrasing found the affine smoothness interface and smooth locus, but no full criterion. The previously recorded searches are retained as historical source material. There are no new nodes requiring additional node-specific searches.

## Review by Q100

I read Milne Proposition 1.37 and the dimension discussion on printed pp.17–18, Proposition 1.28 on printed p.14, and Appendix A.51–A.52 on printed pp.577–578. The split follows exactly their local regularity and homogeneity route, with the global/local issue made explicit. For the auxiliary facts I read the statements in Stacks `algebra.tex` at Tags 00FN (Noetherian permanence), 00KU and the preceding fundamental inequality, 00TV (regularity versus smoothness with separable residue), and 00TT (smoothness implies regularity). I read `varieties.tex` at 0B2E (rational tangent-cotangent duality) and 0478 (Jacobson), `algebra.tex` at 00FV (Nullstellensatz), `schemes.tex` at 01HV (affine stalks), and `morphisms.tex` at 01V6 (affine and open-local smoothness). I checked the finite-dual statement against Mathlib LinearAlgebra/Dual/Lemmas.lean, including the finite-dimensional instance and `Subspace.dual_finrank_eq`. No new source-dependent node is created.

Step 1 cites the finite-type definition only to choose a finite-type affine chart, not to assert an unproved property of every affine open. Its affine-stalk citation explicitly identifies the local ring with A_q. The two separate Noetherian permanence statements give precisely finite-type ascent and localization. A field is Noetherian because its only ideals are 0 and itself. The augmentation is split by F -> A, so it is surjective and has quotient F; hence q is maximal and the residue extension is trivial. The group-local-dimension statement explicitly requires finite type and explicitly allows nonreduced groups, so its use does not assume smoothness or connectedness.

Step 2 uses the full fundamental inequality statement, which supplies both finiteness of m/m^2 and the regularity iff equality. The tangent-duality node really identifies tangent vectors with the linear dual of m/m^2; applying its morphism version to id_J satisfies both rational-point hypotheses. The separate finite-dual Mathlib leaf supplies finite-dimensionality and equality of dimensions; it is not inferred merely from a definition of the tangent space. Nonnegativity is valid because R has a residue field, so its spectrum is nonempty. Thus both numerical finiteness clauses, not just the inequality, are proved.

Step 3 invokes the existing affine regular-separable smooth-neighbourhood statement, which actually produces an open smooth neighbourhood. It does not cite the weaker regular-closed-point statement for a neighbourhood it does not state. The chart algebra is finite type, its local ring was proved regular, and the residue field F/F is finite separable of degree one. All of that node's hypotheses have been established.

Step 4 cites an actual translation-isomorphism statement, with inverse given by the inverse group element. Its image of V is open, contains g, and remains smooth by clause (c) of the cited smooth-restriction/isomorphism theorem. The closed-point residue-field result needs an algebraically closed base and local finite type, both present. The Jacobson node states density of closed points of J in every closed subset, precisely what the closed complement of the union needs. This proves the translated opens cover all of J, not only J(F). The source-local smoothness statement then applies to this set-indexed cover. No new lemma is hidden in that routine assembly.

Step 5 first uses smooth restriction to the affine chart, then the explicit affine scheme/ring equivalence, and finally the regular-local theorem for smooth field algebras. Thus no theorem about smooth ring maps is silently applied to a scheme morphism. Returning to Step 2 gives equality. The two directions therefore cover the full iff, including positive characteristic.

For edge cases I checked the trivial group (both dimensions zero, smooth), finite constant disconnected groups (both dimensions zero), G_a and G_m (both dimensions one), and alpha_p and mu_p over an algebraically closed field of characteristic p (dimension zero, identity tangent dimension one, nonsmooth). Products of these examples confirm that disconnectedness and nilpotents cannot be omitted from the audit. The empty-scheme exception for dimension is irrelevant because the identity provides a point. No proof step exceeds 2000 characters (largest: 739); none merely restates a clause as a new node.

Against delivery-errors B–E: there are no new nodes with hidden proofs, missing notions, duplicated tags or fabricated searches; all cited nodes were read for their statements rather than their proofs; the 17 verbatim quotes witness C4; all non-elementary inputs are cited, with no unmatched flatness, topology or comparison assertion; and the proof is a five-step argument rather than a relabelled conclusion. There are no unresolved mathematical gaps or statement disputes in the assigned item.

## What could not be finished

Nothing in the stage-1 split. Delivery validation and push are recorded by the delivery tool.
