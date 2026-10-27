## Worker report

Q86 split `lem-sfb-complete-nonarchimedean-matrix-group` in `dag/nodes/sec-six-functors-basics/lem-sfb-complete-nonarchimedean-matrix-group.json`. The statement is unchanged. Nine proof steps give the argument instead of moving its clauses into new nodes.

## New nodes

- `lem-sfb-complete-field-cauchy-filter-limit`, statement, Mathlib leaf: `cauchy_map_iff_exists_tendsto`, `Mathlib/Topology/UniformSpace/Cauchy.lean:428–430`. Its statement treats arbitrary proper filters into a complete normed field; it is not a matrix-group clause. It has no proof or proof dependencies.

The other files are `citations.json` and this report. `searches.jsonl` contains the actual msearch records. The sandbox script `write_split.py` assembles the JSON and is not part of the delivery.

## Attachments

None. The project Lean source was searched for the exact blueprint tag and for nonarchimedean, general-linear-group, matrix-group and Cauchy-completeness notions. No declaration under WeilConjectures states all clauses of this item. The nearby use of `cauchySeq_tendsto_of_complete` in `SixFunctors/ProEtale/Adic/LisseCover/Congruence.lean` is a use of the general convergence theorem, not this matrix-group theorem.

## WANTED

None. The matrix proof is explicitly agent-written, as in the item's existing source description. The available Bhatt–Scholze paper supplies the context and the meaning of two-sided completeness, not an exact norm-topology matrix-group theorem.

## Source and route

Read Bhatt–Scholze, *The pro-étale topology for schemes*, PDF pp. 63–65, especially Definition 7.1.3 and Proposition 7.1.5. Example 7.1.7 uses the colimit topology on an algebraic extension; it cannot be used for the norm topology here. Our argument establishes precisely the group-theoretic input for Proposition 7.1.5, without using its Noohi conclusion as an input.

Read `dag/chapters/sec-six-functors-basics.json`, `dag/units/sk-thm-sf-ctf-stability.json`, and the current main-20261015 unit and `sk-thm-sf-ctf-stability-direct-images.proof.md`. The recorded provenance is direct-images paragraph (3), in the all-continuous-coefficient monodromy input. `blueprint_refs.py ancestor` reports null for this inherited created-item chain. I kept that mechanical ancestry, retained the exact existing place, and added the matrix proof obligations to the new leaf's place. The unit and chapter routes are unchanged.

## Searches and existing nodes

Before creating the new node I searched all DAG node statements and Mathlib matches for Cauchy-filter convergence, complete metric/uniform spaces and `cauchy_map_iff_exists_tendsto` / `cauchySeq_tendsto_of_complete`, and the project Lean source for these names and notions. The blueprint searches `Cauchy`, `Cauchy net`, `Cauchy filter`, `complete metric`, `complete uniform` and `metric convergence` found no matching blueprint node. The convergence leaf is absent from the current DAG. Its sole defined algebraic notion is field, citing def-weil-field; norm, metric, filter, convergence and the Cauchy condition are given explicitly in its statement.

The initial geometric-decay search found the existing `lem-wf-geometric-decay` in sec-deligne-laumon-a1. I opened its statement and Mathlib match and reused it. It is a Mathlib leaf and therefore does not change the unit route. Likewise `lem-sfb-normed-field-completion` already supplies the complete field and isometric inclusion. No node was created for finite-product convergence, finite-sum maximum estimates or the two-sided Cauchy inequalities: their elementary arguments are written in the steps.

All Mathlib searches were run through msearch.py and read. For the item, two semantic phrasings and Loogle/grep found matrix-space completeness, normed-ring units and locally compact group completeness, which do not state the whole item. For the new node, LeanFinder's filter formulation and Loogle identify the exact `cauchy_map_iff_exists_tendsto`; the logged grep locates line 428. The earlier net phrasing independently finds the same general completeness interface. I read lines 420–440 of the actual Mathlib file. The leaf uses the arbitrary-filter statement directly, avoiding any unproved comparison between metric and abstract Cauchy definitions.

## Not duplicates

`lem-sfb-complete-field-cauchy-filter-limit` vs `lem-sfb-complete-nonarchimedean-matrix-group`: the new node proves only general Cauchy-filter convergence assuming an already complete normed field; it does not prove that any matrix group is complete, nor its subgroup basis or geometric inverse.

`lem-sfb-complete-field-cauchy-filter-limit` vs `lem-sfb-normed-field-completion`: the existing node constructs the normed-field completion and canonical inclusion; the new node states the convergence interface for proper filters in any already complete normed field.

`lem-sfb-complete-field-cauchy-filter-limit` vs `lem-sfb-complete-group-forgetful-automorphisms`: the existing result identifies natural automorphisms of a discrete-action fibre functor for an already complete group; it is not the general convergence lemma.

No Stacks tag is used by the new node: its exact source is Mathlib. No SGA source is used.

## Review by Q86

I read the item and its completion dependency, the geometric-decay node, and the actual Mathlib statement for the new leaf. I checked the nine steps against those statements, rather than borrowing their proofs or making a definition node stand for a theorem.

1. The completion node explicitly says the uniform completion is a complete normed field and the inclusion is isometric. Density is part of uniform completion. Approximating two elements and passing through continuous absolute value and maximum proves the extended strong triangle inequality; no extension-of-ultrametricity theorem is silently assumed.
2. The empty matrix is separated before asserting that the identity has norm one. For positive size the finite-sum maximum bound follows by induction from the field's inequality, and each matrix-product entry is such a sum. Thus there is no missing factor n. This is an elementary calculation, not a new lemma moved out of the item.
3. I checked that a maximum-norm ball is the finite intersection of coordinate balls and that the minimum of their radii gives the reverse inclusion. This proves the topology comparison and the finite-coordinate convergence criterion. Multiplication is a finite sum of continuous field products, so the continuity used later has already been justified.
4. `lem-wf-geometric-decay` states exactly the convergence of q^m for 0 ≤ q < 1. The new Cauchy-filter leaf says exactly that a Cauchy image filter into a complete normed field converges. Apply it separately in F to each coordinate of the explicitly bounded partial sums. Multiplying the finite geometric identity on both sides gives a genuine two-sided inverse, not merely a one-sided matrix inverse. Completeness is applied to F, never to GL_n(F), so there is no circular completeness assumption.
5. The non-strict bound for the inverse minus the identity comes from the finite partial sums and is preserved under a limit. It is ≤ N(B), which is strictly less than r; replacing this by ≤ r would lose subgroup closure. The case B=0, including q=0, was checked explicitly.
6. The product estimate has all three terms B, C and BC. The hypothesis r<1 ensures N(B)N(C)<r. Inverses come from step 5, and strict coordinate inequalities prove openness. The radius can always be shrunk below 1, so the basis assertion holds even for a trivial absolute value.
7. I checked the local factorization x=g(I+D), the order of factors in its inverse, and the bound N(g^{-1})^2 N(x-g). These give inversion continuity in the topology induced from matrices, without using any different topology on bundled units or assuming continuity of inversion beforehand.
8. A single fixed tail element bounds both g_i and g_i^{-1}; the reversed ordered pair in the left Cauchy condition bounds the inverse factor. The later additive difference for g_i uses g_i^{-1}g_j, whereas the inverse difference uses g_i g_j^{-1}. I checked the two displayed identities and the uniform positive denominator M. Both relative Cauchy hypotheses are available, and no total order or countable index set is assumed.
9. The new leaf applies to the proper tail filter of the nonempty directed index set, in each coordinate of the complete field. Finite-coordinate convergence and multiplication continuity established in step 3 give both ab=I and ba=I. The matrix a is therefore invertible, and the subspace topology gives the asserted group convergence. The same estimates work for a proper two-sided Cauchy filter, by choosing one filter member with pairwise relative differences in U_r and then one element of that member; thus the formulation by uniform completeness is also justified.

I checked the new leaf for finite fields with trivial norm, complete p-adic fields, ordinary sequences, and noncountable directed nets. Its explicit proper-filter hypothesis prevents a spurious existence conclusion from the improper filter. It states only a theorem, with no proof sketch hidden inside its statement. I checked the item for n=0, n=1, B=0, trivial norms, and arbitrary positive real r<1. No local compactness, nontrivial valuation, discrete valuation or characteristic hypothesis is used.

I corrected the initial plan by reusing the geometric-decay node rather than creating a duplicate, and chose the exact arbitrary-filter Mathlib interface rather than packaging a metric/net comparison as a leaf. The item's statement required no correction or dispute. The citations file quotes the exact portions of the three cited node statements. Every non-elementary step names the analytical input it takes. No step exceeds 2000 characters, and none hides a comparison or identification under a word such as “transport”. The report and new-node fields were also checked against delivery-errors B–E: self-contained statements, no proof in an unsplit node, exact source/file/line, searched dependencies, no clause relabelling, and no cycles introduced.

## Unfinished work

None in the proposed stage-1 split. The first dry run rejected the generic complete-space leaf because its statement had no definition-node citation. I specialized it to the complete normed-field case actually needed, cited the existing def-weil-field, and gave the filter and metric notions inline. The revised Mathlib match is still a one-line specialization of the same general theorem. I ran the field-specific semantic search and checked the field definition and both updated citation quotes before repeating preflight.
