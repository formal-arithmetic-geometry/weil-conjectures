## Worker report

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-local-proj-isomorphism-compatibility.json`: statement item, now split into four steps; no full Mathlib match.
- `citations.json`: one exact statement quotation for every node cited by every proof step.
- `searches.jsonl`: five actual searches made through the required msearch command; all returned results and were read.
- `report.md`: this report and signed review.

New nodes: 0. Mathlib leaves: 0. The existing DAG supplies all the non-elementary inputs. No Lean file, compiler, Lake or build tool was used.

Attachments: none. The exact blueprint tag is absent from `lean/WeilConjectures/`. The concept search found `AlgebraicGeometry.Scheme.GradedAlgebraData.relProjIsoOfIso` and the surrounding restriction and composition declarations in `AlgebraicGeometry/RelativeProj/Functoriality.lean`. These cover construction and functoriality, but do not state the degreewise-unit invariance clause of this item. They therefore do not justify ATTACH.

WANTED: none. The source is present.

The imported item was statement-only, with sound hypotheses and detailed chart normalization. I preserved its statement, source, statement dependencies, blueprint ancestry and earlier six searches. The new argument uses the already existing `lem-nagata-affine-proj-scalar-extension` at the identity base map instead of making another affine Proj lemma. The inverse and compatibility computations are written in the item itself. The source's 02NC proof omits the gluing details; this proof supplies the coefficient-restriction square and unit cancellation explicitly. Accordingly its proof origin is agent, with the actual Stacks source and places recorded.

Nothing remains unfinished. The delivery dry run and push are performed after this review.

## Existing-node and blueprint searches

I searched the whole DAG for 01MY, 01N2 and 02NC, homogeneous localization and graded-isomorphism terminology. I ran `tools/blueprint_refs.py ancestor` on this item, and whole-blueprint searches for `Proj`, `graded algebra isomorphism`, and `degreewise unit`. The ancestor is `lem-trf-local-term-locality`; the last two searches have no matches. The broad Proj search was followed by opening the relevant DAG statements. The item has no other blueprint statement with all its clauses, so `same_as` remains empty.

I read `def-sfb-relative-proj-iso-of-graded-iso`, `prop-nagata-relative-proj-functoriality`, `lem-nagata-proj-affine-restriction`, `lemma-nagata-relative-proj-exists`, `lem-nagata-affine-proj-scalar-extension`, and the standard-chart and scheme-gluing statements. The sfb definition describes a specified comparison, but I did not cite a definition as its existence theorem. The scalar-extension theorem actually states existence, inverse-image charts, the comorphism, covering and uniqueness, and is therefore the appropriate input. Its dependency graph does not lead back to this item. I checked the same for the other proposed inputs.

## Mathlib searches

The five new logged queries are recorded verbatim in the node, in addition to all the previous search records. Loogle for `AlgebraicGeometry.Proj.map` returned map, map_id, map_comp, map_preimage_basicOpen, awayι_comp_map and the section formula. I read `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Functor.lean`, including the construction at lines 164 onward and the chart and composition arguments. The two LeanFinder phrasings and LeanSearch returned basic-open isomorphisms, the affine chart map, restriction of fromOfGlobalSections, and pullback-chart identifications. The grep returned restrictions of the Proj scheme to an open. None states the whole relative sheaf comparison with invariance under multiplying homogeneous degree k by a base unit to power k. Thus this item is not a one-line Mathlib specialization; its short remaining calculations belong in its proof, rather than in new nodes.

## Tool use

`lem-nagata-affine-proj-scalar-extension` is an off-unit generic tool, declared in `split_report.tool_uses`. It supplies affine Proj and its chart description. This does not replace a step of the trace-formula unit: it is an algebraic-geometric tool on the already inherited 087S/02NC projectivity-conversion branch. No trace-formula unit node gives that affine Proj construction. Definitions and the Mathlib scheme-gluing node are the other inputs.

## Not duplicates

There are no new nodes, hence no new/existing same-tag pairs. In particular no node was created for an existing graded-isomorphism construction, for the restriction square, for taking an inverse, or for cancellation of units.

## Review by Q116

I read Stacks `constructions.tex`, Tag 01MY, label `lemma-morphism-proj`, including its characterization by inverse-image charts and its proof that the comorphism sends a/f^m to psi(a)/psi(f)^m. I also read Tag 01N2, label `lemma-base-change-map-proj`, whose arbitrary scalar-extension assertion includes the identity base map, and Tag 02NC, label `lemma-twisting-and-proj`, whose proof says to trivialize and glue but omits the details. The tag-to-label mapping was checked in `stacks-project/tags/tags`. Those sources match the item: the graded algebras are commutative and unital, coefficient maps are base-linear, and there is no assumption that degree zero equals the base ring. The current blueprint ancestor and the chapter/unit records were read. This is a subordinate Proj tool on the existing branch, not a change to the unit's contracting-correspondence argument. There are no new-node source statements to review.

Step 1 uses the actual scalar-extension statement, not its proof: it gives the canonical map, its base square, the image of each fraction, the covering, and uniqueness. I verified the identity-base specialization by giving the map R tensor_R A to B and its inverse. Balancing checks the inverse even when R to A_0 is neither injective nor surjective. The relative Proj definition explicitly specifies i_U and its compatibility; it supplies the conjugation used here. I did not assume Proj itself affine, only its stated standard charts affine.

Step 2 uses the same scalar-extension theorem for beta inverse. The homogeneous-localization definition says every chart element has the indicated fraction representation, and the affine-spectrum definition states contravariant functoriality. The two displayed fraction composites therefore really are identity ring maps, and the Mathlib gluing node states precisely that equality on an open cover gives equality of scheme morphisms. This is an elementary calculation from those inputs, with both compositions checked.

Step 3 uses the specified affine restriction data of the relative Proj definition: its statement explicitly says coefficient restriction gives the same localized chart map. It does not merely assert an unspecified isomorphism. The scalar-extension statement gives the chart formula for beta_V. I wrote both composites and used the sheaf-morphism naturality equation rho_B beta = beta_V rho_A on both numerator and denominator. The cover used is the inverse image over V of the existing cover over U, so no assertion that old global sections generate arbitrary new sections is needed. Equality on that cover follows from affine-spectrum functoriality and the exact gluing statement. Replacing beta by beta inverse proves the inverse assertion too. No intersection of arbitrary affines is presumed affine.

Step 4 uses the definition of affine Proj for its homogeneous-prime description of D_+, and the degree-zero localization definition for the common chart ring. The unit's image v lies in B_0 and remains invertible even if the structural map to B_0 has kernel. I checked the common-chart identification by the two explicit mutually inverse fraction formulas; each just moves a degree-zero unit between numerator and denominator. The image of a numerator of degree md is v^{md} beta(a), cancelling exactly the v^{dm} from the denominator. This is not cancellation of f. Affine-spectrum functoriality and the gluing equality clause then give equality of the whole maps; uniqueness of inverses gives equality of their inverses. The step is a short direct localization calculation, not a hidden general lemma.

For edge cases I checked U or V empty, the zero graded ring, and algebras concentrated in degree zero: Proj is empty and uniqueness remains valid, including an empty chart cover. For f=0 or any nilpotent homogeneous f the corresponding chart is empty, with zero localization ring; no denominator cancellation was used. For a nonnilpotent zero divisor take A=(Z/6Z)[x], deg(x)=1, f=2x, u=5; inverting f makes the fraction calculation valid while 2x is still a zero divisor in A. For a genuinely larger degree-zero part take A=R[t,x] with t in degree zero and x in degree one. The proof still uses only the image of R and does not identify A_0 with R. The cases m=0 and u=1 give the identity numerator factors, as required.

Against delivery-errors B--E: the item stays self-contained and has no silently changed hypotheses; no statement-only node acquired a proof sketch because none was created; every non-elementary input is an existing node whose statement was opened, and all cited material appears verbatim in citations.json. The proof does not relabel a conclusion as a new lemma. All four steps are under 2000 characters, and their explicit calculations show why no further sublemma is hidden. I corrected no source statement: the repair was supplying the missing proof while avoiding an unnecessary duplicate construction. Search results are actual results, with the old provenance retained.
