# Worker report: lem-sfb-hom-flat-evaluation-roof

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-hom-flat-evaluation-roof.json`: statement item, split into six proof steps; not a Mathlib leaf. Statement and statement dependencies unchanged. All original fields, original searches, creation attribution and blueprint ancestry retained.
- `citations.json`: 29 step/node records containing exact substrings of the cited statements.
- `report.md`: this report. `searches.jsonl` was produced by the required search wrapper; `write_split.py` is sandbox-only preparation code.

New nodes: 0. New Mathlib leaves: 0. No unit/chapter record changed: this item is not the unit's key node.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint id and for evaluation-roof, scalar-adjunction and internal-Hom scalar terminology found no declaration stating this item. Homology evaluation-roof files concern a different homology comparison. Ordinary tensor-Hom and scalar adjunctions do not give this unbounded ring-sheaf roof equality as an attachment.

## WANTED

None. The relevant Stacks sources are present locally. The precise flat-scalar roof assertion is an agent refinement, as the item's source already says; it is not attributed verbatim to Stacks.

## What was wrong or incomplete

The imported item had a statement and searches but no proof or proof dependencies. Its statement is sound. I supplied the denominator argument and both transposes, including the inverse augmentation in the original evaluation and the augmentation in the strict comparison. I kept these two maps explicit so that the final equality is about the canonical comparison, rather than an unspecified isomorphism.

A tempting invalid argument would apply internal Hom directly to the quasi-isomorphism EC -> EJ, although neither complex need be K-injective. Step 1 instead first applies I_R and proves I_R(e) is a quasi-isomorphism by the natural augmentation square. Another tempting gap would assume B is K-flat when applying the normalized scalar tensor comparison. Step 4 resolves B and descends the representative square. Neither issue requires a new lemma node: the DAG already contains exactly the inputs.

The blueprint ancestor and item provenance refer to the historical coefficient-passage paragraph and old parent steps 7, 10 and 11. The current main-20261015 ancestor Markdown contains its bounded-constructibility statement; this delivery works below that unit on the already-created abstract coefficient-comparison item and changes no chapter or unit route. No prohibited source route is used.

## Unfinished work

None within this one-level split. Existing cited unsplit nodes remain their own items. The proof is marked agent-written. No Lean file was written and no compiler, Lake or build tool was invoked.

## Searches and reuse

The sandbox initially contained no item copy or report. I read and retained the repository item's earlier Q52 search entries; the seven Q116 queries are appended with the exact wrapper query text. LeanSearch, Loogle, LeanFinder (two phrasings) and two source grep searches all returned successfully. The search log contains the actual results; no unavailable service was recorded as an absence.

The ordinary module candidate `ModuleCat.extendRestrictScalarsAdj_homEquiv_apply` at Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean:905 evaluates at 1 tensor m. `IsBaseChange.linearMapLeftRightHom_apply` at Mathlib/RingTheory/TensorProduct/IsBaseChangeHom.lean:118 concerns ordinary linear maps. `Functor.rightDerived_map_eq` at Mathlib/CategoryTheory/Abelian/RightDerived.lean:164 concerns higher derived functors on objects with injective resolutions, not this unbounded internal-sheaf Hom identity. The second semantic phrasing found `SheafOfModules.pullbackPushforwardAdjunction` (PullbackContinuous.lean:60) and `SheafOfModules.PullbackConstruction.adjunction` (same file:79); I read these ordinary sheaf adjunction definitions too. None states the item or specializes to it in one line.

Whole-DAG concept searches covered internal-Hom invariance, K-flat/K-injective inputs, scalar tensor comparisons and the evaluation roof. The existing `lem-pur-rhom-well-defined`, `lem-sfb-hom-kflat-chain-transpose`, `lem-sfb-hom-scalar-chain-identification`, and `lem-sfb-scalar-tensor-comparison` were reused. `tools/blueprint_refs.py ancestor` confirms lem-sfb-dc-hom-preserves; whole-blueprint searches for internal hom, evaluation, scalar extension, resolution roof and 08J9 did not find an equivalent blueprint assertion. In particular the finite-free-stage and filtered-colimit comparisons have additional hypotheses and different conclusions. No new nodes were needed.

## Not duplicates

No new nodes; no new/existing same-tag pairs to distinguish.

## Review by Q116

I read the item, its chapter and unit, the strict models and strict roof definitions, and the scalar-adjunction statement. I read Stacks sites-cohomology.tex Tag 08J9, label lemma-internal-hom, including its proof via the actual Hom/tensor adjunction and K-injective target; Tag 0A95, label lemma-RHom-well-defined, including its hypotheses on BOTH injective targets; Tag 06YY, label lemma-derived-base-change; and Tag 07A4, label lemma-pullback-tensor-product, including its reduction to flat-term K-flat representatives. I also read sites-modules.tex Tag 03CZ, label lemma-adjointness-tensor-restrict, homology.tex Tag 010N, label lemma-exact-functor, and derived.tex Tag 015F, label lemma-right-derived-exact-functor. These are sources for the tools and normalizations, not a claim that any one source already states this roof lemma. There are no new-node statements to compare against sources.

1. Step 1 uses the exact-functor cohomology statement to preserve quasi-isomorphisms, the K-flat resolution statement and derived change-of-rings computation to justify exact-extension representatives, functorial K-injective existence for the natural square, and Hom-invariance for its final map. I opened all five node statements. The Hom-invariance statement applies to I_R(EC) -> I_R(EJ), whose source and target are K-injective; its other map is 1_P. No claim that Hom(P,-) preserves arbitrary quasi-isomorphisms is made. The site's universe-smallness is exactly what the chosen functorial resolutions require.

2. Step 2 uses the fixed Hom representative and inverse augmentation in def-coef-hom-representative-evaluation, the existing K-flat chain-transpose lemma, and the resolution-existence statement for J and I_R(EJ). The chain-transpose lemma explicitly allows arbitrary A and arbitrary K-injective target E, while requiring P to be flat-term K-flat, which is a hypothesis of this item. In particular it applies to E=J and the identity of B, giving the evaluation into J, then the explicit inverse eta_C. The factor order is B,P.

3. Step 3 uses the strict models' formula for Normalized and the strict roof's identification of comparison with that normalized transformation. It uses the scalar chain-identification statement with N=EJ and q=identity; its explicit formula with t=1 gives s tensor f(p). That node assumes neither exactness nor K-injectivity of EJ. The chain-transpose lemma is applied to I_R(EJ), which IS K-injective. The fixed representative definition specifies the inverse eta_EJ, so the cancellation with eta_EJ h is legitimate. Pure tensors and projections are used only to compare two already-defined maps, not as an uncited existence theorem.

4. Step 4 uses the existing K-flat resolution statement to obtain T -> B with flat terms, the scalar tensor comparison's explicit representative-square clause on T,P, scalar extension's K-flat-preservation statement for EP, the chain-transpose lemma's representative/inversion clause for t tensor P, and exact cohomology to apply E to quasi-isomorphisms. I checked each statement rather than taking anything from its proof. Resolving B removes the otherwise unjustified K-flat assumption on B. The square is an application of an existing comparison, not an additional hidden comparison lemma. The argument keeps the pure-tensor order, with scalar s in degree zero.

5. Step 5 uses precisely the evaluation-normalized characterization in lem-sfb-dc-hom-scalar-adjunction, the functorial representative action of def-pur-derived-internal-hom, and the natural adjunction in def-coef-ringed-tensor-hom-model. Localization supplies inverse quasi-isomorphisms. Under the fixed representatives F(e) is H_R(QP,[e]); the transposes are therefore [e][e]^{-1}[h] and [eta_EJ]^{-1}[eta_EJ h], both [h]. Injectivity of the Hom-bijection, and then cancellation of [v_S], are elementary operations after these cited inputs. This step carries the actual roof identity; it does not invoke a new node restating that identity.

6. Step 6 cites the naturality clauses of the resolution, scalar chain-identification, chain-transpose and scalar tensor comparison statements, Hom-invariance, scalar-adjunction coefficient compatibility, and localization. I wrote the precomposition and postcomposition evaluation formulas explicitly. The representative equations extend across inverses of quasi-isomorphisms because the cited comparisons say so, and then across all derived morphisms by localization. Coefficient compatibility uses the existing normalized scalar comparisons and their evaluation characterization, never an assumption that the chosen replacement functor commutes strictly with changing rings.

I checked B--E of delivery-errors.md: no new node or clause-relabelling, no unsplit proof hidden inside a new statement, no unrecorded Mathlib searches, and every step/node pair has a verbatim quote in citations.json. The five off-unit theorem uses are declared in split_report.tool_uses as generic resolution, cohomology and Hom-invariance tools. Each is below the same abstract coefficient route; none supplies a replacement finiteness argument. The item's statement dependencies were read and retained because each notion is actually used in the unchanged statement. All six proof steps are below 2000 characters, and none hides an additional lemma: the non-elementary comparisons are existing cited nodes.

I tested the formulas for R=S (ordinary evaluation followed by a resolution comparison), P=R in degree zero (scalar multiplication s tensor x), P=0 and C=0 (zero maps), and the exact extension to the zero ring (all extended objects zero). Unbounded degrees introduce products in Hom, but no argument commutes scalar extension with those products: the comparison is only a map, and the proof never asserts it is invertible. This distinguishes the statement from finite-free or continuity comparisons. The only use of flat scalar extension is preservation of quasi-isomorphisms and its exact-extension representative identifications. No finite rank, boundedness, filtered exactness or continuity hypothesis was introduced.

The server-side standalone review_split check passed before the full delivery dry run. The required full dry run is run after this report is written, and delivery follows only after it exits successfully.
