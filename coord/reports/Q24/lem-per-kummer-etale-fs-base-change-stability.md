# Q24: lem-per-kummer-etale-fs-base-change-stability

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-kummer-etale-fs-base-change-stability.json`: item, split in four steps; no Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-kummer-etale-local-chart-criterion.json`: new statement-only lemma, unsplit; no Mathlib match after two semantic phrasings, LeanSearch, Loogle and source grep.
- `citations.json`: one verbatim statement quotation per cited node per numbered step. Whole statements are quoted to preserve the hypotheses and the separate clauses used.

## Attachments

None. I searched the live `lean/WeilConjectures/` by the item tag and logarithmic/Kummer names. Ordinary etale Kummer torsors are not morphisms of fs log schemes and do not attach this item. The recorded item Lean states are both `none`.

## WANTED

None for this split: the ILO volume available locally states the local standard-cover theorem in VI 2.2. The existing saturated-pushout and fs-product nodes remain independent obligations, and this split does not claim they have been proved. No SGA source is used.

## Problems and changes

The imported item had no proof, despite referring to the parenthetical fs-base-change assertion in ILO X 1.8. Its statement is retained verbatim, including the ordinary-product local Noetherian hypothesis. There is no statement dispute. The proof is marked agent-written because the source states the conclusion parenthetically rather than giving this chart calculation. I read the current `literature/blueprint/latest/` ancestor statement and proof; the logarithmic material is a supporting input to the existing regular-pair-purity refinement, not a change to the unit or chapter route. No unit file changes.

The first draft of the coordinate-ring explanation was imprecise about the scalar compatibility with the new base. I corrected it to the two explicit tensor products in Step 3 and verified their maps to every ring impose exactly the same equations. This comparison retains the projections; it is not an unlabelled identification of abstract schemes.

## Not duplicates

lem-per-kummer-etale-local-chart-criterion vs lem-per-kummer-strict-local-standard-model: the existing theorem assumes a finite morphism over a strictly local base and concludes a component decomposition, character action, diagonal and invariants; the new theorem treats arbitrary Kummer etale morphisms and states an etale-local chart criterion in both directions, without finiteness or strict-local hypotheses. The existing theorem cannot be applied to the present arbitrary f.

lem-per-kummer-etale-local-chart-criterion vs def-per-kummer-log-morphism: the definition describes the characteristic predicate and what a standard strict local chart means; it does not assert such charts exist or give the local comparison criterion.

lem-per-kummer-etale-local-chart-criterion vs lem-per-prime-to-order-snc-kummer-charts: the existing statement concerns normalizations of invertible-order torsors on regular schemes with a strict normal crossings boundary. The new statement requires none of those restrictions and applies to an arbitrary fs base.

lem-per-kummer-etale-local-chart-criterion vs lem-per-invertible-kummer-chart-log-regular: the existing theorem assumes the chart and a log regular base, and concludes log regularity of the source; it does not establish a chart criterion for arbitrary log schemes.

lem-per-kummer-etale-local-chart-criterion vs lem-per-kummer-saturated-pushout-algebra: the latter is the monoid-pushout and fs-product computation used after charts are chosen; it does not infer the existence of Kummer charts from characteristic Kummerness and log etaleness.

I searched all DAG nodes by Kummer, standard/local chart terminology and VI 2.2, and ran `tools/blueprint_refs.py search` for Kummer, Kummer etale, Kummer chart, log etale and standard Kummer. No imported blueprint node states the new criterion. The new lemma is not the base-change conclusion or a clause of that conclusion: it contains no arbitrary base change and relates the stalkwise predicate to chart data. The already existing saturated-pushout node and fs-product theorem are reused rather than duplicated. No new node has a Stacks tag, so there are no additional same-tag pairs.

## Review by Q24

I read ILO VI 2.1--2.2, printed pp.71--72, for both the item and the new node: 2.1 defines Kummerness on characteristic monoids; 2.2 states that standard Kummer chart covers are Kummer etale and every Kummer etale morphism is etale locally standard. Allowing an etale comparison is the local form of this statement, consistent with the chart definition of log etaleness. I also read VIII 3.3.5--3.3.6, printed p.107, for chart base change, and X 1.8, printed pp.146--147, for the diagram and its parenthetical arbitrary fs-base-change assertion. I did not confuse its finite G-cover formulation with the general local morphism to be proved here. The source for the new node is these actual printed places, rather than a guessed Stacks tag for logarithmic geometry.

For Step 1 I opened `lem-per-fs-product-finite-comparison`: its statement supplies existence and the finite comparison under precisely our locally Noetherian ordinary-product assumption, and its strict clause identifies pullbacks of strict etale neighbourhoods with ordinary pullbacks. I opened `lem-weil-pbc-etale-covering-base-change`: it explicitly supplies joint surjectivity and etaleness of the pulled-back neighbourhoods. The new local-chart criterion supplies an injective Kummer h, an invertible annihilating integer on the target neighbourhood, and an etale comparison. I use no standard-chart conclusion from the definition node or from the finite strict-local theorem. Pulling source neighbourhoods back along X' -> X and pulling target neighbourhoods back along Y' -> Y gives the required family; associativity of these fs products follows from their stated universal property.

For Step 2 I opened the entire statement of `lem-per-kummer-saturated-pushout-algebra`. It explicitly allows arbitrary a:P -> R, provides compatible refinements for the already chosen P-chart, and states injectivity, root-cofinality and the precise group cokernel isomorphism after saturation. These are the statements used, not a conclusion extracted from its proof. All its hypotheses come from Step 1. An inverse of n remains an inverse after pullback, so there is no unjustified flatness inference or new finiteness assumption.

For Step 3 that same node explicitly states the fs-product scheme formula and chart S. The remaining tensor comparison is written out as a universal-property calculation: maps from either ring are triples agreeing on H, Q and R. It is elementary ring-pushout algebra once that cited fs-product formula is available. I corrected the scalar expression during this review, as recorded above. No new comparison lemma is concealed here: all equations and maps being identified are displayed.

For Step 4 I opened `lem-weil-pbc-etale-ring-base-change`; its statement assumes exactly an ordinary etale map of affine schemes and arbitrary scalar extension and concludes the etaleness used for c'. Affineness is arranged by the new chart lemma and by choosing affine V'; the monoid rings and fibre products are affine. The final application is the converse of the new criterion, on the covering family from Step 1. This also verifies characteristic Kummerness, rather than silently inferring it from the word log etale. The two off-unit inputs are existing Mathlib leaves, so they need no off-route tool declaration.

Small cases: for h=1 the pushout is R and the computation is ordinary etale base change. For n=1 the group cokernel vanishes, and the statement still makes sense. The empty source is covered by the empty family and causes no existence or surjectivity assertion for f. For the diagonal pullback of the standard root chart N -> N, 1 -> n, the saturated pushout has group Z plus Z/n, so the argument must retain torsion units and all branches; I checked that it does and imposes neither sharpness nor torsion-freeness on S. For the closed log-point base change of the root map (t=s^n), the ordinary product can be nonreduced; the fs formula, not the unchanged ordinary product, is used. In residue characteristic dividing n the new chart criterion's invertibility hypothesis fails, so the calculation does not falsely call a wild root map log etale.

Against delivery-errors B--E: the only new node is self-contained, statement-only, with genuine logged searches and a precise blueprint origin; no data definition or hollow proof was added. Every non-elementary fact in the item is a cited statement, quoted verbatim in citations.json; the elementary tensor identification and unit preservation are explicit. I checked the dependency closures of every reused input and found no route back to the item. No step exceeds 2000 characters. The item is proved by a computation, not by citing a renamed base-change conclusion. No source or statement correction remains outstanding.

## Unfinished work

None in this one-level split. The new local-chart lemma intentionally remains unsplit, as required for newly created non-Mathlib nodes; its independent proof is subsequent DAG work. No Lean was written and no compiler or Lake command was run.
