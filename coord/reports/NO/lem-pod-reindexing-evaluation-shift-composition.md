# Stage-1 delivery: lem-pod-reindexing-evaluation-shift-composition

## Files written

- `dag/nodes/sec-poincare-duality/lem-pod-reindexing-evaluation-shift-composition.json`: item, statement, split into eight direct proof steps. Mathlib verdict: no exact match; no new nodes and no Mathlib leaves.
- `citations.json`: eighteen verbatim statement quotations, one for every step/node citation.
- `report.md`: this report. The sandbox also retains the authentic `searches.jsonl` and the item-specific writing script.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag, reindexing/evaluation terminology, and Hom/shift terminology. The existing source-shift and target-shift declarations in `Algebra/Homology/DerivedInternalHomShiftLeft.lean`, `DerivedInternalHomShiftRight.lean`, `HomComplexShiftLeft.lean` and `HomComplexShiftRight.lean` supply individual shift comparisons, not the evaluation-normalized comparison along a scheme isomorphism or its composition law. The PoincarePairing declarations concern the pairing and its adjoint description, not this item. No exact project attachment covers every clause.

## WANTED

None. All sources needed for the argument are present locally. No SGA source is used.

## Findings and changes

The imported item was statement-only, not a completed split. Its statement is retained verbatim, as are its statement dependencies, earlier searches and blueprint provenance. There is no statement dispute or change to the unit route. The main-20261015 blueprint proof of `prop-pod-dual-tate-data-compatibility`, Steps 1, 2 and 4, is the route: automorphism comparison, evaluation, and shift/coherence. The unit `sk-def-weil` defines strict Weil data and contragredience, and has no proof steps to realize for this auxiliary node.

I wrote the argument, rather than moving any clause into a new node. The key one-sided evaluation tool is the existing `lem-sfb-hom-kflat-chain-transpose`: the Hom-complex factor need not be K-flat. This avoids an unjustified computation of a derived tensor by two arbitrary representatives. The chain comparison is tested on all sheaf tensor summands, not merely on global sections or stalk values. The signed comparison is explicitly computed, not replaced by an unspecified isomorphism. Composition is proved by uncurrying and the canonical monoidal compositor, not by choosing an independent equivalence.

The new recorded searches were all run through msearch.py and read: LeanSearch on exact reindexing and evaluation; LeanFinder on the full comparison; Loogle on MonoidalClosed/Functor; grep of CategoryTheory for internalHom shifts and naturality of curry/uncurry; and a second LeanFinder phrasing on signed Hom reindexing. The hits give ordinary pullback compositors, abstract closed-category transport, and additive Hom-cochain shift equivalences. I read the naturality formulas in Mathlib's `CategoryTheory/Monoidal/Closed/Basic.lean` (lines 145–180); they do not construct or normalize this derived sheaf-Hom comparison. The individual shift hits do not cover the full item. No recorded search was invented or treated as a match from its name alone.

## Not duplicates

No new nodes. I searched the whole DAG and imported blueprint for evaluation, Hom/shift, reindexing and internal-Hom pullback. Existing resolution and tensor-Hom normalization nodes are cited directly. In particular, the parent `lem-pod-derived-automorphism-hom-evaluation` is not cited, which would create a cycle.

## Review by NO

I read delivery-errors B through E in full, the item, its chapter and unit, and the current blueprint proof at `literature/blueprint/main-20261015/blueprint/sec-poincare-duality/sk-lem-finite/prop-pod-dual-tate-data-compatibility.proof.md`. I read Stacks `sites-modules.tex`, Tag 0GMX (`remark-pullback-internal-hom`), which defines the comparison on localized-site module maps, and `sites-cohomology.tex`, Tag 0A8X (`section-hom-complexes`), Tag 08J7 (`section-internal-hom`) and Tag 08J9 (`lemma-internal-hom`), including the arbitrary first-complex/K-flat second-factor proof. These support the comparison's route and representative model; the detailed coherence calculations here are marked agent-written because those sources do not explicitly prove the item's full package.

For Step 1 I read the statements of `lem-pc-kflat-resolution`, `prop-pur-kinjective-resolutions-exist` and `lem-pod-reindexing-hom-resolution-model`. They respectively provide flat-term K-flat representatives, functorial K-injective resolutions, and preservation of these representatives and the actual product-Hom comparison under the exact inverse-image equivalence. The first two require a small ringed site, which is exactly the small pro-etale site here (with the fixed module universe). The latter explicitly covers arbitrary unbounded inputs at both B_n and the completed ring sheaf R, so no perfectness, boundedness or finite-coefficient hypothesis is silently imposed. Its completed identification commutes with quotient projections.

For Step 2 I read the complete statements of `lem-sfb-hom-kflat-chain-transpose`, the resolution-model lemma, `lem-sfb-ringed-derived-monoidal-comparisons`, and `def-coef-ringed-tensor-hom-model`. The chain-transpose statement explicitly permits an arbitrary first factor, flat-term K-flat second factor and K-injective target, and gives the local formula and inversion-of-quasi-isomorphisms normalization. All of these hypotheses hold with A=Hom(P,I), P and I as in Step 1. The model definition is used only for the fixed normalization, not as an existence theorem. The monoidal lemma gives preservation of the actual Koszul symmetry. I expanded the two cancelling differential terms and the common sign when factors are reversed. This proves equality of the specified maps and incorporates inverse localized augmentation, rather than asserting equality of unrelated replacement models.

For Step 3 I read `lem-sf-ringed-derived-closed-symmetric-monoidal`, whose statement gives a natural bijection and explicitly identifies its inverse with evaluation. Its right-tensor convention is converted to the statement's left-tensor convention by its specified symmetry. This is a bijection on derived Hom groups, so uniqueness does not depend on representing arbitrary derived arrows by chain maps. Step 4 uses that same bijection and tensorator naturality from the monoidal-comparisons statement; the displayed calculation proves the transpose formula. Step 5 uses precisely the naturality in all three variables stated by the closed lemma and tensorator naturality from the monoidal lemma. Both uncurries have the same source FM' tensor FH(M,N) and target FN', so the variance and types agree. These are elementary substitutions into cited formulas, with no extra theorem hidden.

For Step 6 I read `def-pur-hom-complex` and the resolution-model statement. The former specifies the product, degree-r differential and componentwise pre/postcomposition; the latter specifies componentwise reindexing, additivity and degreewise-identity shift comparison. I computed the scalar (-1)^(a*r), reindexed q=p+a, and verified both differential coefficients. This is the source-shift-then-target-shift convention used in the inspected Lean source. The same scalar appears on both sides of the reindexing square. Step 7 reads `def-pur-kinjective-complex` and the resolution-model statement: the definition is used only for its null-homotopy criterion, and the shift-null-homotopy argument is written explicitly. The model's representative independence and quasi-isomorphism invariance, not the definition alone, justify localization of the chain square.

For Step 8 I re-read the exact monoidal compositor equation and identity normalization in `lem-sfb-ringed-derived-monoidal-comparisons`. The typed composite comparison is evaluated twice using Step 2; naturality of the h tensorator moves G(c_g) through it, and the compositor equation identifies the resulting tensor map with the specified one for gh. The closed bijection from Step 3 then gives the asserted equality. The identity case uses the lemma's canonical identity pullback normalization, not a chosen identity equivalence. Generic off-unit tools are declared in split_report.tool_uses; none replaces the Weil-unit route.

I checked the edge cases g=id, either input zero, a=b=0, a or b negative, and coefficients of characteristic two (where signs become identities). For a=1,b=0 the adjacent-degree scalar ratio is -1 and cancels exactly the flipped source differential sign; for a=0,b=1 the reindexing has no scalar and the target shift flips the Hom differential as required. The arguments use products over all integer degrees, with no finite-product or bounded-complex shortcut. The composition calculation also works when either isomorphism is the identity. No new statement, hollow definition, duplicate, relabelled clause, unquoted non-elementary step or SGA route is introduced. Every step is below 2000 characters; the longest is the single representative-evaluation argument (1125 characters), with its non-elementary facts explicitly cited. `proof_deps` is the exact union of step uses and every citation quote was copied verbatim from the cited statement.

## Unfinished work

None in this split. The existing unsplit dependency nodes remain independent stage-1 items; this delivery does not claim to prove them or to complete the Lean formalization.

## Dry-run repair

The first server preflight parsed the TeX shift bracket `[b-a]` as a DAG-node reference. I added TeX spacing inside that bracket, matching the statement's existing notation; this changes no mathematics or citation.
