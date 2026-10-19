# Q155: lem-trf-graph-frobenius-open-exchange

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-graph-frobenius-open-exchange.json`: retained the earlier seven-step split after comparing it with the current repository and checking every cited statement. Its statement and statement dependencies are unchanged. Mathlib verdict: no match for this specified pro-etale scheme/Galois comparison square.
- `citations.json`: retained the earlier verbatim citations and checked every entry against the current dependency statements; there is exactly one entry for every step/node pair.
- `report.md`: this report and the author's source review.

No new nodes and no new Mathlib leaves. The earlier `searches.jsonl` and `write_split.py` are retained as working records; the latter was not rerun.

## Attachments

None. I searched `WeilConjectures/` in the read-only slopmaster2 source for the exact blueprint tag, scheme/Galois comparison names, and Frobenius/open/exchange terminology. I read the relevant pro-etale `GeometricFrobenius.lean` declarations and the nearby trace-formula Frobenius declarations. The former construct exchange with geometric Galois Frobenius and compatibility of `j_! -> j_*`; they do not assert compatibility with the specified scheme/Galois comparison. The latter's general Weil coefficients also do not state this square. No exact sorry-free attachment was found. The master reference checkout is not used as evidence of completion.

## WANTED

None. The current blueprint and the Stacks inputs needed for this split are present.

## What needed repair or expansion

The repository item has an empty proof. The retained attempt expands the compatibility needed in Step 2 of `prop-trf-graph-frobenius-operator`: first restrict the *specified* comparison to the open, then compare both composites using the normalized exchanges, then lift the equality using derived full faithfulness of open extension. The comparison is not replaced by an arbitrary isomorphism of pullback functors. I found no statement error and made no change to the statement.

The earlier attempt stopped before writing its report. Its proof, citations and searches remain usable. I read the logged results rather than repeating unchanged searches. The natural-language searches return bundle trivializations, scheme-module restrictions or generic pullback comparisons; the Loogle search returns ordinary adjunction Hom equivalences. The grep of AlgebraicGeometry has no Frobenius/extensionByZero hit. None states the pro-etale derived square with the specified comparison and both open exchanges. The first four Mathlib search entries were already in the current repository; the five additional searches are retained in the sandbox log with their original queries and results.

## Unfinished work

No mathematical part of this one-level split remains. The dependencies are existing nodes and their own proofs are separate items. The remote dry run and delivery are performed after this report is written.

## Blueprint route and existing nodes

I read the chapter `sec-trace-formula`, the unit `sk-d-weil`, and the current `main-20261015` proof of `prop-trf-graph-frobenius-operator`, especially Step 2. I also read the current blueprint proofs of `prop-trf-scheme-galois-comparison`, `lem-trf-absolute-frobenius-site` and `lem-trf-open-square-exchange`. This is an agent expansion of the open-extension coherence required by that route, not a change of unit or chapter route. The existing item ancestry already identifies that exact place. Whole-blueprint searches for Frobenius/open and scheme/Galois comparison, together with DAG searches, produced no distinct blueprint node stating this same square. Related coefficient-change and open-adjunct nodes state different compatibilities. All required tools are reused as existing nodes; their off-unit uses are explained in `split_report.tool_uses`.

## Not duplicates

There are no new nodes, hence no new/existing same-tag pairs. In particular, the pullback-naturality result is the existing `lem-pur-frobenius-trivialization-pullback`, and the derived open-unit/full-faithfulness result is the existing `lem-sf-open-tensor-normalization`. Neither is restated as a new node.

## Review by Q155

I reviewed delivery-errors B through E against the retained JSON, the current cited node statements, and the source text. For the item I read the current graph-operator proof's Step 2 and the displayed construction of kappa in the current scheme/Galois proof. The latter defines precisely the comparison used in Step 1. I read Stacks Tag 0F6W (`more-morphisms.tex`, `lemma-relative-frobenius-weakly-etale`), which supplies relative Frobenius for weakly etale site objects, and Tag 0D6D (`sites-cohomology.tex`, `lemma-derived-pullback-composition`), which computes composition on K-flat representatives. I also read Tag 0GL1 (`lemma-j-shriek-and-tensor`); it alone does not state the full open-unit normalization. The split instead explicitly cites the existing stronger normalization node. There are no new nodes whose sources or edge cases remain to review, and no prohibited SGA route is used.

Step 1 uses the *statements* of `prop-trf-frobenius-factorization` and `def-trf-scheme-frobenius` to obtain H = g_sigma^m Phi^m and g = g_sigma^{-1}, hence Phi^m = g^m H. The composition node supplies P -> T G, the absolute-Frobenius-site node supplies the iterated trivialization, and the scheme/Galois node supplies natural comparisons compatible with this factorization. The item's own specification fixes the comparison by exactly these constructions; the current blueprint verifies the displayed formula kappa = t G composed with c. Both X_0 and Y_0 are finite type, and A is the required finite commutative prime-to-p coefficient ring (a power of ell annihilates it). Characteristic p follows from the finite-field datum. The Galois and absolute maps are scheme morphisms; they are not assumed to be k-morphisms.

Step 2 cites the constant-ring-map node for the unique identifications preserving constant sections, the tensor-composition-unit node for the explicit local generator formula, the constant-exact node for exact inverse image, the localization-universal-property node for descent of transformations and equality, and the derived-composition node for agreement with the specified termwise comparison. I checked each of these assertions in its statement, rather than borrowing a construction available only in its proof. The scalar expression for three pullbacks is the same in either parenthesization; the base-change reassociations have the same projections. This is a routine computation from the cited explicit comparison, not a new coherence theorem asserted without argument. Exactness permits termwise descent on complexes, and the localization node explicitly states both descent and faithfulness on transformations. Finite constant coefficients and their isomorphic coefficient maps meet the hypotheses throughout.

Step 3 cites `lem-trf-frobenius-open-square` for the commuting Cartesian squares and the composition node for their restriction comparisons. The full statement of `lem-pur-frobenius-trivialization-pullback` explicitly gives t_X composed with alpha_T = r(t_Y), identifies its trivialization with that of Step 1, and covers all iterates. Its hypotheses hold with u = j and b = am. Combining this equality with Step 2 gives the displayed comparison equation; both its sides have source r P_Y N and target T_X G_X r N. This avoids treating unspecified isomorphisms as canonical ones.

Step 4 is substitution of Step 1 into Step 3 and one naturality square of t_X. Its displayed three-line calculation proves the restriction identity for kappa. It requires no additional non-elementary input beyond the earlier steps.

Step 5 takes isomorphic derived open units from the statement of `lem-sf-open-tensor-normalization`, Cartesianity from `lem-trf-frobenius-open-square`, and the natural exchanges with identity normalization from `lem-trf-open-square-exchange`. I checked that the normalized equations have source r P_Y j_!M or r G_Y j_!M and target P_X M or G_X M. The ambient categories are the ordinary derived categories of constant pro-etale modules, exactly among the categories in the normalization statement; no etale comparison, completion, or geometric-stalk conservativity is being used. The canonical pullback-composition identifications are those computed in Step 2.

Step 6 applies the restriction identity and the two equations of Step 5, then naturality of kappa and of the inverse open unit. The calculation keeps both morphisms in the same Hom group. Cancellation uses an isomorphism nu, not an unjustified restriction-detects-maps claim.

Step 7 invokes the normalization node's explicit derived full faithfulness. Precomposition by b_P^{-1} puts both maps between two objects in the image of j_!, where full faithfulness and the unit formula identify maps with their restrictions. Thus Step 6 implies the original equality. The naturality assertions used at the end are in the statements of the scheme/Galois and open-exchange nodes. This is a direct short application of those cited results. The proof works for each arbitrary m >= 1 using am, and introduces no Weil structure on M.

For the small cases, when j is the identity the exchanges and units normalize to identities and the equation is kappa = kappa. For the empty open every extended object is zero and the same calculation is valid. For M = 0 both sides are zero. At m = 1 the exponent is a, so the formula compares q-power scheme Frobenius with the geometric inverse of arithmetic Frobenius, not the opposite Frobenius. Taking X_0 = Y_0 = Spec(k_0) checks this inverse convention directly in the factorization. No reducedness, smoothness, properness, or k-linearity of the Galois map was introduced.

The B checks are vacuous for new-node form but I checked the retained item's notions, TeX, recorded searches and blueprint place. For C, every external input has an existing cited statement and an exact quote in citations.json; elementary substitutions refer only to previous steps. For D, the proof actually derives the square and creates no clause-restatement nodes. For E, the coefficient categories, morphism directions, finite-field hypotheses and arbitrary iterates agree with the source. All seven steps are below 2000 characters; I nevertheless checked the coherence calculation in Step 2 for a hidden lemma and found it is the written local-generator reassociation from the cited explicit formula. I found no source error requiring STATEMENT-DISPUTED.
