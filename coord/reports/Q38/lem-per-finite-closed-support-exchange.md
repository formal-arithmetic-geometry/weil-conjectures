# Q38: lem-per-finite-closed-support-exchange

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-finite-closed-support-exchange.json`: statement, split into seven steps; no Mathlib match for the complete exceptional comparison and its normalization.
- `citations.json`: verbatim statement quotations for every step/node citation.
- `report.md`: this report. Existing `searches.jsonl` retained, read and reused; one subsequent LeanFinder response was read in full and retained in that log.

New nodes: 0. New Mathlib leaves: 0. Existing Mathlib leaves are cited, not duplicated.

## Attachments

None. Searches under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` by the exact blueprint tag and by closed/finite exchange and support terminology found no declaration giving this entire statement. The finite base-change declaration `AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isFinite` in `SixFunctors/Finite/BaseChange.lean:333` is ordinary inverse image, not this exceptional inverse image and counit identity. The closed-immersion file provides ordinary full faithfulness, while `Etale/Derived/UpperShriek.lean` defines a general exceptional right adjoint subject to an existence hypothesis and includes sorry declarations. Neither is an attachment for this item. No Lean files were written and no compiler was run.

## WANTED

None. The source PDF and all used Stacks sources are available locally.

## Corrections and scope

The statement's citation to `def-amb-etale-compact-support` did not supply either closed adjoints or finite exactness: its statement defines a compact-support candidate. Replace that citation with `def-weil-pbc-direct-image` and `lem-exc-closed-ambient`, and use the actual finite exactness theorem in the proof. Spell out the existing Noetherian convention inline. No hypothesis, conclusion, coefficient category, or normalization was changed. No STATEMENT-DISPUTED is needed.

The original item had no proof. ILO XVII, proof of Proposition 5.4.1, printed p. 291 (PDF page 297) supplies the application of closed extraordinary restriction to the finite-gluing counit. Its compressed chain of evident functor isomorphisms did not spell out which isomorphism fixes the counit. The proof here is marked agent-written because it expands this into a particular Hom-bijection construction and verifies the arrow explicitly.

The chapter and unit records and the current main-20261015 ancestor `lem-per-artin-gabber-affine-curve` were read. This is the generic closed-support subargument in the existing finite-modification/potential-dualizing expansion of Step 3. There is no change of the unit's perverse/Fourier route. Off-unit generic tools are declared individually in `split_report.tool_uses`.

## Searches and reuse

The sandbox initially contained searches.jsonl only, not an earlier split or report. I read all logged queries and the recorded hits. Those hits concern ordinary scheme modules, ordinary pullback/pushforward, scheme base-change stability and general adjunctions. They do not give the claimed exceptional comparison with the normalized counit. I reused them in the node, retaining every inherited search as well. In particular two semantic phrasings and local CategoryTheory greps are already recorded; no absent search was invented. The additional full LeanFinder response again gives scheme-module pseudofunctor identities, `SheafOfModules.pullbackComp`, and related ordinary functor identities, not this statement.

Before considering a helper node, I searched the whole DAG by the closed-support, finite-direct-image, adjunction, base-change, Yoneda and exactness notions, and used `blueprint_refs.py search` for `closed support`, `closed extraordinary`, `finite exchange`, and `finite direct image`. Existing statements suffice; no helper was created. The affine proof of finite base change and the categorical transpose calculation belong in the item's steps, not in extra nodes.

## Not duplicates

No new nodes, hence no new/existing same-tag pairs. The ordinary finite-exchange and closed-full-faithfulness nodes are explicitly reused. The general coyoneda-isomorphism node is used in the opposite category; the scheme-valued Yoneda node was rejected because it is not the general categorical statement needed here.

## Review by Q38

I read ILO XVII printed pp. 291–292 in the supplied PDF, especially the paragraph asserting that applying i! to q_*K_(Y') -> p_*K_(X') is an isomorphism. I also read Stacks `etale-cohomology.tex`, Tag 04CA (`proposition-closed-immersion-pushforward`), Tag 03QP (`proposition-finite-higher-direct-image-zero`), and Tag 0959 (`lemma-finite-pushforward-commutes-with-base-change`), together with the module-kernel/cokernel description used to pass to constant A-module sheaves. The corresponding existing DAG statement files were opened, not just their titles or proofs. No SGA source is used.

Step 1 uses the closed-base-change, closed-finite and finite-composition statements for exactly their stated geometric properties. The remaining finite-base-change assertion is proved on the actual quotient affine chart B/IB: the finite generators of B map to generators over R/I. Thus there is no inference merely from an image lying in a closed set. The direct-image composition c is calculated on V ×_X Y', using the statement of the direct-image definition. Nothing is taken from another node's proof.

Step 2 takes exactness only from the finite-direct-image-exact statement, rather than from the compact-support definition. That statement concerns abelian sheaves, so I wrote the passage to modules: the defining kernels and sheafified cokernels forget to their abelian counterparts. The inverse-image-exact statement and the module inverse-image adjunction give the exact linear adjunction, and the exact-derived-adjunction definition specifies its localized units and counits. The exact-functor-derived-functor statement justifies computing Rp_* by p_* on D+. These are ordinary small-etale constant-ring module categories throughout; no pro-etale or condensed-ring theorem is silently substituted.

Step 3 uses precisely the existence of the ordinary closed right adjoint from `lem-exc-closed-ambient`. That statement alone does not assert boundedness preservation. I therefore checked it directly from the adjunction and the standard t-structure: exact closed pushforward preserves D^{<=n-1}, so orthogonality shows that its right adjoint preserves D^{>=n}. This justifies the D+ domain without requiring any exceptional functor for p. The finite-ring hypothesis matches the cited closed-adjoint statement.

Step 4 takes the actual ordinary counit isomorphism from `prop-openclosed-lowerstar-fully-faithful`, its linearity from the module adjunction, and its localization from the exact-derived adjunction. The fully-faithful criterion applies to i^* left adjoint to i_*, not to the exceptional adjunction in the wrong orientation. Full faithfulness then makes the unit of i_* left adjoint to i! invertible by the displayed Hom calculation. The cited general coyoneda theorem is applied to the opposite derived category, so its covariant Hom statement gives precisely the required contravariant representable conclusion. The normalization is this unit's inverse, not an unspecified equivalence.

Step 5 applies finite base change with finite map i and arbitrary base-change map p. This is the square that gives p^*i_* -> i'_*p'^*, not the distinct comparison i^*p_* -> p'_*i'^*. I checked each of the five Hom adjunction directions and the source and target of theta. All are on bounded-below ordinary A-module derived categories, where Step 2 and Step 3 supply the functors. The exchange is linear and invertible before localization, so its termwise inverse descends. Natural Hom bijections and the same coyoneda statement give delta; this is a particular isomorphism natural in M.

Step 6 is the substantive normalization calculation, written out rather than hidden by the word 'transport'. The equation with the ordinary counits a and a' is the defining base-change restriction equation, evaluated on the actual fibre product. Tracing the identity through Step 5 gives e' i'_*(a') theta; that equation and naturality of a identify its p-adjunct as E = p_*e' composed with c. Its final i-adjunct is delta = i!(E) composed with the closed unit. Every displayed composite is typed on the indicated schemes. The proof uses the definition's canonical exchange, not a merely existential isomorphism, and invokes only the ordinary adjunction triangle identities.

Step 7 is then the equality delta^{-1} i!(E) u = identity. This checks the precise source normalization by u and target normalization by delta^{-1}; it proves every clause of the item's assertion, including that the original counit-induced map is an isomorphism. It does not replace the claim by a new lemma restating a clause.

For edge cases I checked empty Y and empty X' (the zero derived category and identity of the zero object), identity i (both sides are p_*M and the counit is the identity), identity p (the construction reduces to i!), and arbitrary noninvertible coefficient characteristic. The argument never assumes etaleness of p, flatness of p, reducedness, regularity, positive dimension, constructibility, or invertibility of |A|. Nonreduced closed subschemes are handled by the same quotient chart and closed-immersion theorem. All seven proof steps are under 2000 characters, and none hides an independent geometric or comparison lemma: the only comparison is the item's own Hom/counit calculation. I checked delivery-errors B–E against the files: all reused statements say what is taken, all non-elementary facts are cited, and every citation has a verbatim quotation in citations.json.

## Unfinished work

No mathematical subargument remains to split in this item. The required server dry run and final push follow; their result is reported by the delivery tool.
