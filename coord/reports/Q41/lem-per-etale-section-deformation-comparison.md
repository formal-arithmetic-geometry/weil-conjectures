# Worker report — lem-per-etale-section-deformation-comparison

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-etale-section-deformation-comparison.json: existing statement, now split into eight proof steps. Statement and statement dependencies preserved. Mathlib verdict: no match.
- citations.json: 30 verbatim statement excerpts backing every proof-step citation.
- searches.jsonl: five actual msearch.py calls, including two semantic phrasings; existing inherited item searches retained in the node.
- report.md: this report. No new nodes, no Mathlib leaves, no unit file changed.

## Attachments

None. I searched WeilConjectures/ in the read-only slopmaster2 source for the exact blueprint tag, deformation/section/etale terms, normalCone and sectionInvariant. The closest declaration is AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_normalCone, WeilConjectures/EtaleCohomology/Purity/Smooth/Deformation.lean:63. Its proof is sorry, and its Nonempty conclusion omits the equality of specified maps. The geometry existence declaration in AlgebraicGeometry/DeformationToNormalCone.lean also has sorry and its data are not tied to the actual conormal bundle. Neither is an attachment. The upstream master checkout is not used as proof evidence.

## WANTED

None. The current blueprint proof and the Stacks source used for the elementary algebra and formal coherence are present locally.

## Corrections and route

The item was statement-only. Its statement is mathematically consistent and is unchanged: the asserted identity concerns the actual normal frame from the ideal and the actual ordinary-etale adjunction maps. No statement dispute arose.

The proof does not identify an etale chart with affine space. It constructs the base-changed extended-Rees chart and compares both families using smooth exceptional base change. The whole content is not moved into a new lemma: the two fibre equations, normalization, and final cancellation are written in the item itself. No Tate orientation or orientation-invariance assertion is needed.

I read the fixed chapter sec-deligne-laumon-a1 and unit sk-p-dl-a1-perverse. This auxiliary item originates in the Artin–Gabber/duality branch through lem-per-ordinary-smooth-orientation, not in a replacement argument for Fourier exactness. All generic off-unit geometry and adjunction interfaces are declared in split_report.tool_uses, with reasons. The blueprint ancestry stays as imported, with the already precise Local construction place and the existing via chain.

## Not duplicates

No new node is proposed. Searches of the whole DAG and tools/blueprint_refs.py for deformation, etale and normalized found the existing ordinary-etale section-specialization theorem, which is cited. The field-based pro-etale sk-thm-dnc, thm-pur-dnc-invariance and lem-pur-diagonal-dnc-chart-normalization are not equivalent to this arbitrary-Noetherian ordinary-etale equality of maps; same_as remains []. The generic compact-support composition, etale normalization and mate-pasting facts were already nodes and are reused.

## Review by Q41

I read the current main-20261015 sk-thm-dnc.proof.md in full, especially Local construction, normalization at t=1, and Gluing. The item makes its coordinate normalization explicit in ordinary etale categories. For its algebra I read Stacks algebra.tex, lemma-flat, Tag 00HD, and morphisms.tex, lemma-flat-characterize, Tag 01U5. I also read morphisms.tex, lemma-base-change-etale, Tag 02GO; schemes.tex, lemma-separated-permanence, Tag 01KU; etale-cohomology.tex, lemma-shriek-base-change, Tag 03S6; and sites-cohomology.tex, remark-compose-base-change and remark-compose-base-change-horizontal, Tags 0E46 and 0E47. The last two say their verification is omitted; our use is backed by the existing explicit mate-pasting node, not by treating an omitted verification as a proof. The proof is marked agent-written because it supplies the formal comparison calculation rather than just following the blueprint's orientation trivializations. No SGA source is used.

Step 1 uses the statement of lem-pur-noetherian-etale-section-specialization, not its proof: it explicitly supplies the actual smooth deformation, both canonical exceptional fibre identifications, the uniquely normalized kappa, and its zero specialization delta. Its Noetherian, regular-section, finite-coefficient and compactifiability hypotheses are exactly those of our item. sbc-lem-affine-space-smooth supplies dimension d for q and Q. The fibre maps theta_0 and theta_1 are retained so inversion has the correct direction.

Step 2 uses def-weil-etale-morphism for flatness, the affine flatness criterion for B flat over P, and lem-weil-pbc-flat-tensor-exact for the injections of every ideal power after tensoring. I checked that the centre hypothesis gives I=JB, without asserting B=P. The Laurent-piece and monomial formulas then prove the Rees identification directly. The isomorphisms are fixed on B, t and x_j/t, so they glue; this is an explicit elementary algebra calculation, not a new unproved Rees lemma.

Step 3 uses etale base-change and separated finite-type base-change exactly as their statements allow, with E the base change of e. The conormal-algebra node specifies the degree-one class map; section-specialization specifies the actual zero fibre. Evaluation at 1 gives e, while reduction of e*x_j/t modulo t gives the ideal class defining lambda. Thus a different normal frame cannot silently appear. The deformation open contains all of the section and of the zero fibre because those map to the centre inside U.

Step 4 checks the hypotheses for every subsequent citation. The finite-type-over-Noetherian lemma gives the polynomial schemes; the section-specialization statement gives D; the open-subscheme lemma gives U and D_U. Open-immersion-etale supplies etaleness of j,J, while finite type follows from quasi-compact opens and being locally an isomorphism. Smooth permanence preserves dimension d on these restrictions. Locally-Noetherian-quasi-separated and Noetherian quasi-compactness supply Nagata's target conditions. The required compactifications for the restrictions and chart maps therefore exist; the explicitly assumed g, pi and deformation compactifications are respected. Finite A and invertibility of its killing integer ell^n are checked before using ordinary smooth exceptional base change.

Step 5 uses five statements that I opened: ordinary etale locality, smooth exceptional base change, unbounded compact-support comparisons, etale compact-support normalization, and mate-pasting. The composition/exchange coherence is explicitly in the compact-support comparisons statement; normalization explicitly identifies etale sum-extension exchange and its counit; mate-pasting gives equality after taking the relevant mates. Smooth-base-change identifies its map as the counit mate. The displayed locality/base-change square is obtained by these two pastings and the change-of-adjunction clause. This is a short formal instance of already stated general identities, not an additional geometric comparison lemma hidden in the proof. The identity and repeated-base-change assertions use the corresponding identity/pasting clauses. The proof never takes counit preservation merely from the existence of an unspecified isomorphism.

Step 6 uses locality for J and E, with the inverse on the Q,E side, to produce tilde-chi from F to the standard family. Smooth base change supplies eta in the opposite direction from a*C_q to that family, so H=eta^{-1} tilde-chi has the claimed type. Inverse-image-modules-exact explicitly gives exact constant-coefficient inverse image; no derived coefficient-change or completed category is substituted.

Step 7 applies the Step 5 identities to the actual maps of Step 3. At zero J is identity on N and E is lambda; at one J is j and E is e. The affine product's repeated base change along a followed by i_r is the identity base change of q. Consequently the canonical fibre map cancels eta, giving the two displayed equations for H. Both equations are written with theta_r, and the uncancelled zero equation is also given, so this step does not conceal an unspecified transport or assume the conclusion.

Step 8 is the normalization calculation: a*(chi_e^{-1})H restricts to theta_1, so the uniqueness clause of the section-specialization statement identifies it with kappa. Its zero restriction is chi_e^{-1} chi_lambda theta_0. Inverting and composing with theta_0 gives delta=chi_lambda^{-1}chi_e with the right direction. The conclusion follows by cancellation.

For small cases I checked empty S and rank zero explicitly. In rank zero the centre condition forces U=s(S); there is no monomial generator, so the chart calculations still work. Nonreduced affine bases such as k[epsilon]/(epsilon^2) cause no failure: the proof uses flatness over R[x] and free monomial coordinates, not a domain assumption. I also checked the genuinely nontrivial etale chart over a field of characteristic different from 2, with B=k[y,y^{-1},(y+1)^{-1}] and x mapping to y^2-1, section y=1. Its zero inverse image is the single section but the chart is not an isomorphism to affine space. The formula is B tensor_{k[x]} k[t,u] with x=tu, and the zero coordinate is [y^2-1], exactly the induced conormal frame.

Against delivery-errors B–E: no new node needs a separate statement/search audit; every non-elementary input is one of the 20 existing cited statements and the citation excerpts are literal substrings. No argument uses the proof of a cited node. The dependency union is recomputed, all proof steps have Boolean elementary fields and sources, and no non-elementary step exceeds 2000 characters. The brief's three common node-creation errors are avoided by giving the Rees computation and mate-pasting instance as explicit proof steps. I corrected the draft to cite smooth-relative-dimension permanence explicitly when checking the chart restriction hypotheses. The final statement and statement dependencies remain unchanged.

## Unfinished work

None in the mathematical split. Required server dry run and delivery follow this report.
