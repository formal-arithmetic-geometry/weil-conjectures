# Stage-1 worker report: lem-sp-section-dnc-integration-square

## Files written

- dag/nodes/sec-smooth-purity/lem-sp-section-dnc-integration-square.json: statement, split; six proof steps, unchanged statement and statement dependencies; no Mathlib match.
- citations.json: one verbatim statement quotation for each of the eleven node citations in the proof.
- searches.jsonl: the five real searches performed through msearch.py; all services answered. No new nodes and no Mathlib leaves.

## Attachments

None. Searched the upstream WeilConjectures tree for the exact blueprint tag and for deformation, section invariant, normal bundle, orientation, integration and base-change notions. Read the declaration index in Purity/Smooth/Deformation.lean and Orientation.lean. The family and section comparison theorems do not state the subsequent integration square together with its diagonal normalization. No declaration found proves every clause of this item, so partial results were not treated as an attachment.

## WANTED

None. This is an agent-written assembly of existing DAG interfaces following the available current blueprint, not a claim that a missing reference contains the whole item verbatim.

## What changed

The imported node had no proof. Its mathematical statement is retained, including the actual normal bundle, arbitrary non-flat base change, rank zero, empty schemes and the specified diagonal orientation. The proof now displays two equations, delta' c_s = c_N b*delta and (z'*b_N') c_N = b*(z*b_N), and composes them. It also explicitly handles the ordinary-etale realization of vector-bundle purity before using it on the pro-etale site. No statement dispute was found and no hypothesis was added.

The argument follows Proof (1) of main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-purity-bc/sk-prop-sp-purity-bc-factors.proof.md and the orientation paragraph of its unit. The inherited Q115 argument, whose report is named in source.place, is preserved below. No unit realization is edited: this item is an intermediate lemma, not the unit's key statement.

## Not duplicates

No new nodes were created. The searches of the whole DAG and blueprint (blueprint_refs.py searches for deformation, integration and DNC) found the existing ingredients, which are reused. thm-pur-dnc-invariance supplies the deformation arrow and its naturality; cor-pur-vector-bundle-purity supplies integration and its compatibility. Neither alone states the composite and its diagonal identification. lem-pur-vector-integration-site-comparison already states the needed comparison of actual integration arrows; creating another site-comparison lemma would duplicate it.

## Review by Q73

I read the chapter and unit records and delivery-errors B--E, then the current item and every statement cited below. I read the current blueprint proof of det-sp-purity-bc-factors (1), the current DNC-invariance proof and the original DNC statement/proof, the current vector-bundle-purity proof and its expanded live statement, and the current orientation-charts proof. I also read the live diagonal-dualizing-object proof to check the direction of the composite. The Stacks inputs for the existing site-comparison and mate facts are proetale.tex, Tags 09AF (lemma-jshriek-comparison) and 099R (section-comparison), categories.tex Tag 0B65 (lemma-transformation-between-functors-and-adjoints), and sites-cohomology.tex Remarks 0E46/0E47 (remark-compose-base-change and remark-compose-base-change-horizontal). These generic sources do not by themselves prove the normalized integration comparison; that specific assertion is supplied by the existing site-comparison node, whose complete statement I read. No SGA route was used.

Step 1 uses def-pur-conventions only to specialize E=Q_ell, varpi=ell, n=r. The statement of lem-pur-dnc-section-geometry really gives the two fibres, the punctured trivialization, the standard model and base change of the Rees family and family object. The base-change hypothesis is a smooth morphism with a closed section. I did not apply arbitrary-base-change compatibility to an arbitrary blowup or arbitrary closed immersion. N is the actual normal bundle from the zero fibre, not a chosen affine space.

Step 2 uses the statement of thm-pur-dnc-invariance, which explicitly quantifies over all finite-type separated k-base changes, with no flatness. Its coefficient stage specializes exactly to R. def-pur-finite-section-comparison defines the ordinary/pro-etale section comparison using the actual exceptional functor and comparison pullback; def-pur-co-smoothness specifies beta as the transpose of inverse compact-support exchange followed by the pulled-back counit. Thus c_s and c_N denote the prescribed maps, rather than orientations chosen to force an equation. All sources and targets are section invariants on B'.

Step 3 uses the full map-level assertion of lem-pur-vector-integration-site-comparison: it identifies the two integration adjuncts and says their inverse is the orientation of cor-pur-vector-bundle-purity. The separate statement of thm-cbc-finite-level-proetale says precisely that the compact-support exchange is transported through proper/open and pullback comparison, independent of witnesses. Finite-type separated bases are qcqs; the vector bundle admits its projective completion, and the coefficient and dualizing objects under consideration are bounded etale-origin objects, as in the site-comparison statement. The explicit mate-pasting and conjugation equations of lem-weil-pbc-mate-pasting identify the two transposes of that same square. This repairs the potential category mismatch: ordinary-etale compatibility is not silently asserted on an arbitrary ambient pro-etale adjunction. This generic categorical tool is declared in split_report.tool_uses; it does not replace the unit's geometric route.

Step 4 cites cor-pur-vector-bundle-purity for its actual displayed gamma equation, not merely the existence of some purity isomorphism. At K=R_B its gamma is b_N inverse by its independent integration normalization. I checked the inverse algebra: e pull(gamma)=gamma' a implies b_N' e=a pull(b_N). Pulling back by z' produces exactly the normal-section square with c_N. Both bundles have rank d over Noetherian finite-type k-bases and ell is invertible. No scalar extension or flatness hypothesis is introduced.

Step 5 is elementary composition of the preceding two equations, with the source b*C(g,s) and target R_B'(d)[2d] on every line. Identity base change gives the identity square. Rank zero has no coordinate factors and uses R(0)[0], including when a smooth relative-dimension-zero map has extra components away from its section. Empty base or source gives zero objects and unique morphisms. A test non-flat base change is Spec(k) to Spec(k[epsilon]/epsilon^2) for the standard pair A^d_B: the Rees coordinates u_i=x_i/t, the zero bundle and both normalized maps pull back exactly as asserted. None of the cited compatibility statements asks for flatness.

Step 6 uses lem-pur-diagonal-base-change for C(p1,Delta) to omega_f and det-sp-orientation-charts for the explicitly stated composite beta delta alpha inverse and its coordinate-adjunction normalization. I checked p2 Delta=1, alpha=kappa, and beta=z*b_N. This identifies the requested map by substitution; no separate node restating the diagonal clause is created. The target Y here is separated, so the separated-target formula applies on the whole target.

For C1/C4, every non-elementary use is a cited statement and every quotation in citations.json is verbatim from that statement. proof_deps is their union. No argument relies on an auxiliary construction only present inside another node's proof. Every step is under 2000 characters, and the only elementary step is the displayed composition and its degenerate cases. B1--B10 and D1--D5 create no new-node issues: there are no new nodes, proofs were not moved to renamed clauses, and no unrun search is recorded. I read every msearch hit: manifold vector-bundle pullback, sheaf/global-section naturality and condensed-module naturality are not the claimed etale/pro-etale DNC/integration theorem. Two semantic phrasings, Loogle and source grep found no exact result.

## Validation

The first dry run rejected two quotation fragments as shorter than forty characters. Both were replaced by the full relevant statement paragraphs, retaining the exact coefficient datum and the full diagonal-isomorphism formula.

## What remains unfinished

Nothing remains for this stage-1 split relative to its cited existing nodes. Their proofs are independent DAG tasks; no claim is made to have written or compiled Lean. No agents were started. The maintainer will perform the independent delivery review.

## Appendix: inherited argument

### Old step 2

For this smooth closed-section pair, let $N=N_{\Delta/W}$, with projection $\pi_N$ and zero section $z$, and let $\delta:C(p_1,\Delta)\xrightarrow{\sim}C(\pi_N,z)$ be [thm-pur-dnc-invariance]. By [lem-pur-dnc-section-geometry](1),(5), the deformation family and its fibres commute with the arbitrary base change $u$; taking the fibre at $0$ identifies the primed normal-bundle pair with the pullback of $(N,z)$. The rank is $d$ by [lem-pur-diagonal-regular-immersion]. Write $b_N:\omega_{\pi_N}\xrightarrow{\sim}R_N(d)[2d]$ for vector-bundle purity. By [cor-pur-vector-bundle-purity], $b_N$ commutes with base change and with the adjunction comparisons. The diagonal orientation is the composite
$$\Pi_{f,R}:\omega_{f,R}\xrightarrow{\kappa_f^{-1}}C(p_1,\Delta)\xrightarrow{\delta}z^*\omega_{\pi_N}\xrightarrow{z^*b_N}R_X(d)[2d].$$
This spells out the canonical diagonal construction of [thm-pur-diagonal-dualizing-object]; its chart normalization is exactly [det-sp-orientation-charts]. The first arrow respects the exchange by step 1, the second by the arbitrary-base-change assertion of [thm-pur-dnc-invariance], and the third by vector-bundle purity. Pullback of the displayed three-arrow composite is therefore its primed composite, so $\Pi_{f',R}e_{1,R}=u_R^*\Pi_{f,R}$. Taking inverses gives $e_{1,R}u_R^*a_{f,R}=a_{f',R}$. Here $u$ need not be flat: DNC base change is used only for a smooth morphism with a closed section, precisely the hypothesis of the cited geometry and invariance statements.

Uses: thm-pur-dnc-invariance, lem-pur-dnc-section-geometry, lem-pur-diagonal-regular-immersion, cor-pur-vector-bundle-purity, thm-pur-diagonal-dualizing-object, det-sp-orientation-charts.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-purity-bc/_section.md; Orientation paragraph: deformation, normal bundle, vector-bundle integration, and coordinate normalization.
