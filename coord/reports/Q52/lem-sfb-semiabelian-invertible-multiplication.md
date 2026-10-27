# Stage 1: lem-sfb-semiabelian-invertible-multiplication

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-semiabelian-invertible-multiplication.json: existing statement, split into six steps; statement and statement dependencies unchanged; no Mathlib match.
- citations.json: literal statement excerpts for every citation in every step.
- searches.jsonl: searches actually run through msearch.py. Existing source-node searches retained, and six Q52 searches added after reading the returned hits.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. The whole-DAG search found the smaller inputs already present, so creating replacements would duplicate them.

## Attachments

None. Searching lean/WeilConjectures by the item tag and by semiabelian/SemiAbelian/Semiabelian found no declaration. The abelian-variety declarations etale_npow_id, isFiniteLocallyFreeOfDegree_npow_id and singleton_mem_fppfPrecoverage_npow_id have the proper abelian-variety hypothesis, which the semiabelian item does not have. They are inputs already covered by existing DAG nodes, not an attachment for this item.

## WANTED

None. All sources used are available locally. I read Milne Algebraic Groups §8.21 on printed p.152 (PDF p.164), Stacks groupoids.tex at lemma-degree-multiplication-by-d (0BFG), lemma-abelian-variety-multiplication-by-d-etale (0BFH), proposition-review-abelian-varieties (03RP), algebra.tex at definition-standard-etale (00UB) and lemma-standard-etale (00UC), and examples-stacks.tex at lemma-finite-etale-stack (0BLZ). The extension proof is explicitly marked agent-written: Milne §8.21 alone is not a theorem about semiabelian algebraic spaces.

## Audit findings and route

The imported item has a correct self-contained statement but no proof. No statement dispute arose. Its source note proposes local trivialization of the torus torsor and descent; that is exactly the proof now written, without assuming that the group space G is a scheme. The abelian quotient is treated by existing abelian nodes. The local fibre is written as a root scheme over arbitrary affine test schemes, and finite etale scheme descent then proves representability.

I read AGENTS.md, GOAL.md, the stage-1 brief, worker role, stage-1 document, SETUP's fixed chapter/unit/free node hierarchy, the chapter and unit records, and delivery-errors B–E in both copies. I read the latest blueprint's sk-thm-sf-ctf-stability unit and det-thm-sf-ctf-stability-direct-images proof, from the latest symlink (recorded latest commit 7284bb09daf97437d544c51882b325f9c52cd345). I preserve the inherited alteration/Picard supporting route below the unit; no chapter or unit file is changed. The blueprint ancestor command returns None for this auxiliary chain, as it does for nearby reviewed nodes, so the inherited null ancestor and detailed place are retained. Searches of the whole blueprint for semiabelian, finite etale torsor, multiplication invertible, monic derivative, and finite etale descent found no equivalent blueprint item. The broad multiplication search was read for the abelian matches. Whole-DAG concept and source-tag searches found the exact reused nodes; all their statements were opened.

Mathlib search: the two distinct LeanFinder phrasings, LeanSearch, Loogle's AlgebraicGeometry/npow pattern, and two grep patterns are recorded as run. Hits were ring-etale/standard-etale declarations, morphism permanence, affine space surjectivity, and a Galois-category result. The standard-etale and permanence inputs have existing DAG leaves. None states the semiabelian item or specializes to it in one line. No service was unavailable in these searches. No Lean was written or compiled, and no repository or launcher file was written.

## Not duplicates

No new nodes were created. The split cites the existing monic-quotient, standard-etale, abelian multiplication, fppf base-change and finite-etale descent nodes directly. A separate torus-power node would be an elementary specialization of those algebra statements; a separate translated-fibre node would be the explicit two-formula calculation already given in step 4.

## Review by Q52

I checked the proof with each cited statement open, against C1 and C4 rather than relying on source tags. Step 1 uses exactly the power basis asserted by lem-weil-pbc-monic-quotient-free and the derivative-localized etale algebra asserted by lem-weil-pbc-standard-etale-monic-derivative. The equations z^n=u and z^{-1}=u^{-1}z^{n-1} prove the derivative is a unit even over a nonreduced base. The two composition nodes state finite and etale composition. Existence of an algebraic closure and roots is explicitly the statement of def-weil-algebraic-closure; these give a point over every base prime, so surjectivity is proved, not silently inferred from finiteness. The t=0 algebra is B itself. No extra torus lemma is concealed in this coordinate calculation.

Step 2 uses lem-sc-isogeny-facts for finite flat surjectivity and the fppf-cover assertion, and lem-sc-mult-n-etale-kernel for etaleness of the multiplication morphism itself, not merely its kernel. These statements apply to an abelian variety over the given algebraically closed field and n≥1. The field-unit assumption excludes the positive characteristic dividing n. Their statements include dimension zero; the zero abelian variety is the identity case even though the iff formulation of Stacks 0BFH is stated for nonzero abelian varieties. The fibre product node gives the scheme W and tautological section a. Finite and etale base-change statements give finiteness and etaleness, and the exact covering-family base-change statement gives surjectivity through the fppf covering. I declared the two abelian results as generic off-unit tools.

Step 3 uses algebraic spaces as fppf sheaves and the given hypothesis of exactness, which explicitly promises local lifts over every scheme. Thus a is lifted on an fppf cover of W, not on an unsupported cover of the original U. The fppf site axioms allow affine refinement and composite coverings. q(y−ng_i)=0 proves membership in the stated kernel T. These are elementary sectionwise calculations from the definitions and hypothesis. In particular no representability or flatness of G→A is assumed.

Step 4 uses only the earlier coordinate construction and the group's definitions: x−g_i lies uniquely in T, and n(g_i+t)=ng_i+nt. Both forward and inverse natural maps are written for all scheme-valued sections, so the model is an isomorphism of sheaves over W_i even when W_i is nonreduced. It is not just an equality of geometric fibres. This elementary identification is not made into a new node.

Step 5 cites the local-representations full-faithfulness statement for scheme overlap maps induced by local representations of one fppf sheaf; its statement explicitly permits set-indexed covering families and says compatible local isomorphisms glue globally. The cocycle is equality on the shared x-coordinate. The finite-etale descent statement explicitly supplies an effective finite etale scheme over arbitrary W, so no noetherian, quasi-compact or constant-rank restriction is introduced. Applying full faithfulness to the descended scheme and V identifies their sheaves. Surjectivity is proved by choosing a covering point and a point of its local root scheme. This full-faithfulness input is recorded as a generic off-unit tool.

Step 6 uses the exact finite and etale composition clauses. The two surjections compose by elementary set theory on points. The comparison preserves the maps to W and U, so the represented object is the required fibre product with its actual projection, not an abstract finite scheme. The arbitrary scheme test establishes representability and all claimed properties.

Small cases checked: n=1 gives one root with z=u and hence the identity fibre; t=0 removes all root variables; G=T and A=0 reduce to the coordinate power map; G=A with T=0 reduces to abelian multiplication; the trivial group gives U itself; U empty is allowed. Units over nonreduced B are handled by the same inverse and derivative equations. If char(k)=p and n=p, the power map on G_m has derivative zero, confirming why the invertibility hypothesis is needed. General smooth groups are not substituted for semiabelian groups: G_a in characteristic p with n prime to p is etale but that alone would not justify the finite-fibre descent used here.

B–E review: no new node or hidden lemma, no circular dependence, no source-only citation standing in place of a node, no unsupported notion, no unlogged search, and no clause merely moved to a new statement. All six steps are shorter than 2000 characters. The statement is unchanged and no assumption is strengthened. Full cited statements are copied verbatim to citations.json to make the C4 audit checkable. Nothing remains unfinished in this one-level split; its existing unsplit inputs remain the maintainer's stage-1 queue items.
