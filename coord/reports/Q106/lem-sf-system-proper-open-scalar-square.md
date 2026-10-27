# Stage-1 worker report: Q106

## Files written

- `dag/nodes/sec-six-functors/lem-sf-system-proper-open-scalar-square.json`: existing statement node, now split in seven steps. No statement change; no new nodes and no Mathlib leaves.
- `citations.json`: every step/node pair backed by the verbatim statement, preserving its hypotheses and map directions.
- `searches.jsonl`: five actual Mathlib searches run through msearch.py, with their results retained. The inherited searches in the item are retained as historical records, not represented as new Q106 searches.
- `report.md`; sandbox-only supporting `write_split.py` and `zheng-pages34-36.txt`.

## Attachments

None. The project source has no declaration tagged with this item's id. Searches for proper/open/scalar notions found `hasProjectionFormulaOfCompactification_extendScalars` and `isIso_rightDerivedLowerStarExtendScalarsMap_app`; reading their statements shows that they concern projection-formula transport or finite-ring constructible input and do not assert this arbitrary strict-system mate equality. Neither is an attachment.

## WANTED

None. The local Zheng PDF, Stacks sources, current latest blueprint, DAG statements and Lean comparison source suffice for this agent-written proof.

## Findings and changes

The imported item had no proof. Its cited Zheng place is relevant to coefficient-system proper/open gluing but does not literally state this arbitrary-ring-system, noncartesian scalar cube. I read PDF pages 34–36: Lemma 5.13 proves a specified coefficient projection comparison; Constructions 5.14–5.15 construct open extension and glue proper/open operations. I retain that distinction in proof_origin: this proof is by an agent, not an unqualified attribution of the enlarged statement to Zheng. Stacks 0F7B and 0F7F are also context for the proper/open construction, not citations for a theorem about arbitrary varying coefficients.

The statement is preserved. In particular no cartesian square, absolute separatedness, finite ring, etale-origin, boundedness, constructibility, or normalized-system assumption is inserted. The finite-free compatible basis is used solely to make tensor extension exact on ordinary systems and hence to allow a simultaneous termwise model on all complexes. No argument tests equality of derived arrows by forgetting coefficients or by evaluating at each quotient.

The latest blueprint read is `literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-compatibility/fix-prop-coherence.proof.md`, especially the sentences on tensor reassociation, evaluation, units/counits and mates. I read the chapter and the compatibility unit records and their route. This item is a created lemma, not their key statement, so no unit realized fields are changed. `blueprint_refs.py ancestor` reports a null imported ancestor for this coefficient-construction branch; the inherited from.node, from.place and via are retained. Blueprint searches for proper open, proper/open, scalar extension and semilinear find no imported node asserting the item. In particular fix-prop-coherence is a global constructible-package assertion, not a duplicate statement about arbitrary ring systems.

Mathlib searches: leanfinder for both the finite-free derived-system statement and the mate/scalar/open cube; leansearch for scalar extension versus proper/open interchange; loogle for conjugateEquiv and Adjunction; grep for proper/open/scalar and semilinear/mate. All returned successfully. I read the hits: they provide ordinary module scalar extension, generic adjunction conjugation, associators, and general sheaf pullback adjunctions. None states the item's full system equality. The generic cube result already has the DAG node lem-weil-pbc-exchange-mate-cube, so no new categorical node is made.

## Not duplicates

No new nodes. I reuse the existing open normalization, intrinsic mate, clopen product/shift models, localization universal property, mate cube, mate definition, mate pasting and shift-uniqueness statements. Narrower finite-ring refinement and fixed adic tensor-compatibility nodes were read and not applied outside their hypotheses.

## Review by Q106

I checked delivery-errors B through E with the node statements and local sources open. There is no statement-only auxiliary node to audit or search separately. I inspected every proof step for an unquoted non-elementary result, an appeal to another node's proof rather than its statement, a clause merely renamed as a new node, and a dependency returning to the item. The non-elementary inputs are the nine existing proof dependencies. Their relevant hypotheses and directions were checked as follows.

Step 1 uses lem-coef-semilinear-derived-sections for componentwise exactness, the actual system tensor construction and K-flat computation. The compatible bases give an explicit underlying A-system identification with d copies of M, including its transition formula; this proves exactness directly. Tensoring a resolution is then a quasi-isomorphism because an exact functor preserves its acyclic cone. This elementary calculation requires neither flat transitions nor bounded complexes. It does not assert that restriction on derived morphisms is faithful.

Step 2 uses lem-coef-semilinear-derived-sections for simultaneous pullback/tensor models and lem-sf-open-tensor-normalization for the open isomorphism with its inverse's exact unit transpose. The latter explicitly covers arbitrary ring maps on the ringed diagram topos of strict inverse systems, so it applies to A_bullet -> B_bullet, not merely to constant finite coefficients. The local tensor calculation checks the ordinary geometric-open square and composition, after which the open-adjunction bijection supplies equality. The formula for transitions t(m) tensor tau(b) checks that these are compatible system maps, rather than unrelated levelwise equations. I checked Stacks sites-modules.tex 03DI and 0E8I for the underlying open adjunction and tensor direction.

Step 3 uses lem-sf-semilinear-proper-open-mate-pasting for the clopen factor s of a general pk=ir square, and lem-pur-diagram-open-clopen-shift-models for the product decomposition of the whole system categories and the literal (1,0) projector. These statements apply to arbitrary coefficient sequences and unbounded objects. In the product category tensor balancing restricts componentwise, so the equality of projections follows immediately; it is not inferred from conservativity of derived evaluation. The scheme hypotheses are exactly the item's proper verticals and quasi-compact open horizontals.

Step 4 substitutes the already checked comparisons into the three factors of alpha, with the source P_p,B T_Z J_i,A and target J_k,B T_U P_r,A written explicitly. The intrinsic-mate node states precisely that alpha word. The localization universal-property node explicitly preserves natural transformations, their compositions and equalities. The semilinear-derived-sections node says that these specified words are the derived system operations. Thus applying exact functors termwise and localizing proves an equality of B-system transformations. No non-elementary alpha-compatibility lemma is hidden: this step only substitutes the factor equations of steps 2 and 3 into the cited alpha definition.

Step 5 uses the statement of lem-weil-pbc-exchange-mate-cube, not its proof. I also read its Lean signature at lean/Sheaf/CategoryTheory/ExchangeMateCube.lean:42 to check all eight categories and the four comparison directions. The substitution is F=P_r, K=P_p, G=J_i, H=J_k, a=T_W, b=T_U, c=T_Z, d=T_V, pF=ell_r inverse, pK=ell_p inverse, pG=beta_i and pH=beta_k. In particular its mate uses pF.inv=ell_r, exactly the counit-normalized chi_r, and similarly for p. The mate-definition node gives that transpose and the intrinsic-mate node gives Gamma as alpha's proper mate. The cube conclusion is the displayed item equality, with beta_i on the right and S_p(beta_k) on the left. No comparison mate is assumed invertible.

Step 6 cites the full mate-pasting node, whose clause (2) concerns composition along adjunctions and clause (4) identities. This is the needed assertion, not merely full faithfulness or a definition of adjunction. The intrinsic-mate node explicitly fixes direct-image compositors as mates of inverse-image compositors. Their tensor comparison composition has already been checked on actual ordinary models. Taking its mate gives chi_wv=S_w(chi_v) chi_w S_v with canonical compositors, which justifies an outer proper whiskering. I read categories.tex Tag 0B65 as the categorical source context.

Step 7 cites the whole-system open/clopen shift-model node: its S_v shift is explicitly the K-injective comparison or equivalently the mate of P_v's termwise shift. The shift-uniqueness node supplies both the unit and counit equations for that mate shift. With the mate-definition node, substituting those equations into the unit-square-counit word proves shift compatibility of chi and Gamma. The only scalar shift computation is the written equality of degree-a and degree-(a+h) tensor maps and the common (-1)^h differential, so no additional shift theorem is hidden. I checked derived.tex Tag 0A8D for the counit-normalized right-adjoint shift context.

I tested d=1 with the identity coefficient map (all scalar comparisons become identities), a genuinely nontrivial finite-free algebra (no Frobenius/coextension or injective-preservation assertion is used), identity open immersions, an empty source open, and an empty complementary clopen component. The projector calculation gives respectively identity or zero as required. With nonflat coefficient transitions, tensor sends both comparison paths to t(m) tensor tau(b); compatibility of bases makes the exactness calculation an actual system calculation. Unbounded input causes no problem because tensor is exact and the proper mates are taken in the supplied unbounded adjunctions. No step exceeds 2000 characters; the longest is the routine open-comparison calculation, 1189 characters. The proof does not hide a separately usable comparison theorem inside a long step.

The off-unit citations are generic system, localization, categorical mate and shift tools. Their purposes are declared in split_report.tool_uses; they do not replace the compatibility unit's proof route. All citations have their full verbatim statements in citations.json, so the complete hypotheses remain available for checking. The item's statement and inherited metadata are retained, and proof_deps is precisely the union of uses.

## Unfinished work

None in the mathematical split. The required server dry run exited 0 and printed OK (not pushed) at 55787bf3d80, with preflight passed. The direct-delivery brief authorizes the ensuing push; no second worker is required.
