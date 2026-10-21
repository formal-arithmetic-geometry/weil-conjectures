# Stage-1 worker report: lem-zl-constant-sheaf-weight-zero

## Files written

- dag/nodes/sec-zeta-weil/lem-zl-constant-sheaf-weight-zero.json: item, statement unchanged, status split; three proof steps, no Mathlib match.
- citations.json: one entry per use in every proof step, with verbatim portions of the cited statements.
- searches.jsonl: actual msearch.py records for the item, retained as produced.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. No unit or chapter file changed.

## Attachments

None. The live project does contain AlgebraicGeometry.WeilSheaf.isPunctuallyPureOfWeight_adicConstant, WeilConjectures/DeligneLaumon/Reduction/QuasiFiniteMixed.lean:48. I read its complete proof, the variables at lines 43–44, the predicate in WeilConjectures/WeilSheaf/Stalk.lean:330, and the identity-of-local-Frobenius theorem in WeilConjectures/WeilSheaf/StalkPairing.lean:180. The tagged theorem's own proof has no sorry and needs even less scheme hypotheses. However, it is about the upstream ProEtaleWeilSheaf/WeilSheaf category and its stalk predicate. The current definition nodes def-weil-weil-sheaf-complex and def-weil-punctual-weights use the common-stage rationalized coefficient categories, fixed pairs, and the specified derived point-fibre local operator. The latter node's current stage-1 review expressly does not identify its predicates with the upstream pro-etale encoding. No comparison is supplied by this item. Therefore I have not declared an exact attachment across those coefficient encodings. The existing lean and reviewed_lean records are preserved; assessing that old Lean attachment is a maintainer issue, not a field this delivery changes.

## WANTED

None.

## Corrections and observations

The imported one-paragraph argument cited def-weil-global-geometric-frobenius as though it gave the local constant-stalk identity. Its global cohomology operator does not supply that assertion. I removed that proof dependency and used the actual local-operator identity already stated in lem-zl-constant-sheaf-lseries. Its normalized-compatible-constant-datum hypothesis is supplied explicitly by lem-zl-constant-weil-datum. Only the geometric local-operator clause is used, not the determinant, Euler product, model-operator clause or trace-formula conclusion.

The statement remains verbatim; this is not a statement dispute. I added the definitions of the canonical constant Weil structure and punctual weights to stmt_deps because the statement uses those notions. The original Weil-sheaf definition remains. The proof_origin is agent, following the agent-written current blueprint paragraph and spelling out its coefficient and eigenvector arguments. The source field and all imported and maintainer-owned metadata remain unchanged.

The item is not the key proposition of sk-input-weights. Its proof realizes the constant-sheaf clause (1), recorded as the unit's second proof step; the general relative estimate and smooth-proper purity route are untouched.

## Searches and reuse

I searched the live WeilConjectures source both by the item tag/name and by constant-sheaf/weight concepts. The source theorem above is a candidate in another encoding, not an exact attachment to the present statement's definitions. I searched the whole DAG for constant coefficients, unit sections, stalks and Frobenius and ran blueprint_refs.py search for "constant sheaf" and "weight zero", as well as ancestor for this item. No other blueprint node states this same weight-zero assertion. In particular lem-zl-constant-weil-datum and lem-zl-constant-sheaf-lseries already provide the coefficient construction and the local identity; I created no duplicate. The connected-global-section lemma lem-pod-frobenius-fixes-unit-section is not used, since it assumes a nonempty connected geometric scheme and concerns global H^0 rather than the required local operator.

All Mathlib searches were run through msearch.py and their actual results are in searches.jsonl and the item's mathlib_searches. Both semantic phrasings found ordinary constant sheaves, isocrystals or ring-theoretic Frobenius, not constructible l-adic Weil-sheaf purity. The Loogle query found four scalar-shift eigenvalue lemmas; these are not the item and no such auxiliary lemma is needed for the written eigenvector calculation. Grep for the Weil-sheaf/punctual-purity names found nothing; the second broader grep found unrelated Witt-vector notation and Selberg-sieve weights. Every service used here answered successfully. No unavailable service was recorded as a negative result.

## Tool uses

- lem-zl-constant-weil-datum: the generic coefficient construction needed to instantiate the existing constant-local-factor lemma. It works for exactly a separated finite-type k0-scheme with l different from p.
- lem-zl-constant-sheaf-lseries: only its local geometric Frobenius identity on the canonical constant Ql stalk. This is precisely the constant-section calculation prescribed by the weight unit, reused as an existing local coefficient tool. It does not replace the unit's argument by a global trace theorem. The item has no other node stating that identity. Both uses are declared in split_report.tool_uses for maintainer review.

## Review by NB

I read the current main-20261015 statement and proof of lem-zl-constant-sheaf-weight-zero, the chapter and unit records (including the unit's clause (1) proof with local polynomial 1-T), and compared the original master paragraph. The current statement has the same separated finite-type hypothesis and the same canonical constant Qlbar Weil sheaf and weight-zero conclusion. I also read the full statements and proof steps of the two reused constant-datum/local-factor lemmas, their cited trace-transport setup in main-20261015, and the current statements of the constant-Weil-structure, local-Frobenius and punctual-weight definitions. No new node needs a separate source review. The proof is kept agent-authored, since the blueprint and these expanded constant-section arguments are agent-written.

For Step 1 I checked lem-zl-constant-weil-datum says that the canonical constant E=Ql Weil sheaf admits exactly the normalized integral model assumed in lem-zl-constant-sheaf-lseries. Both assume separated finite type over the fixed finite field and l different from p, all present here. The latter statement expressly names the one-circuit F_y of def-weil-local-frobenius-trace and says it is the identity on the degree-zero constant E stalk; I quote that part, rather than taking anything only from its proof. The field-point above a closed point is included in that lemma's formulation; no new existence or connectedness hypothesis is silently used. The local operator includes point transport and a degree-length return, so this does not confuse a global Frobenius operator with a local one or assert that the geometric point is literally fixed.

For Step 2 I checked clause 5 of def-weil-constant-weil-structure fixes the coefficient stage to Ql. The current def-weil-punctual-weights specifies both H^0(C_E) tensor_E Qlbar as the actual common-stage stalk and the same local composite at Qlbar. These are the two cited statements. Their stagewise prescriptions turn the identity of Step 1 into the identity tensor 1; the displayed map a tensor b to ab identifies its carrier with Qlbar. This is a three-line scalar-extension calculation, not an unquoted comparison with the upstream category. The obsolete 2-colimit description in the constant-structure node's clause 5 is not used: its specified object at stage Ql is the literal finite-stage object of the current fixed-pair definition.

For Step 3 I checked def-weil-punctual-weights defines eigenvalues by nonzero vectors and gives exactly the absolute-value equality required. The calculation (alpha-1)v=0 forces alpha=1 over the field, the embedding preserves 1, and any positive residue cardinality to exponent 0 is 1. There is no semisimplicity assumption or algebraicity assumption on an arbitrary Frobenius spectrum. This arithmetic and eigenvector calculation is elementary and is written in full. No new lemma merely restates a clause of the item.

I tested the empty scheme (vacuous quantifier), Spec(k0), and a point of degree greater than 1 (all iterates remain identities), and disconnected schemes (the calculation is pointwise and uses no connectedness). A nontrivial scalar Weil structure on an underlying constant sheaf would fail weight zero in general; that is why the canonical structure is specified, through the existing constant-structure definition, and no arbitrary Weil structure is substituted. Each non-elementary use has a cited node whose actual statement gives it. I checked all step citations by copying verbatim statement text into citations.json and verified proof_deps is their union. Every proof step is below 2000 characters, so none hides an oversized inline argument. The statement and source have no repaired false clause, and no SGA source is used.

B–E checklist outcome: no new unsplit statement with a hidden proof, no new definition, no Mathlib leaf without a declaration, no duplicate or clause-node, no cycle back to the item through the two reused tool lemmas, and no extra hypotheses introduced. I checked that neither reused lemma's statement/proof dependency closure reaches the item before citing it. The original global-to-local inference and the coefficient-model ambiguity were the issues corrected or reported above.

## Unfinished work

None in this stage-1 split. Acceptance of the declared generic tool uses and reconciliation of the pre-existing upstream Lean attachment belong to the maintainer's independent review.
