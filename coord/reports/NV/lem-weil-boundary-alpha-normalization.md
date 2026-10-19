# Worker report

## Files written

- `dag/nodes/sec-six-functors/lem-weil-boundary-alpha-normalization.json`: statement, split in six steps; no Mathlib match for the full normalized derived-costalk comparison.
- `citations.json`: four verbatim statement quotations, one for every step/node citation.
- `searches.jsonl`: actual wrapper search log, retained in the sandbox.

No new nodes and no Mathlib leaves. No unit or chapter record changed: this created helper is not the unit's key node.

## Attachments

None. Searched the read-only slopmaster2 `WeilConjectures/` tree for the exact blueprint tag, costalk, evaluation-normalized, and the normalization notation; also inspected `SixFunctors/Etale/Derived/Dualizing.lean`. The latter's general Verdier theorems have sorry and do not state this normalized costalk comparison. No project declaration gives all clauses of the item without sorry. The upstream master tree was searched as reference only.

## WANTED

None. The needed blueprint passages and ringed-site source are present.

## Audit of the imported item

The imported item had no proof. Its parent explicitly separates the existence-only costalk isomorphism from the evaluation-normalized map; I preserved this separation. `lem-weil-closed-costalk-duality` states a natural isomorphism, but its statement supplies no formula for its transpose, so I did not use its proof's final normalization sentence as a theorem. `def-weil-boundary-duality-input` also mentions the normalization but is a definition, so it cannot prove this item.

The statement is unchanged. Its pro-etale comparison notation is unused in its actual assertion, which is explicitly etale. The proof does not silently assert an ambient pro-etale exceptional adjoint. The notation q(M,N) is used on its indicated projection-formula domain: the only instance needed is M=K, N=D_T K, where G D_T K is bounded constructible by hypothesis. No assertion for arbitrary inputs with no available projection inverse is used.

The left-first projection formula in the question differs in tensor order from the named right-first ordinary projection map. Step 2 fixes that convention explicitly and step 4 writes both symmetry cancellations. There is no new geometric hypothesis, no boundary-exchange assumption, no biduality assumption, and no coefficient transport added.

## Searches and reuse

Whole-DAG searches included the exact item id, q notation, evaluation-normalized/evaluation-defined, costalk, transpose, projection formula, Tags 08J9 and 08JA. `tools/blueprint_refs.py ancestor` returned `cor-weil-boundary-duality-discharge`; searches for costalk found `lem-weil-closed-costalk-duality` and `def-weil-boundary-duality-input`. Searches for evaluation-normalized transpose, alpha normalization, and tensor Hom found no blueprint node that states the additional specified-map assertion. The item's same_as therefore remains empty. No candidate new node was created.

Read all seven wrapper results in searches.jsonl. The first Loogle query was rejected for an unknown identifier, and the first grep had a redundant Mathlib/ prefix and was not used as evidence of absence. A second semantic phrasing and valid Loogle/grep searches were run. LeanSearch was available and returned evaluation/adjunction infrastructure. The promising exponential/Frobenius comparisons were checked at Mathlib/CategoryTheory/Monoidal/Closed/Functor.lean lines 43-44, 61-64, 84-95, and 137 onwards: they assume CartesianMonoidalCategory and concern Cartesian exponential comparison, not derived module tensor or this mixed ordinary/exceptional closed-immersion comparison. Generic adjunction bijections and rigid tensor equivalences are partial infrastructure, not a one-line specialization giving every clause here. All actual queries and results are recorded verbatim; inherited search entries are retained.

## Unfinished work

None in this one-level split. Existing cited nodes keep their current proof/audit states. This is a stage-1 argument, not a claim that Lean proofs were completed. No Lean files were written or compiled.

## Review by NV

I read the chapter `sec-six-functors`, the unit `sk-prop-sf-biduality-general`, the master source `cor-weil-boundary-duality-discharge.md` and its current main-20261015 second proof paragraph, the current costalk-duality proof, and the boundary-duality definition. The source's words “adjointing back through tensor–Hom and i_* left adjoint to Ri^!” require the exact calculation supplied here, rather than merely an isomorphism of its endpoints. This helper remains on the unit's formal duality route and does not use the forbidden SGA route.

For step 1 I opened both cited node statements and Stacks `sites-cohomology.tex`, labels lemma-internal-hom (Tag 08J9) and lemma-section-RHom-over-U (08JA), lines 8874-8932. The first statement supplies currying on any small ringed site without bounds; the second identifies zeroth global derived internal Hom with morphisms on that same site. Hence they apply to the constant A ring sheaves on the small etale sites. Taking global sections gives precisely the stated Hom bijection. Uncurrying a map is evaluation after tensoring it with the identity, by the image of the identity under a natural adjunction bijection. I did not cite the superficially similar O_X-module adjunction as an etale A-module theorem.

For step 2 I opened `def-kun-projection-formula-map` and its blueprint source. Its statement actually defines the canonical right-first map through ordinary pullback/direct-image unit and counit. It is used for that definition and its formal naturality, not to claim invertibility. Invertibility is the item's explicit hypothesis. The proof defines the left-first version by the two symmetries, then inverts that formula and cancels the source symmetry. The required instances have M=K and B arbitrary in D^b_ctf, or B=G D_T K; all are within the hypothesis. Naturality and inverse naturality follow by composing natural transformations and multiplying the naturality equation by inverses.

Step 3 uses the already specified ambient F left adjoint to G, the tensor-Hom bijection from step 1, and the projection inverse from step 2. The formula h_b has source FB tensor K and target omega_T. Precomposing with pi inverse gives a map F(B tensor LK) to omega_T; its exceptional adjunct has target G omega_T=omega_Z. This typing check is why no preservation of B tensor LK by a functor on a restricted constructible category is being assumed: the exceptional adjunction is ambient. Each arrow is a bijection and natural in B.

Step 4 has no extra theorem hidden behind “corresponds.” I applied the actual adjunction equation to q and wrote the full transpose of r_K. In the expression P inverse followed by F of symmetry, the order identity of step 2 gives symmetry followed by pi inverse. Naturality of symmetry moves the counit across, leaving e composed with (mu tensor identity) composed with pi inverse. This is h_identity composed with pi inverse, exactly the result of step 3 at the identity. Both transpositions are bijective, so equality of the transposes proves equality with the particular alpha. This is a two-line mate substitution, not a separate smaller lemma needing a new node.

Step 5 is the elementary representable inverse argument, written without citing a Yoneda theorem with mismatched hypotheses. The source X=G D_T K belongs to D^b_ctf by hypothesis. The target Y=D_Z i^*K also belongs to that full subcategory because i^*K does and D_Z preserves it. Thus both X and Y are legitimate test objects; taking gamma=theta_Y inverse(identity_Y) makes alpha gamma the identity. Naturality under alpha, and injectivity of theta_X, make gamma alpha the identity. Testing only D^b_ctf objects is sufficient for exactly this reason.

For step 6 I opened `lem-weil-duality-pairing`: its statement says evaluation is a natural pairing for every complex, without a constructibility assumption on its dual. I use only that natural pairing, which gives e_K(Du tensor identity)=e_K'(identity tensor u). Substitution into the explicitly defined h_b and naturality of projection and adjunction yield the displayed naturality equation. The arrows point contravariantly in K; testing at B=G D_T K' verifies the exact source and target of both composites. No shifts, distinguished triangles, or unrecorded biduality identities are taken from that node.

I checked B=0 and K=0, the empty closed subscheme, and the identity immersion. In the zero and empty cases all formulas become the unique maps of zero objects. For i=identity, the formula reduces to ordinary tensor-Hom evaluation and its identity transpose. To check the signs, for homogeneous factors of degrees a,b the two interchanges contribute (-1)^(ab) twice, hence 1; the proof uses naturality of the signed symmetry and does not erase a single interchange. None of the six steps exceeds 2000 characters, and no general comparison lemma has been hidden in a long step.

Against delivery-errors B–E: there are no new statement-only nodes, no copied clauses, no hollow definitions, and no duplicate nodes. Every cited statement was opened, its used portion copied verbatim into citations.json, and its hypotheses checked as above. The two off-unit nodes in step 1 are declared in split_report.tool_uses as generic ringed-site Hom tools; they do not replace any geometric step of the unit. The remaining work is formal substitution from hypotheses and prior steps, with every argument displayed. No statement dispute or source error was found. The correction made during self-review was to keep the left- and right-first projection maps separate and to check that theta_Y(gamma), rather than a map in the wrong Hom set, is used in the inverse calculation.
