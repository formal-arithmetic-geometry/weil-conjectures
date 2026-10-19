1. Files written:

- `dag/nodes/sec-smooth-purity/lem-exc-etale-origin-proper-open-interchange.json`: unchanged statement, repaired proof with nine steps; Mathlib verdict remains no match for the fixed-coefficient site-transport theorem.
- `citations.json`: 43 verbatim citations, covering every node used by every proof step.
- `searches.jsonl`: retained required Mathlib searches for the item.

2. Attachments: none.

3. WANTED: none.

4. Repair of the returned delivery:

- The statement is unchanged and still has no new nodes. The previous `thm-weil-pbc-site-comparison` entry was removed from `stmt_deps` because witness full faithfulness is a proof dependency, not a notion needed to state the item.
- The former first step now cites proper base change, open-immersion base change, the definition of properness and finite type, and exactness of both extension-by-zero functors. It explicitly checks that the base-changed maps r and k have the hypotheses required by the comparison maps.
- The former normalization step was split into five steps. `lem-weil-pbc-comparison-pullback` supplies the Cartesian pullback comparison, `lem-weil-pbc-comparison-direct-image-canonical-mate` supplies the counit-normalized b_u, and `lem-weil-pbc-transport-identifies-exchange` supplies the conjugation identity carrying the etale exchange to the pro-etale ambient exchange.
- `def-kun-unbounded-exchange` is cited for the unit--square--counit formula of the unbounded exchange, and `lem-amb-unbounded-proper-open-interchange` is cited for the precise Gamma^e normalization by the inverse of lambda.
- `lem-sf-open-comparison-unit-normalization` is now cited for the exact equation showing that each e_i,e_k preserves the open-adjunction unit; this repairs the prior C4 gap about units and counits. Exactness and the naturality/composition clause of `lem-cbc-proetale-extension-zero-comparison` justify the termwise passage.
- The final transpose step spells out the order of the mate pasting and identifies its result with lambda_M^{-1} before invoking uniqueness of the open-adjunction transpose. All off-unit statements used as generic tools are declared in `split_report.tool_uses`.

## Not duplicates

- `lem-exc-etale-origin-proper-open-interchange` vs `lem-exc-proetale-finite-cd-proper-open-interchange`: the existing node assumes a uniform finite cohomological-dimension bound and constructs a pro-etale comparison for arbitrary pro-etale inputs; this item transports the etale canonical interchange for bounded-below etale-origin inputs without that bound.
- `lem-exc-etale-origin-proper-open-interchange` vs `lem-trf-proper-open-site-transport`: the existing node concerns finite morphisms and a different finite-site exchange; this item concerns a proper morphism, arbitrary open immersion, the unbounded etale interchange, and witness transport.

5. What I could not finish: nothing. No Lean files were written and no compiler or build tool was run, as required for stage 1.

## Review by Q114

I reread the item, its chapter and unit records, the retained Step 7 proof in `prop-exc-base-change-proper.proof.md`, and the full statements of every cited node. The item statement still matches the retained source clause by clause: finite commutative coefficients, Noetherian corners, proper p, arbitrary open i, the displayed five-arrow composite, bounded-below etale-origin witnesses, witness independence, naturality, and both lambda normalization equations.

Step 1 uses the proper and open base-change statements and the definitions of properness, finite type, and closed immersion to verify that r and p are qcqs and that k is open. It uses the two extension exactness statements only for the termwise complex passage. Step 2 uses the canonical-mate comparison, the extension comparison, and the unbounded etale interchange; each cited statement explicitly supplies the isomorphism or naturality used. Step 3 uses the witness definition and the full-faithfulness theorem exactly for the unique map between two witnesses, then uses naturality of the five arrows and cancellation.

Steps 4 and 5 address the returned C4/E5 fault directly. Step 4 identifies (f,f',g,g')=(p,r,i,k) and reads the exact a_u and b_u normalizations from their statements; the transport node then gives the stated conjugation to Ex^R. The unbounded exchange definition in Step 5 has the same unit--square--counit mate formula as the bounded-below etale exchange used by Gamma^e. Step 6 applies the open-comparison unit equation to both open edges, so the cited statement now says precisely what the step takes from e_i and e_k. Step 7 performs the transpose calculation using those unit equations, the b_u counit equations, the Cartesian pullback comparison, the transport identity, and the Gamma^e normalization; it ends with the explicit equality of the transpose and lambda_M^{-1} rather than an unsupported “pasting shows” assertion. Step 8 is the ordinary uniqueness and triangle-identity argument for the open adjunction. Step 9 checks the bounded-below etale-origin scope against the operation definitions and the full ordinary pro-etale adjunction.

I checked the edge cases used in the prior review: W=T gives the identity comparison, W empty gives the zero extension, and p=id reduces to the comparison conjugation. The two existing nearby nodes remain non-duplicates for the reasons recorded above. Every citation quote is a verbatim substring of its node statement, and `proof_deps` is the union of the nine `uses` lists.

## Repair of the landing refusal (2026-10-17)

The return at c693fca2c3 said that the independent reader approved the split but the landing rejected an attempted fix named repair.py, since fixes may only be node/unit files. I retained the reviewed sandbox proof, citations and search log. The first dry run against the current DAG passed, and the delivery tool confirmed that the retained content exactly matched the returned head c693fca2c3; it declined an unchanged re-push. I then revised the node itself, rather than delivering a repair script or changing project tools.

I reread the current statements of every statement/proof dependency. In particular, the current lem-exc-proetale-derived-open-restriction specifies lambda by rho on K-injective representatives, with no properness, boundedness or etale-origin restriction. Step 7 now cites that statement and identifies rho with the ambient exchange by comparing their adjunction transposes: both are the pullback of the p-counit after the Cartesian inverse-image identification. The cited statement supplies the termwise equality and preservation of K-injectives by open restriction; the existing ambient-exchange definition supplies the exact transpose formula. This avoids treating the old description of lambda by exchange as an unstated equality. Step 8 now explicitly extends the model normalization along the witness using naturality of lambda and the open-adjunction counit. The item statement and its hypotheses remain unchanged.

The current comparison/site statements retain finite discrete constant coefficients and bounded-below input; the canonical direct-image comparison and the exchange-transport statement require qcqs p and r, checked in Step 1. The etale proper/open interchange still supplies precisely its Cartesian lambda normalization, now quoted in citations.json rather than merely its isomorphism clause. The canonical b-map citations likewise quote the actual counit equation in Steps 4 and 7. The current site and module conventions do not require a different coefficient category. No cited node is merged. All step citations were checked verbatim against current statements.

I corrected proof_origin.by to agent: the referenced blueprint file currently has four steps, while this item was extracted from the retained repaired parent proof (the current prop-exc-base-change-proper Step 8 realizes that retained Step 7). Stacks 099R and 0F7B support the comparison and etale inputs, respectively; they are not claimed to state this pro-etale transport theorem. The nine proof steps all remain below 2000 characters, with no new nodes or Mathlib leaves. The identity-open, empty-open and identity-proper tests still reduce to the same identities. The delivery contains the node and this ordinary report; no repair.py is supplied as a fix.
