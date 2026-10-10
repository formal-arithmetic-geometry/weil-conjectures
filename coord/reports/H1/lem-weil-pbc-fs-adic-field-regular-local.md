# lem-weil-pbc-fs-adic-field-regular-local

## Worker delivery

- Item: `dag/nodes/sec-proper-base-change/lem-weil-pbc-fs-adic-field-regular-local.json`, split in six steps; no new nodes.
- Lean attachments: none. The item has `lean_audit.slopmaster2.state = none`.
- WANTED: none. I read the local Stacks source at `/home/ubuntu/weil-conjectures-sheaf-F2/literature/stacks-project/more-algebra.tex`, lines 9535-9589, and checked tags 07EI, 07EC, 07ED, 07EF, 0320, 032A, 00OF and 00MC against its `tags/tags` index.
- The imported item had no proof. Its statement matches More on Algebra Lemma 07EI. The source abbreviates the successive approximation proving surjectivity of the map to the power series ring; Step 5 writes that approximation out. The source warns that the lifted maps need not be residue-field linear; Step 4 keeps only prime-field linearity.
- All source ingredients already had nodes: characteristic-zero field formal smoothness, characteristic-positive field nilpotent lifting, adic completion and its regularity criterion, Cohen coefficient field, power-series regularity and completeness, Nakayama, and the dimension bound. The composition of formal smoothness is proved directly in Step 1 from the lifting definitions, since Stacks 07EF omits its proof.
- Blueprint: `tools/blueprint_refs.py ancestor` gives `thm-weil-pbc-finite-etale-lifting`; searches for `formally smooth field regular local`, `regular local ring`, and `formally smooth for the` found no blueprint node with this statement, so `blueprint.same_as = []`. The item serves the regularity fact under step 7 of the ancestor's essential-surjectivity route.
- Mathlib: the item's existing LeanSearch, LeanFinder, and grep records report no adic formal smoothness to regular local theorem. No new Mathlib leaf is asserted.
- Small cases checked: for $n=0$, $T=K$ and the residue map already gives surjectivity; in positive characteristic a characteristic-$p$ target ring is required for the field lifting lemma and follows because it is an $\mathbf F_p$-algebra. The coefficient field exists only after completion, as used in Step 3.

## Review by H1

I read More on Algebra 07EI in `more-algebra.tex` from its prime-field reduction through its final dimension comparison, including the warning that the lifts need not be $K$-linear. The unchanged item statement has the same Noetherian local and adic formal-smoothness hypotheses. I checked the cited node statements: the characteristic-$p$ lifting node explicitly requires the target to have characteristic $p$, which holds because step 1 begins with a $k_0=\mathbf F_p$-algebra; the completion, Cohen coefficient-ring, power-series and Nakayama nodes give the facts used in steps 2, 3, 5 and 6. Step 4 states the square-zero kernels and continuity, and step 5 supplies the successive approximation that 07EI abbreviates. For embedding dimension zero the construction reduces to the residue field, and in positive characteristic the coefficient ring becomes a field only after passing to the complete equal-characteristic ring. No new nodes were made; I checked the whole-blueprint searches and found no equivalent statement. I sent nothing back to the worker.

