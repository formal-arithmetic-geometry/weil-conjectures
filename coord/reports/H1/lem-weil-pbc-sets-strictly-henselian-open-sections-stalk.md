# Delivery report: lem-weil-pbc-sets-strictly-henselian-open-sections-stalk

1. **Files written**

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-sets-strictly-henselian-open-sections-stalk.json`: split statement; no new nodes.

2. **Attachments**

None. I searched slopmaster2 by the item id, key phrases, and the corresponding abelian lemma; no exact sorry-free declaration exists.

3. **WANTED**

None. The cited Stacks sources are present in the project's citation table; the proof is recorded against `etale-cohomology.tex` Tag 03QO and `algebra.tex` Tag 04GG through existing cited nodes.

4. **What was wrong or incomplete in the earlier attempt**

The maintainer identified three gaps. Step 1 had applied affine shrinking without specifying the open `W`, so it had not shown that `Spec A` lies over `U` or produced the required map `R -> A`; it now takes `W = f^{-1}(U)`, factors through `U = Spec R`, explains etaleness after restriction to the open, and records `phi^{-1}(q) = m`. Step 2 had asserted that the induced section passes through the marked geometric point; it now gives `sigma = j o Spec(tau)`, checks `f o sigma` and `sigma o tbar` by the explicit residue-field calculation, and invokes the pointed-neighbourhood definition. Step 3 had omitted the cofiltered hypothesis and used the wrong identity object notation; it now cites `lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered`, works with `(U, tbar)`, proves the only endomorphism is the identity, and identifies the colimit coprojection with the germ map. The cofiltered node is also in `proof_deps` and `split_report.tool_uses`.

## Review by H1

I read Stacks Project `etale-cohomology.tex`, Lemma Tag 03QO (“lemma-vanishing-etale-cohomology-strictly-henselian”), including its affine-neighbourhood reduction and use of Theorem Tag 04GG. The item statement matches the sheaves-of-sets assertion: `U` is an affine open identified with the spectrum of a strictly henselian local ring, the geometric point lies at its closed point, and the section-to-germ map is bijective. I checked the blueprint ancestor `lemma-weil-pbc-proper-strict-henselian-h0`; `blueprint.from.place` records the 03QO invocation and identity-neighbourhood cofinality, and no other blueprint node states this item.

Step 1 uses `lem-weil-pbc-pointed-etale-neighbourhood-affine-shrink` with `W = f^{-1}(U)`, so the affine open is over `U`; the open-immersion factorization supplies `phi : R -> A`, while the common local rings on an open justify that the factored map remains etale. The point `u` corresponds to `m`, hence `phi^{-1}(q) = m`. Step 2 uses `lem-weil-pbc-etale-algebra-residue-field-separable` for finite separability, `lem-pc-sepclosed-finite-sep-trivial` for triviality over the separably closed residue field, `lem-weil-pbc-henselian-local-root-lifting` for the simple-root lift, and `lem-weil-pbc-root-lifting-etale-retraction` for the retraction `tau : A -> R` with `tau^{-1}(m) = q`. It then checks `f o sigma` using `tau o phi = id_R`, and checks `sigma o tbar = vbar` using `alpha o sigma^# = beta o f^# o (f^#)^{-1} = beta`; these are exactly the geometric-point and residue-field conditions in the pointed-neighbourhood definition. Step 3 uses `lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered` to meet hypothesis (1) of `lem-weil-pbc-colimit-initial-full-subcategory`; step 2 gives the required map from `(U, tbar)` to every object. The identity-endomorphism argument uses that the open immersion is an isomorphism onto its image. Finally `lem-weil-pbc-colimit-constant-connected-diagram` computes the constant `(G(U), id)` colimit, whose canonical coprojection `iota_(U, tbar)` is the germ map. No step is marked elementary because each invokes cited non-elementary statements.

I checked every cited node's statement, including the cofiltered node (Tag 03PQ and its fibre-product construction), searched the whole DAG for duplicate ids/statements and 03QO/tag phrases, and searched Mathlib with LeanSearch, LeanFinder, and source grep. Mathlib has only structure-sheaf stalk results and no small-etale sheaf-of-sets analogue, so this remains an unsplit non-Mathlib statement. The edge case `U=T=Spec R` reduces directly to Tag 03QO; the open case uses the explicitly chosen `W = f^{-1}(U)` and the same argument after restriction.

5. **What could not be finished**

Nothing unresolved.

