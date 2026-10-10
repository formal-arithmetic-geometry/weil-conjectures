# lemma-weil-pbc-proper-strict-henselian-h0

## Files written

- `dag/nodes/sec-proper-base-change/lemma-weil-pbc-proper-strict-henselian-h0.json`: five-step split of the set-valued degree-zero comparison, with the geometric-fibre and naturality clauses.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-gabber-h0-etale-criterion.json`: new unsplit statement, Stacks Tag 09ZF (`lemma-gabber-h0`), the finite-cover criterion upgrading Zariski to etale sections. LeanSearch, Loogle and an available Mathlib source mirror found no match.

## Attachments

No exact attachment. `AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_geometricFibre` in `WeilConjectures/SixFunctors/Etale/BaseChangeTheorems/DegreeZero.lean:118-149` has the blueprint tag for this node, but its statement covers only sheaves of `Λ`-modules. This node and Stacks Tag 0A0C cover all etale sheaves of sets. The theorem body contains no `sorry`, but the committed sorry map shows its dependency `AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_of_henselianRing` at lines 85-92 contains `sorry`, so the module-valued specialization has sorry reachable. The latter declaration corresponds to the narrower abelian node `lemma-weil-pbc-etale-degree-zero`; neither closes the set-valued item.

## WANTED

None. The Stacks source was read at `/home/ubuntu/weil-conjectures-sheaf-F2/literature/stacks-project/etale-cohomology.tex`: Tag 09ZG (`lemma-h0-topological`), Tag 09ZF (`lemma-gabber-h0`), Tag 0A0B (`lemma-zariski-h0-proper-over-henselian-pair`) and Tag 0A0C (`lemma-h0-proper-over-henselian-pair`). Their labels were confirmed in `tags/tags`.

## Corrections and proof route

The imported Step 2 cited `lemma-weil-pbc-etale-degree-zero`, whose statement is abelian-only, for a claim about arbitrary etale sheaves. Imported Step 3 recounted the proof of that dependency and asserted a constructible-sheaf gap; it did not supply a separate argument for this item. Stacks 0A0C instead invokes 09ZF after the set-valued Zariski comparison 0A0B. The new criterion is strictly more general than this item, with a qcqs scheme and a closed immersion but no henselian hypothesis; it is not a restatement of the proper strict-henselian comparison.

Step 1 verifies the henselian pair, qcqs source and properness of each finite cover. Step 2 applies the already split 0A0B node to the source and every finite cover. Step 3 checks exactly the two hypotheses of 09ZF and obtains the set-valued closed-fibre comparison. Step 4 uses the existing algebraic-extension and purely inseparable base-change nodes, then universal-homeomorphism invariance, to pass to the algebraic-closure geometric fibre. Step 5 expands naturality using the finite-pullback identities. The cross-unit 0A0B and universal-homeomorphism facts are generic tool lemmas, recorded in `tool_uses`; the chapter and unit route was not changed.

The new node was searched by tag and concept over `dag/nodes/` and through `tools/blueprint_refs.py search` across the blueprint. The related `lemma-weil-pbc-etale-degree-zero` is abelian-valued and does not state the generic 09ZF criterion. Edge checks: for `Z=\varnothing`, both sides have their unique section; for `A=k` separably closed, the closed-fibre comparison is the identity, and the remaining algebraic-closure map is a purely inseparable universal homeomorphism. No new hypothesis is needed for these cases.

## Checks

- `python3 tools/review_split.py lemma-weil-pbc-proper-strict-henselian-h0`: PASS.
- `python3 tools/blueprint_refs.py check lemma-weil-pbc-proper-strict-henselian-h0 lem-weil-pbc-gabber-h0-etale-criterion`: 0 errors.
- `python3 tools/check_dag.py`: 0 cycles; seven unreachable nodes unrelated to this item remain from the base.
- `git diff --check`: clean.

## Unfinished

The new 09ZF criterion is an unsplit queue item. No Lean was written or built.

## Review by E1

I read Stacks Etale Cohomology 09ZF (lemma-gabber-h0), 0A0B (lemma-zariski-h0-proper-over-henselian-pair), and 0A0C (lemma-h0-proper-over-henselian-pair). The new 09ZF node has the source's qcqs scheme, closed immersion, Zariski-section bijection on X and on every finite X', and set-valued etale-section conclusion, without an extra henselian assumption. It is a statement-only unsplit node; DAG, whole-blueprint, Lean and available Mathlib searches found no exact existing declaration. The item's closed-fibre assertion is exactly 0A0C at I=m. Its geometric-fibre clause uses the canonical algebraic closure of the separably closed residue field; the worker explicitly narrowed the imported wording to avoid arbitrary geometric points, for which the claim can fail for general sheaves.

In Step 1, the cited henselian terminology yields the henselian pair and separably closed residue field, qcqs-over-affine yields qcqs Z, and finite-morphism permanence gives proper Z' over S. In Step 2, the 0A0B node supplies the Zariski bijection both for Z and each Z'; these are precisely both 09ZF hypotheses. Step 3 applies the new 09ZF statement to set-valued sheaves, without using the narrower module-sheaf Lean theorem. In Step 4, the cited separable/purely-inseparable decomposition shows k^alg/k is purely inseparable; the pure-inseparable homeomorphism node applied after every base change establishes the universal-homeomorphism definition. The cited base-change and etale-topos-invariance nodes then give the bijection on sections. Step 5 is functoriality of canonical inverse image and the cited finite-pullback identity. The empty closed fibre case gives singleton sections on both sides, and k algebraically closed makes Step 4 the identity. I checked the cross-unit nodes' statements, not their internal proofs; their use is identified as a tool in the worker report. No A-E issue required return to the worker.
