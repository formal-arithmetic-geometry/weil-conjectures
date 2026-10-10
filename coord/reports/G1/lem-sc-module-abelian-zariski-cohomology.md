# Delivery report

1. Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-module-abelian-zariski-cohomology.json` — statement, split proof, no Mathlib match.
- `dag/nodes/sec-curve-estimates/lem-sc-injective-module-abelian-acyclic-zariski.json` — statement-only unsplit child, no Mathlib match.
- `dag/nodes/sec-curve-estimates/lem-sc-zariski-module-sheaves-enough-injectives.json` — statement-only unsplit child, no Mathlib match.

2. Attachments: none. A grep of `WeilConjectures/` found no declaration tagged `lem-sc-module-abelian-zariski-cohomology`; the nearby cohomology declarations either have `sorry` or define only underlying abelian cohomology.

3. WANTED: `literature/stacks-project/sites-cohomology.tex`, Lemma 03FD and its cited Lemmas 03FC and 03F9, for the proof of `lem-sc-module-abelian-zariski-cohomology` and `lem-sc-injective-module-abelian-acyclic-zariski`. WANTED: `literature/stacks-project/sites-modules.tex`, Lemma 03DA and Injectives Theorem 079H, for `lem-sc-zariski-module-sheaves-enough-injectives`. The local literature checkout contains only citation indexes; the statements were checked against the online Stacks pages.

4. What was wrong in the imported node or brief: the imported item had no proof steps and left the module-to-abelian comparison as a black box. The existing etale injective-acyclic node cannot be cited for the Zariski site, so the missing ringed-site acyclicity fact and the Zariski enough-injectives fact were made explicit as new unsplit nodes. No statement was weakened. The source's proof uses the exact forgetful functor, an injective module resolution, and the acyclic Cech/derived-functor criterion; each now appears as a cited step or child statement.

5. What I could not finish: the two child nodes remain unsplit by design for stage 1. Their statements were checked on the empty site, a one-point site, and the affine Zariski site; no Mathlib declaration states either theorem.

## Review by G1

I read the item source as Stacks Lemma 03FD (the online page labels it “Cohomology of modules—cohomology computed in abelian sheaves agrees with cohomology computed in modules”). Its hypotheses allow an arbitrary ringed site and module sheaf, so the item is a direct specialization to $(X_{\\mathrm{Zar}},\\mathcal O_X)$; no quasi-coherence or Noetherian assumption was inserted. I also checked the parent unit and the existing `lem-sc-ga-cohomology` proof, which is the only blueprint ancestor named by `blueprint_refs.py`.

Step 1 uses the exact-forgetful statement of `lem-weil-pbc-module-sheaves-colimits-forgetful`; that node explicitly says kernels and cokernels are preserved, which is exactly the exactness needed here. Step 2 uses the new Zariski enough-injectives child and Step 1 to turn a module injective resolution into an exact underlying abelian resolution. Step 3 uses the new Zariski injective-module acyclicity child and the existing acyclic-resolution criterion `lemma-weil-pbc-leray-acyclicity`; these statements say that the common global-sections complex computes the two right-derived functors. Naturality follows from the same resolution comparison and is stated explicitly.

For each new child I searched the DAG and blueprint for duplicate statements (including the existing etale injective-acyclic node), then ran LeanSearch, LeanFinder, and Mathlib-source grep searches. The searches found only generic sheaf cohomology or Grothendieck-category results, not these ringed-site comparisons. Small cases checked were the empty site, the one-point site (where higher cohomology is zero), and an affine Zariski site. All hypotheses in the source specialization are therefore present, and the two missing non-elementary facts are isolated as statement-only nodes rather than hidden in the proof.
