1. Files written:

- `item.json`: `lem-weil-pbc-ringed-site-injective-module-cech-acyclic`, statement, split proof, and blueprint metadata.
- `lem-weil-pbc-ringed-site-injective-module-injective-presheaf.json`: statement-only child; Mathlib search found ingredients but no combined theorem.
- `lem-weil-pbc-ringed-site-free-cech-complex-exact.json`: statement-only child; Mathlib search found no site-level theorem.
- `citations.json`: verbatim citations for every step dependency.

2. Attachments: none.

3. `WANTED:` none.

4. No statement correction was needed. The imported item had no proof and its Cech-complex dependency was already present. I added the two missing general ringed-site statements rather than citing the specialized small-etale versions.

5. Nothing remains unfinished.

## Review by M1

I read the item against Stacks Project `sites-cohomology.tex`, Lemma 03FC (injective module trivial Cech), with the second-paragraph transfer in Lemma 03FD. I also read the proof sources for Tags 03FB (module injectivity passes to presheaves), 03F5 and 03AT (the free Cech complex and its contracting homotopy), and 03AS (Yoneda identifies Hom from the free representable complex with the Cech complex). The item hypotheses are unchanged: an arbitrary ringed site, an injective sheaf of O-modules, and an arbitrary covering.

Step 1 cites the ringed-site, sheaf-module, presheaf-module/sheafification, and injectivity definitions, plus the new general 03FB child; that child states exactly the presheaf injectivity used. Step 2 cites the new general free-Cech exactness child and the existing power-set contracting-complex node; their statements provide respectively positive-degree exactness and the chosen-lift contraction, including the empty-lift case. Step 3 cites the Cech-complex and presheaf-module definitions for the Hom/Yoneda identification. Step 4 cites the two child statements and the Cech definition; exactness of Hom into an injective is the 03FC argument. Step 5 cites the Cech and sheaf-module statements for the fact that forgetting the module structure leaves the same sections and restrictions.

I searched the whole DAG and blueprint before creating the children. The only close existing result, `lem-weil-pbc-injective-module-abelian-acyclic`, is specialized to the etale site and includes the same route, while `lem-weil-pbc-site-injective-cech-acyclic` assumes abelian injectivity, which is not available for an underlying module-injective sheaf. The existing `lem-weil-pbc-power-set-complex-contractible` exactly supplies the set-level contraction and is declared as a tool use. Small checks include the zero module, a one-object site with only identity covering, and an empty lift set; all give zero positive Cech cohomology as required. Mathlib searches were recorded for both new statements and the item; no single Mathlib declaration states either general ringed-site result.
