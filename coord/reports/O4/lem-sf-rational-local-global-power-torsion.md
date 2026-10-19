# Stage-1 report: lem-sf-rational-local-global-power-torsion

Files written:

- `dag/nodes/sec-six-functors/lem-sf-rational-local-global-power-torsion.json` — item retained and split; no new nodes and no Mathlib leaves.
- `citations.json` — verbatim statement quotations for every cited node in steps 2 and 3.

Attachments: none.

WANTED: none.

The imported item was not already stated by a sorry-free declaration in either reference Lean source. I found no duplicate DAG or blueprint node: the closest existing result, `lem-sf-finite-cover-ctf-locality`, concerns finite-coefficient constructibility and Tor amplitude, whereas this item concerns arbitrary completed-coefficient derived objects and scalar-localized zero morphisms.

No statement, blueprint, or brief error was found. No Lean files were written and no compiler, Lake, or build tool was run.

## Review by N4

I read the item, its unit `sk-prop-sf-dualizable-biduality`, chapter `sec-six-functors`, and the ancestor proof in `prop-sf-dualizable-hom.json`; the latter explicitly invokes this lemma after obtaining a finite pro-etale cover on which the cone is rationally zero. I also read the cited statements `lem-pur-site-restriction-module-adjunction-exact`, `lem-sf-derived-homology-long-exact`, and `lem-sfb-sheaf-cover-local-isomorphism` in full. The first states that restriction to a localized ringed site is exact; the second supplies the cohomology functor on derived morphisms; the third applies to an arbitrary category-valued sheaf and says that a morphism whose restrictions along a covering family are isomorphisms is an isomorphism globally. Their hypotheses match the item: each `D_j` is a module-sheaf derived category, and the `U_j\to X` are a covering family in the pro-etale site.

Step 1 handles the finite maximum explicitly and uses only the stated \mathcal O_E-linearity of each `D_j`; it also checks the `t=0` convention. Step 2 uses exactness of restriction to identify \mathcal H^d(C|_{U_j}) with the restriction of \mathcal H^d(C), then applies the cohomology functor to the local zero scalar endomorphism. Step 3 applies the cover-local isomorphism criterion to `0\to\varpi_E^N\mathcal H^d(C)`, whose restrictions are `0\to0`, and concludes the global sheaf is zero for every `d`. I checked the edge cases `t=0`, `N_j=0`, `C=0`, and a one-member cover. The three literal node statements used in these steps are recorded in `citations.json`.
