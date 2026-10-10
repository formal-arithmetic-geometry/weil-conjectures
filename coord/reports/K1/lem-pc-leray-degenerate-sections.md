Files written:

- \`dag/nodes/sec-picard-framework/lem-pc-leray-degenerate-sections.json\` — repaired item.
- \`dag/nodes/sec-picard-framework/lem-pc-grothendieck-edge-cocycle.json\` — new unsplit statement node, Mathlib no match.

Attachments:

- None; \`CategoryTheory.Functor.grothendieckLeftEdgeMap\` is abstract and does not state the cocycle formula.

WANTED:

None.

What was wrong and what changed:

- The returned split used \`pqf-lem-leray\`, which is only for quasi-coherent modules and only asserts spectral-sequence existence. I replaced it by \`thm-sp-grothendieck\` for \`F=f_*\` and \`G=Gamma(Y,-)\`, with \`lem-weil-pbc-module-pushforward-injective-acyclic\` (Stacks 01EX, \`V=Y\`) supplying acyclicity. The identity \`Gamma(Y,f_*G)=Gamma(X,G)\` and \`pqf-def-cohomology\` identify the composite derived functor with \`H^n(X,-)\` for every O_X-module.
- The prior sentence identifying the cocycle map with the abstract edge map had no cited statement. I added \`lem-pc-grothendieck-edge-cocycle\`, whose statement gives the kernel-to-cohomology cocycle formula and, in the same setting, records the finite first-quadrant abutment filtration and collapse consequence.
- Step 3 now explicitly names the first-quadrant spectral sequence, its finite exhaustive separated decreasing abutment filtration, and the exact-couple/convergence hypotheses needed by \`lem-sp-edge-collapse\`.

## Review by K1

I reread Stacks Cohomology Lemma 01F4(2), Derived Categories Lemmas 015N and 01EX, and the imported statements of \`thm-sp-grothendieck\`, \`lem-sp-grothendieck-edge-maps\`, \`lem-sp-edge-collapse\`, \`lem-sp-derived-well-defined\`, and \`pqf-def-cohomology\`. The repaired item remains the 01F4 edge map and degeneration, but its hypotheses now range over every O_X-module, as required.

Step 1 uses the definitions of injective resolutions, direct image sections, and cohomology; its cocycle and quotient descriptions were checked term by term. Step 2 applies the generic Grothendieck theorem to \`f_*\` and \`Gamma(Y,-)\`, uses 01EX to verify acyclicity, uses \`Gamma(Y,f_*G)=Gamma(X,G)\` for the abutment identification, and cites the new cocycle node for the load-bearing edge-map formula. The cited edge-map statement supplies functoriality and \`lem-sp-derived-well-defined\` supplies resolution independence. Step 3 checks that the hypothesis is exactly \`R^pG(R^qF(F))=0\` for \`p>0\`, and that the Grothendieck sequence is first quadrant with the finite exhaustive separated decreasing filtration required by \`lem-sp-edge-collapse\`; the new node states the resulting edge isomorphism.

For the new node I searched the full DAG and blueprint by its cocycle and edge-map wording and found no duplicate. I checked slopmaster2 around \`grothendieckLeftEdgeMap\` (lines 378–391): it defines only the abstract composite, so no closed declaration attaches. LeanSearch was unavailable; LeanFinder/Loogle and source grep found no cocycle-level Mathlib result. Small cases \`n=0\` and a complex with zero differential agree with the stated kernel-to-cohomology map. I corrected the returned quasi-coherent-only route, removed \`pqf-lem-leray\`, and added the explicit acyclicity, composite-identification, cocycle, and filtration citations.
