# Worker report

Files written:

- item `lem-trf-flat-finite-type-dense-presentation` (statement, split; repaired proof and dependencies)
- new node `lem-trf-flat-finite-type-flat-point-local` (statement, unsplit; Mathlib no-match)
- `citations.json` (verbatim node statements for every cited step)

Attachments: none.

WANTED: none.

The item statement agrees with Stacks Tag 081N, including local finite presentation of the morphism, finite type and base-flatness of the quasi-coherent module, retrocompact scheme-theoretic density of the open, and finite presentation after restriction. I read Tag 081N's complete affine proof and Tags 05I7 and 05I8 at the finite-type-flat-at-point-local passage, together with Tag 00RC in `algebra.tex`.

## Repair of returned delivery

The returned E2 point was correct: the former node incorrectly asserted that a single localization is both finitely presented and flat from flatness at a prime. I replaced it with the true Tag 05I7 stalk assertion that $N_{\\mathfrak q}$ is finitely presented over $B_{\\mathfrak q}$ when it is $A$-flat. This removes the counterexample and prevents the helper from proving the item by itself. The returned E3/E5 and C4 points are repaired by citing this stalk node in Step 2, and by citing the existing `lem-weil-pbc-openness-of-flatness` node (Tag 00RC) in Step 3 for the open flat locus of the finitely presented approximant $N'$. Step 4 now uses only the flatness obtained in Step 3, the density injection and the localization diagram; it no longer cites the false helper for a neighborhood conclusion.

## Review by Q57

I checked the item against Tag 081N line by line. Step 1 uses the local nature of finite presentation, finite type, and the affine finite module presentation; retrocompactness gives a finite principal cover of $U$ and scheme-theoretic density gives the product-localization injection. Step 2 uses exactly the repaired Tag 05I7 stalk statement: after choosing a finite free presentation, finite presentation of $N_{\\mathfrak q}$ permits finitely many kernel relations to enforce agreement at $\\mathfrak q$, while the finite cover localizations are enforced by powers of the inverted elements. Thus the resulting $N'$ agrees with $N$ at all required localizations and remains flat at $\\mathfrak q$. Step 3 verifies that the finite-relation quotient $N'$ is finitely presented over $B$, then applies the existing Tag 00RC node, whose statement says the flat locus of a finitely presented module over a finitely presented ring map is open; this supplies $g\\notin\\mathfrak q$ with $N'_g$ flat. Step 4 reads the exact comparison diagram from Tag 081N: the bottom map is an isomorphism by the chosen relations, the left map is injective by flatness and the density injection, and the top map is surjective by construction, hence an isomorphism; localization preserves the finite presentation displayed by $N'$. Step 5 checks the basic opens cover `Spec(B)` as $\\mathfrak q$ varies and invokes locality of finite presentation for the sheaf.

I opened every cited node and verified that each quote in `citations.json` is verbatim: the local finite-presentation definition, finite-type definitions, the repaired stalk statement, the Tag 00RC openness statement, and the finite-presentation definition. The helper node's hypotheses match the affine specialization of 05I7: $A\\to B$ is finitely presented, $N$ is finite over $B$, $\\mathfrak q$ is a prime, and only $N_{\\mathfrak q}$ is assumed $A$-flat. Its three kinds of Mathlib searches were rerun after the statement changed; all found only more general localization or sheaf declarations and no exact stalk theorem. I also searched the DAG and blueprint for 05I7, 05I8, 00RC, and the finite-type-flat-point keywords. The existing openness node is used as an off-unit tool because it is precisely the route's Tag 00RC input and no node in this trace-formula unit supplies that theorem.

Small-case checks included $U=S$ (the cover has $f_1=1$ and the argument is the usual local finite-presentation criterion), $U=\\varnothing$ (scheme-theoretic density rules it out unless $S$ is empty), and $N=0$ (all finite presentations and localization comparisons are immediate). The former false helper was the only statement fault; no hypothesis or conclusion of the item was changed.

## Not duplicates

lem-trf-flat-finite-type-flat-point-local vs lem-weil-pbc-openness-of-flatness: the new node is the stalk finite-presentation conclusion from Tag 05I7 at one flat prime, whereas the existing node is the Tag 00RC openness theorem for the flat locus of an already finitely presented module.
lem-trf-flat-finite-type-flat-point-local vs lem-pc-recd-locally-principal: the new node concerns finite presentation of a module stalk; the existing node concerns relative effective Cartier divisors.
lem-trf-flat-finite-type-flat-point-local vs lem-weil-pbc-flat-point-noetherian-model: the new node is the Tag 05I7 arbitrary-ring stalk result; the existing node supplies Noetherian approximation data at a flat point.

What was wrong in the returned node: its helper combined the Tag 05I7 stalk conclusion with the later Tag 00RC neighborhood conclusion and was false. The repair separates these facts exactly as the source does. The item proof now cites the true stalk node and the existing openness node at the corresponding steps.

What I could not finish: nothing.
