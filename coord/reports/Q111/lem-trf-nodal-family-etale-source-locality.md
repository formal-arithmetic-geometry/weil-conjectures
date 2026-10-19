# Worker report

Group Q111; item lem-trf-nodal-family-etale-source-locality; stage 1 only.

## Files written

- dag/nodes/sec-trace-formula/lem-trf-nodal-family-etale-source-locality.json: item, statement split into nine proof steps; no matching project declaration or Mathlib theorem.
- dag/nodes/sec-trace-formula/lem-trf-lfp-fppf-source-locality.json: new statement, unsplit; no Mathlib source-cover theorem found.
- dag/nodes/sec-trace-formula/lem-trf-nodal-point-etale-locality.json: new statement, unsplit; no Mathlib nodal completed-local-ring theorem found.
- citations.json: one verbatim statement quotation for every step/node use.
- searches.jsonl: actual search-command results, retained as recorded.

## Attachments

None. The project-source search for the blueprint item tag, nodal curves, and fppf source locality produced no matching declaration. The nodal matches are comments in ProjectionFormula, Kunneth/Relative and Dualizing, not proofs. The reference master is not treated as finished Lean.

## Wanted

None. All sources used are in literature/stacks-project/.

## Faults and corrections

The imported item was unsplit. Its mathematical statement is retained. The purity link now names def-weil-pure-dimension, which actually defines every irreducible component having dimension one, instead of merely naming Krull dimension. Completed local rings over Ω are understood as Ω-algebras, as in the source's ordinary-double-point definition. There is no added finiteness or separation assumption.

During drafting I rejected a bundled flatness/finite-presentation/dimension auxiliary node: it duplicated existing flatness tools and omitted the locally finite type condition needed for the pure-dimension comparison. That file is absent from the final delivery. The dimension argument is now written as steps using existing generic statements. I corrected the reverse nodal argument to use smoothness reflection before invoking the nodal hypothesis at the lift, and corrected the empty-source argument: the maps into the empty scheme force their sources empty.

Mathlib's LocalFlatDescent.lean line 38 instance for LocallyOfFinitePresentation is descent after target base change, not source precomposition. Its underlying RingHom.FinitePresentation.codescendsAlong_faithfullyFlat has the same base-change meaning. Neither gives the new source-cover statement by one-line specialization. FinitePresentation.lean supplies composition and base-change instances, which also do not assert this descent. The point searches returned etale/smooth APIs and Lagrange interpolation; the grep hit in EllipticCurve/Reduction.lean:319 is a Taylor-expansion comment, not the stated completion theorem. Searches used two natural-language formulations for each new statement; the item searches were repeated against the current command log while retaining the inherited records.

## Unfinished

No part of the item's natural-language split remains unfinished. The two new nodes are deliberately statement-only, as required for a one-level split. No Lean was written or compiled.

## Not duplicates

lem-trf-lfp-fppf-source-locality vs lem-sc-hom-etale-locus-translation: the latter asserts translation invariance of the etale locus of an abelian-variety homomorphism; it does not state general descent of local finite presentation after a jointly surjective source family, despite citing 036N.

lem-trf-lfp-fppf-source-locality vs lem-sc-etale-base-change-geometric: the latter compares etaleness at points after field extension on the target; it does not assert source-family descent of finite presentation, despite citing 036N.

No existing node cites 0C57. In particular lem-trf-nodal-point-local-criterion is a closed-node equivalence with an LCI/Fitting-ideal condition, not invariance under an etale map. The nodal-family local-model node is a relative chart theorem, not the pointwise completed-local-ring statement. Existing flatness, smoothness, etale-cover base change and dimension nodes are cited, not recreated. Whole-DAG tag and keyword searches and blueprint_refs searches for nodal etale, 0C5D, and finite presentation fppf/source yielded no blueprint duplicate. Both new nodes retain the exact historical auxiliary ancestry of the item, with the item prepended to via. They do not assert that this historical branch occurs verbatim in the current contracting-correspondence proof.

## Review by Q111

I read curves.tex, lemma-nodal-family-etale-local-source (0C5D), its preceding precomposition lemma (0C5C), and lemma-node-etale-local (0C57), with the section's definition of a node over an algebraically closed field. I verified their tags in stacks-project/tags/tags. For the finite-presentation child I read descent.tex, lemma-locally-finite-presentation-fppf-local-source (036N), including the composition and affine-algebra permanence argument. Its hypothesis is a flat locally finitely presented jointly surjective family, which includes the etale family without any quasi-compactness requirement. For the point child I used 0C57 and the preceding completed-local-algebra characterization: over algebraically closed k, residue fields at closed points are k and the etale map induces an isomorphism of completions. The version quantifying over arbitrary points is legitimate: a completion isomorphic as a k-algebra to k[[u,v]]/(uv) has residue k, forcing the original point to be k-rational, hence closed on a locally algebraic scheme. Thus no premise of closedness is silently assumed when applying it to the item's nonsmooth points. This is one local-ring invariance lemma, not the family's nodality condition renamed.

For step 1 I opened lem-trf-relative-flatness-source-cover: it states exactly the pointwise equivalence and jointly surjective flat-family consequence for a quasi-coherent module. Taking the structure sheaf is justified explicitly by the rank-one affine module and B tensor_A A=B. The etale definition supplies flatness, rather than a separate unproved implication. Step 2 uses the newly stated general fppf source result, with flatness and local finite presentation supplied by the etale definition. These steps give the finite-presentation hypotheses needed in both directions before any dimension argument.

For step 3 I opened lem-weil-pbc-etale-covering-base-change; its conclusion explicitly includes both etaleness and joint surjectivity for arbitrary base change, so it supplies the lifts even after passing to a geometric fibre. Fibre-product associativity is explained by the compatible-pairs universal property. Step 4 uses the exact ring base-change clause (1) of lem-weil-pbc-finite-presentation-base-change-composition; retaining presentation generators gives finite type. I opened pqf-lem-locnoeth-lft: it assumes only locally finite type over a locally Noetherian base, as needed here over a field, not globally finite type.

For step 5 I checked lem-sbc-flat-composite-fibre-dimension-at-point requires both maps locally finite type and the first flat. These hold by step 4 and etaleness. Its equality is an equality of local topological fibre dimensions. The zero-dimensional fibre assertion in lem-weil-pbc-etale-smooth-zero-dimensional-fibres supplies the zero summand. Step 6 uses the full statements of lem-sbc-equidimensional-open-local-dimension and lem-sbc-constant-local-dimension-components in opposite directions, with the whole scheme as the open set; their locally finite type and locally Noetherian hypotheses were established in step 4. Joint surjectivity in the reverse direction comes from step 3. This avoids treating pure dimension as an unsupported etale-local slogan.

For steps 7 and 8 I opened lem-trf-etale-source-smoothness and checked its explicit pointwise equivalence, not just its whole-family assertion. It makes nonsmoothness pass in the needed direction at the chosen lift before the nodal hypothesis is used. The new completed-local-ring lemma then applies to an etale map of geometric fibres over algebraically closed Ω, with the base fibre's purity and local finite type already established. Forward and reverse directions are both written. Step 9 uses only the impossibility of a point mapping into an empty topological space and vacuous local conditions.

I checked the delivery-errors B–E issues against the final files: definitions are named in statements; no family clause is hidden as a new auxiliary node; no elementary tensor identity or finite-presentation generator argument is made a node; all non-elementary steps list their actual statement dependencies and every listed use has a literal quotation in citations.json. Generic tools from other units are declared in split_report.tool_uses and do not replace the unit's route. No proof step exceeds 2000 characters. I tested the empty cover, an identity cover, an open subcurve, a smooth point, and the origin of Spec k[u,v]/(uv); the pointwise claim uses k-algebra completions so no residue-field identification is assumed without justification. In particular neither singularity nor closedness is assumed for an arbitrary lift before the relevant equivalence is used. There are two new unsplit nodes and zero new Mathlib leaves.
