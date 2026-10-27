# Q70 stage-1 delivery

## Files written

- dag/nodes/sec-six-functors/lem-sf-native-weil-clopen-sheaf-comparison.json: statement item, now split; six proof steps, zero new nodes, zero Mathlib leaves. The native all-sheaf assertion is not in Mathlib.
- citations.json: verbatim statement quotations for every citation of every numbered proof step.
- searches.jsonl: actual searches recorded by msearch.py; prior searches in the live item were retained, and seven searches from this run were appended to its Mathlib record.

## Attachments

None. The previous proposed attachment was refused, and this delivery does not repeat it. The project source files were read as mathematical source material; no assertion of transitive sorry-freeness is made.

## WANTED

None.

## Findings and changes

The live item had no proof. Its statement is correct for arbitrary open immersions and all native module sheaves, without quasi-compactness. The quasi-compactness required by the nearby constructibility theorem is irrelevant and was not imported. No statement or definition was changed. In particular the coefficient is the actual locally finite continuous-function ring B, not a discrete constant coefficient or a completed inverse system, and the fixed pairs are formed in the sheaf heart.

The latest blueprint prop-functor-package and its proof, clause (3), were read alongside the recorded unit and chapter. The item supplies the native sheaf-level open-factor input to proper coincidence. The seeded blueprint ancestry has a null terminal ancestor (blueprint_refs.py ancestor prints None); its existing breadcrumb and via list were preserved and its place was made explicit. The searches over extension by zero, clopen, ringed sites, and Frobenius found general ringed-site and fixed-pair results; none states this same native all-sheaf result with all clauses. No unit key-node realization is involved.

The ordinary canonical map is written on presheaf summands and extended by the sheafification universal property. Its Frobenius compatibility is verified on those same summands, with the displayed commuting equation. Clopen invertibility is proved through the existing arbitrary-ring clopen gluing theorem; it is not postulated by a newly named copy of the item's conclusion.

Generic tool citations: lem-weil-pbc-module-sheaves-colimits-forgetful supplies completeness and cocompleteness for module sheaves; lem-pur-clopen-ringed-module-gluing supplies the finite clopen product description for any commutative ring sheaf. Both are listed in split_report.tool_uses. All other dependencies follow the native definitions and the fixed-pair and localized-site route. A transitive dependency traversal found no cited node reaching the item.

## Not duplicates

No new nodes. In particular the proposed exact-extension input is already lem-pur-site-restriction-module-adjunction-exact (Stacks 03DJ), the fixed-pair exactness/conservativity input is already lem-sf-fixed-pair-created-abelian-structure, and the clopen product input is already lem-pur-clopen-ringed-module-gluing (Stacks 04TQ/04TR/04TS). The nearby lem-sf-native-weil-open-exact-constructible assumes quasi-compactness and includes a different constructibility conclusion, so it was not used for the arbitrary-open assertion.

## Review by Q70

I read the two native source files WeilSheaf/OpenImmersion.lean (especially lines 50-69 and 140-150) and WeilSheaf/ProperCohomology/OpenImmersion.lean (lines 43-66). I also read the construction and Frobenius compatibility in SixFunctors/ProEtale/Adic/OpenImmersion.lean, including the definition and adjoint normalization of the ordinary comparison, lines 230-251, and its compatibility equation, lines 374-390. For the document route I read Stacks sites-modules.tex, lemma-extension-by-zero (03DI) and lemma-extension-by-zero-exact (03DJ), including the proof of exactness, and sites.tex, lemma-mapping-property-glue (04TS) and its references to glue-maps and glue-sheaves (04TQ/04TR). There are no new nodes requiring separate sources.

For Step 1 I opened the framework, module-sheaf limits/colimits node, and fixed-pair created-abelian-structure node. The module theorem gives sectionwise limits and sheafified colimits, not just finite ones. Frobenius is an actual automorphism; reindexing by it and its inverse preserves the specified coefficient function condition, and this verifies the additive autoequivalence hypothesis of the fixed-pair theorem. That theorem explicitly gives created kernels/cokernels, exactness reflection and inverse morphisms.

For Step 2 the open-immersion base-change node states exactly that the geometric open remains open. The framework identifies the ring restriction on the localized site with B_U and defines the sheafification construction. The exact localized module-extension node explicitly states exactness for an arbitrary sheaf of commutative rings; hence it applies to B, with no finite, torsion, constructibility, compactness or separatedness hypothesis. Applying the exact forgetful functors from Step 1 proves the native exactness. Additivity is checked on presheaf maps. I did not use the quasi-compact constructibility statement as an exactness theorem for arbitrary opens.

For Step 3 the direct-image definition explicitly supplies M(V times_X U); the extension-presheaf definition supplies its summands and their restrictions; and the sheafification definition supplies unique factorization of module maps. I checked that on a summand V mapping into U, this intersection is canonically V, so the identity section map is well typed. If V does not factor through U, the source is zero, even when V meets U; no false assertion that j_* vanishes there is made. This defines the comparison on all objects and proves naturality. For Step 4, the framework specifies the actual lift and its reindexing comparisons. The same section rule after Frobenius translation gives the displayed comparison identity; naturality in phi then gives exactly the fixed-pair equation in the cited definition. No unrecorded base-change theorem is invoked for this elementary automorphism reindexing.

For Step 5 I opened the properness definition: universal closedness includes this particular base change and sends its entire closed source to a closed image. The open base-change property from Step 2 makes that image clopen. I read the whole gluing statement, which permits arbitrary commutative ring sheaves, supplies the product-of-sections quasi-inverse, and detects maps componentwise, including empty components. Thus it applies directly to the actual native coefficient ring. Its Hom description identifies the tuple (M,0) with the left extension by its universal property, while the direct-image section formula identifies the same tuple with the right extension. The comparison is explicitly identity on the open, and the unique zero map on its complement. Step 6 uses the fixed-pair theorem's explicit assertion that the underlying inverse is a commuting morphism; the equation proving naturality of inverses is written out.

I tested j empty, j the identity, zero M, and X a disjoint union of two components; all formulas give respectively zero extension, identity comparison, zero modules, and the tuple (M,0). An arbitrary non-quasi-compact open still uses the localized site theorem, so no finite-cover claim is hidden in exactness. Only the clopen comparison uses a finite partition, always the two pieces U and its open complement. No new nodes, inline hidden lemmas, new hypotheses, derived identifications or SGA sources are present. Each non-elementary step cites the full statements it uses; each step is below 2000 characters. This checks B1-B10, C1-C8, D1-D5 and E1-E7 against the actual proof rather than merely relying on the delivery gate.

## Unfinished

None at stage 1. The server dry run and final delivery are the remaining mechanical actions.
