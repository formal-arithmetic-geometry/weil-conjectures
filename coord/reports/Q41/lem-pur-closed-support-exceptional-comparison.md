# Stage-1 report: lem-pur-closed-support-exceptional-comparison

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-closed-support-exceptional-comparison.json` — statement, split proof, and no new nodes.
- `citations.json` — verbatim statement quotes for every cited node in every proof step.

## Attachments

None. I searched the read-only slopmaster2 source for the item id and its support/exceptional comparison terminology; no sorry-free project declaration states this item exactly.

## WANTED

None.

## What was wrong or incomplete

The imported item had an empty proof and was marked unsplit. Its source paragraph is an agent-extracted comparison obligation, so I retained the exact statement and supplied the missing argument. The proof now explicitly specializes the relative exceptional-adjoint theorem to (c=(\mathrm{id}_Z,i)), including the identification (P_c=i_*), and uses the stated bounded-below etale-origin assumptions when applying Yoneda. No statement correction was needed. No duplicate DAG node was found for this comparison; the existing closed-support localization and relative exceptional-adjoint nodes provide the two Hom bijections.

## What I could not finish

Nothing in the stage-1 scope remains unfinished. No Lean source was written and no compiler or build tool was run, as required.

## Review by Q41

I read the complete item node, its `stmt_deps`, the unit `sk-prop-a1-kummer`, chapter `sec-smooth-purity`, and the source paragraph in `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/lem-pur-gysin-structure.proof.md`. I also read the support-localization statement and proof in the master blueprint and the full statement of `thm-sf-ambient-adjoint-class`. The item hypotheses match those sources: (j) is quasi-compact for the support triangle; (i) is a closed immersion and therefore supplies the proper part of the compactification (c=(\mathrm{id}_Z,i)); (T), (B_0), and (B) are used only in the bounded-below etale-origin class where the two Hom bijections are available.

Step 1 uses exactly the support node's assertion that (Rs^!) is right adjoint to (s_*) on bounded-below derived categories and that the counit is canonical. Step 2 uses the relative-adjoint node's natural Hom bijection and bounded-below typing, while the identity open part of (c) makes (P_c) the exact termwise (i_*). Step 3 applies Stacks Categories Tag 001P to the two natural representations of (T\mapsto\operatorname{Hom}(i_*T,K)), writes the representing morphism explicitly, constructs its inverse from the inverse natural transformation, and checks both composites by naturality; the two cited adjunction nodes are the sources of the bijections used. Step 4 evaluates the defining relation at (B_0) and uses naturality of the relative adjunction to identify (e_{B_0}(\phi_K)) with (e_B(1_B)\circ i_*\phi_K), giving the required counit equation.

I checked edge cases in the abstract argument: if (K=0), both Hom bijections are singleton bijections and φ is the unique isomorphism between zero representing objects; if (Z=\varnothing) or (i=\mathrm{id}), the same Yoneda comparison reduces to the corresponding zero or identity adjunction. The Mathlib searches were rerun for the item with LeanFinder, Loogle, grep, and LeanSearch; generic Yoneda/adjunction declarations were found, but none states the site-specific bounded-below etale-origin comparison, so the item remains a project statement rather than a Mathlib leaf. I found no source error, no duplicate, no hidden new lemma, and no dependency-cycle route.
