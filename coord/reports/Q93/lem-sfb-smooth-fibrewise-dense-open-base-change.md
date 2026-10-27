# Q93 stage-1 delivery

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-fibrewise-dense-open-base-change.json: item split, statement preserved.
- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-fibre-dense-quasi-compact-selection.json: statement-only lemma, unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-flat-finitely-presented-module-fibre-injectivity.json: statement-only lemma, unsplit, no Mathlib match.
- citations.json: verbatim statements for every step citation.

## Attachments

None. Searched upstream WeilConjectures for the exact blueprint tag and the density notion. The smooth depth-two purity declarations require additional hypotheses and prove extension/flatness results, not this assertion. No project declaration gives both clauses. Existing sbc-lem-smooth-geometrically-reduced is reused, not reattached.

## WANTED

WANTED: Bosch–Lütkebohmert–Raynaud, Néron Models, §2.5, Lemmas 1 and 3, printed pp.55–57, for the item and lem-sfb-smooth-fibre-dense-quasi-compact-selection. The local literature copy is absent. Read the existing primary scan URL from the item's source with the web reader, PDF pages 61–63 (printed pages 55–57). No download or repository change. Accordingly the assembly is marked agent-written. The new lemma's source records the absent local document and exact primary scan.

## Audit and changes

The item is mathematically sound, including arbitrary T', empty fibres, reducible fibres, and non-quasi-compact V. Its source's Lemma 1 assumes a quasi-compact open, so applying it directly to this item would omit a hypothesis. Lemma 3 supplies a quasi-compact subopen simultaneously dense in all fibres on each quasi-compact smooth chart. This selection is a substantive lemma, not a compactness argument applied separately to individual fibres. It is smaller than the item: it asserts existence of a finite selection, neither base-change density nor a structure-sheaf injection.

BLR supplies only a Noetherian proof of its schematic-density implication, referring elsewhere for the general case. I replaced that part with the arbitrary-ring Stacks Tag 0AT9 criterion on a finite tuple of principal localizations. The new module node is a general fibrewise universal-injectivity theorem, not either clause of the item. Its hypotheses exactly include the finitely presented algebra, localized finitely presented source module, and flatness of both A-modules; these restrictions are not omitted.

No statement dispute, target change, unit-route change, SGA source, Lean writing, compilation, or repository write. The current blueprint's sk-thm-sf-ctf-stability source and proof were read in literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/. This is a supporting algebraic-geometric lemma deep in its inherited direct-image/compactification branch, not a realization of its key statement. The inherited ancestor tool returns null, retained in new-node provenance. All off-unit foundations are declared in split_report.tool_uses.

## Searches and Not duplicates

Whole DAG statements, upstream source, and whole-blueprint searches were read before creation: dense, S-dense, universally injective, finitely presented flat, quasi-compact S-dense, pure spreadout, and quasi-compact open. Searches by exact Stacks Tag 0AT9 and label found no existing node. BLR §2.5 Lemma 3's finite-selection statement likewise has no existing node. The many dense-open nodes impose generic-fibre, integral-base, Noetherian, field, or flat-pullback hypotheses; none gives simultaneous finite selection or 0AT9. Both new nodes have all four msearch methods and two semantic phrasings recorded from searches.jsonl; item searches were rerun and added without discarding the inherited searches. The Mathlib local finite-free residue-field test and smooth cotangent test were read in RingTheory/LocalRing/Module.lean:334 and RingTheory/Smooth/Local.lean:34; their finite-free/cotangent hypotheses do not cover the arbitrary flat target product here. Mathlib's scheme-theoretic dominance flat-pullback result requires flatness of the base change, unlike arbitrary T' here.

## Not duplicates

No same-tag new/existing node pair was found for Tag 0AT9. The selection lemma has a BLR source rather than a Stacks tag. lem-sfb-smooth-fibre-dense-quasi-compact-selection vs lem-trf-generic-open-principal-multiplication-data: the latter assumes an integral base and selects principal opens only on the generic fibre; the former works over every base and selects an open dense in every fibre at once. lem-sfb-flat-finitely-presented-module-fibre-injectivity vs lem-trf-localized-generic-multiplication-universal-injectivity: the latter assumes an integral base, generic injectivity of a specific multiplication map, and flatness of its cokernel after localization; the former permits arbitrary bases and an arbitrary A-linear map, testing all residue fields without assuming a flat cokernel.

## Review by Q93

I read BLR §2.5's S-density paragraph, Lemma 1(b) and proof, and Lemma 3 and proof in the primary scan. Its saturation argument is the source for the new finite-selection node: smooth fibre-component saturation makes an open cover of X, from which quasi-compactness selects finitely many U_i. This argument is retained here for the next worker; it is not inserted into that unsplit node's statement. I read Stacks flat.tex Tag 0AT9 (lemma-universally-injective-if-flat) and the preceding equation-star in full, including the arbitrary A-module target and localization hypotheses. Those are the source of the other new node. I also read morphisms.tex 0383, 056D, 081H, and the reduced-density and schematic-image statements; 081H alone is insufficient because T' need not be flat.

Step 1 uses exactly the existing field-scheme universally-open projection theorem, the definition of base change, and stability of open immersions. Its nonempty-open argument proves density without a finiteness or irreducibility assumption and does not confuse points of a fibre product with a Cartesian product of point sets. The canonical residue-field extension is the one induced by g at t'. I opened each cited node statement and verified those assertions.

Step 2 uses smooth implies flat and locally finitely presented, the arbitrary-base-change pointwise smoothness theorem (its flatness is required of f, not g), and source-local smoothness to assemble the open neighbourhoods. Thus it is valid on nonreduced and non-Noetherian changed bases. All three statements were read, and none assumes a constant relative dimension.

Step 3 uses the definition of locally finite presentation to choose affine algebra charts, source restriction of smoothness, smooth-flatness, affine flatness comparison, and the new selection lemma. Affine schemes are quasi-compact, and the chart open in every original fibre inherits density by the nonempty-open criterion. The finite principal refinement follows from the basis of principal opens and quasi-compactness of W. Shrinking a finite-presentation affine chart to D(h) retains finite presentation by adjoining z and the relation hz-1. No intersection of arbitrary affine opens is declared affine.

Step 4 uses localization of an A-flat B-module to preserve A-flatness and the existing finite-product flatness statement. The geometric reducedness theorem is applied only to the smooth chart fibres; no reducedness of the total space over a nonreduced base is asserted. The reduced dense-image theorem requires a quasi-compact and quasi-separated inclusion; W_p is a finite principal union and its open immersion has isomorphic diagonal. The scheme-image node then supplies the sheaf injection. The ordinary sheaf axiom supplies the injection into the section product. I checked the two scheme-image statements separately; the first is not cited for the second's injectivity clause.

Step 5 uses the existing localization/tensor comparison with R=A and the algebra B, then Tag 0AT9 with trivial localization, source N=B finitely presented over B, and flat target the finite product from step 4. The displayed fraction formula identifies the maps, not merely their objects. Finite tensor distribution is written explicitly as a direct elementary argument. Step 6 has no hidden geometric theorem: it is restriction to a smaller open followed by the sheaf uniqueness axiom on an affine basis, and applies the conclusion to the changed family already constructed.

Edge cases checked: Y empty; an individual empty fibre; V=Y; Y=Spec(k) disjoint union Spec(k) so irreducibility is unavailable; smooth affine line over k[epsilon]/(epsilon^2) with V=D(x), so the total space is not reduced but restriction remains injective; m=0 gives M=0 and the fibre criterion forces B=0. For the new module node, N=0 is automatic and A a field reduces to the hypothesis; the source need not be finite as an A-module, which is why the finite-free local Mathlib result is not a leaf. For the selection node, U=X and X empty hold and a disconnected smooth fibre must have every component met. No non-elementary step exceeds 2000 characters; neither new node has a proof or proof dependency. Every uses entry is recorded with its verbatim statement in citations.json.

## Unfinished work

Only the two intentionally statement-only children remain for future stage-1 work. No unresolved part of the item's assembly remains. Required server dry run and direct push follow this report.
