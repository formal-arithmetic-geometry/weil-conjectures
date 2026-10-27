# Worker report: lem-trf-monomorphism-finite-type-composite-lqf

## Files written

- dag/nodes/sec-trace-formula/lem-trf-monomorphism-finite-type-composite-lqf.json: unchanged statement, complete four-step split, existing dependencies only; not a Mathlib leaf for the exact affine-neighbourhood pointwise conclusion.
- citations.json: a verbatim statement quote for each of the eight citations across the four proof steps.
- searches.jsonl: five actual searches through msearch.py, read before recording their verdicts.
- report.md: this report.

## New nodes

None: 0 new nodes and 0 new Mathlib leaves. The diagonal inverse is a short universal-property calculation, not a separate lemma. The finite-type cancellation and unramified-to-quasi-finite theorem already exist and are cited.

## Attachments

None for the item. The project tag search finds no declaration of the whole item. The relevant existing declaration AlgebraicGeometry.Scheme.Hom.isLocallyQuasiFinite_of_unramified belongs to lem-weil-pbc-unramified-quasi-finite-at-points, already recorded there. I read its affine-neighbourhood signature and sorry-free proof at lean/WeilConjectures/AlgebraicGeometry/UnramifiedQuasiFinite.lean:39; it proves only the final implication of this item, so is not an attachment of the whole item.

## WANTED

None. All sources used are present locally.

## Source and route

I read Stacks schemes.tex, Tags 01L3 (lemma-monomorphism) and 01L4 (lemma-monomorphism-separated), and morphisms.tex, Tags 01T8 (lemma-permanence-finite-type), 02GE (lemma-diagonal-unramified-morphism) and 02V5 (lemma-unramified-quasi-finite). These establish the item's statement with precisely its hypotheses. I also read spaces.tex Tag 0265 (lemma-presentation-quasi-compact), first two proof paragraphs and the first representability step: the item is a general tool extracted from the quotient-presentation branch, and its requested unramified route gives the specified affine-neighbourhood conclusion. I read the trace-formula chapter, sk-i-curve-zero unit, the current main-20261015 lem-trf-local-term-locality proof, and the parent lem-trf-affine-etale-relation-separated-lqf. The source is a generic scheme-morphism argument inside that ancillary branch, not a replacement of the contracting-correspondence argument of the unit.

## Existing-node and Mathlib searches

I searched the entire DAG by the source tags 01T8, 02GE, 02V5, 01L3 and 01L4 and by monomorphism, diagonal, unramified, quasi-finite, and finite-type composition phrases. blueprint_refs.py ancestor identifies lem-trf-local-term-locality. Whole-blueprint searches for monomorphism, unramified, and locally of finite type found the already imported finite-type cancellation lemma and no alternative node stating the whole item. No new node is proposed, so there are no duplicate pairs to justify.

The five new msearch.py results are in searches.jsonl with the exact queries: LeanSearch and two LeanFinder phrasings, Loogle for LocallyQuasiFinite together with Mono, and a grep of AlgebraicGeometry/Morphisms. All services answered; Loogle returned zero hits. I read the hits, FiniteType.lean:72-74, and QuasiFinite.lean:330-397. The finite-type cancellation and diagonal facts are present in Mathlib. Mathlib's QuasiFiniteAt is defined by a stalk ring map and its LocallyQuasiFinite by an affine ring-map property; the item's explicit isolated-fibre affine-neighbourhood definition is a different interface. Its comparison is substantive, and the exact existing node lem-weil-pbc-unramified-quasi-finite-at-points supplies that interface without falsely treating the entire item as a one-line Mathlib specialization. The creator's prior searches are retained unchanged; this delivery appends only the searches made here.

## What was wrong and what remains

The original node had no proof. Its statement is correct as written and all statement dependencies are retained. There is no statement dispute or weakening. The proof is now explicit; no work remains within this one-level split. No Lean was written and no compiler or build was run.

## Review by Q145

I compared each clause with the five Stacks results listed above, including the absence of quasi-compactness of X and separatedness of g. I opened every cited node and copied its actual statement into citations.json.

Step 1 uses precisely clause (a) of lemma-nagata-finite-type-to-separated-target, which states cancellation of locally finite type for an arbitrary triangle. Substituting T=X, p=g gives f locally finite type. Clause (b)'s separatedness assumption is irrelevant and is not used. This is the non-elementary cancellation theorem already provided by that Mathlib leaf.

Step 2 uses only def-pc-fibre-product, whose statement gives the two projections, their compatibility, the diagonal lift, and uniqueness of a morphism with prescribed projections. Compatibility and monicity give p1=p2. I checked both inverse identities: p1 after the diagonal is the identity, and the diagonal after p1 has the same two projections as the identity of the fibre product. This is an elementary argument from the universal property; it hides no representability or immersion theorem.

Step 3 opens the statements of def-weil-open-immersion and def-weil-closed-immersion. The isomorphic diagonal has image the whole space, open and closed, and isomorphic structure sheaves; its sheaf map is therefore surjective. These are exactly the definitions. def-weil-proper-morphism explicitly defines separatedness by the closed diagonal (no properness conclusion is taken). def-weil-unramified-morphism explicitly defines unramifiedness by locally finite type and the open diagonal, so step 1 supplies the remaining hypothesis. These four definition citations are sufficient: no conormal-sheaf or differentials result is used implicitly.

Step 4 uses the exact statement of lem-weil-pbc-unramified-quasi-finite-at-points, not its proof or the superficially similar Mathlib notion. Its only hypothesis is an unramified scheme morphism, now established; it concludes the finite-type affine neighbourhood and isolated fibre prime condition at every x, and locally quasi-finite in pqf-def-quasifinite (2). I opened pqf-def-quasifinite as well: clauses (1) and (2) are exactly those conclusions. This is a generic tool from another unit, declared in split_report.tool_uses because sk-i-curve-zero gives no separate theorem about these scheme-morphism properties. No other node's maintainer-owned tool_uses field is edited.

For small cases, I checked the empty scheme (pointwise claim vacuous; the diagonal calculation still applies), the identity map, and a nonreduced closed immersion Spec(k) into Spec(k[epsilon]/epsilon^2). The last example tests that no flatness, etaleness, or open-immersion conclusion for f itself is accidentally used; it is the diagonal that is open. The same proof works for a non-quasi-compact open immersion when the composite is locally finite type, so it adds no hidden global finiteness assumption. The definitions and the cancellation step impose no separatedness on g. No new statements need separate edge-case tests.

I checked delivery-errors B through E against these files: the statement is self-contained with its existing notion nodes, there are no new unsplit nodes carrying proofs, no clauses are moved to replacement lemmas, all non-elementary inputs are named and stated by their cited nodes, and the sole categorical calculation is written out. Every proof step is below 2000 characters. Corrections were confined to filling the absent proof, its precise dependency union, source provenance, fresh search records, and the split report; the mathematical statement was kept verbatim.
