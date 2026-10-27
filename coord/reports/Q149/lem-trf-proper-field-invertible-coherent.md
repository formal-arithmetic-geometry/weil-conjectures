# Stage-1 report: lem-trf-proper-field-invertible-coherent

## Files written

- dag/nodes/sec-trace-formula/lem-trf-proper-field-invertible-coherent.json: existing statement, split in four steps; no Mathlib match for the whole item.
- citations.json: all 13 step/node pairs, with verbatim statements.
- searches.jsonl: five searches run through msearch.py for this item.
- report.md: this report.

There are 0 new nodes and 0 new Mathlib leaves. No Lean was written or compiled. Only the designated sandbox was written.

## Attachments

No attachment for the whole item. AlgebraicGeometry.Scheme.Modules.isNoetherian_of_isProper in WeilConjectures/AlgebraicGeometry/Modules/HilbertPolynomial.lean:255 proves only the Noetherianity clause. The existing coherence equivalence is already attached to pqf-lem-coherent-ft-locnoeth; its current source was read in WeilConjectures/AlgebraicGeometry/CoherentFiniteTypeLocallyNoetherian.lean:151. No new attachment is requested.

## WANTED

None. All sources used are present locally.

## Corrections and route

The imported statement is correct and unchanged. Its empty proof is replaced with the argument of coherent.tex Tag 01XZ (lemma-coherent-Noetherian), with the proper-field preparation of morphisms.tex Tag 01T6 (lemma-finite-type-noetherian). Properness supplies finite type; local Noetherianity follows by the existing 01T6 node, and quasi-compactness by the existing affine-base lemma. An invertible module has one local generator, so the existing general 01XZ criterion proves coherence. The structure sheaf is handled by the same criterion after its local description as the sheaf associated to the ring itself.

This is the proper-field preparation required by the recorded ancestor chain from lem-trf-curve-degree-tensor-additive to the fibrewise ampleness part of lem-trf-local-term-locality. The chapter and unit records were read; neither is changed. This is not a key node of the unit, so no realized fields are changed. Blueprint searches for 01XZ and 01T6 found the existing general nodes, which are cited instead of duplicated. Searches for invertible/coherent and proper/Noetherian did not find a blueprint node stating the whole item. The item is not the same statement as either general criterion, so blueprint.same_as remains empty.

The generic tool uses are declared in split_report: the coherence criterion, and the affine associated-module construction. These do not replace any unit-level route.

## Mathlib searches

The five queries in searches.jsonl were all read: a whole-item LeanFinder query, a Loogle query for IsNoetherian together with IsProper, a grep for coherent/invertible predicates, a LeanSearch query for coherence of a locally free rank-one module, and a second LeanFinder query using quasi-coherent finite type. The first returned Noetherianity predicates and the affine criterion; the second semantic phrasing returned finite-type and finite-presentation definitions. None states Stacks coherence of the two module sheaves together with Noetherianity. The source grep returned no coherent predicate. Finite presentation is not silently identified with the finite-kernel definition of coherence: the existing 01XZ theorem supplies that non-elementary bridge. Historical searches in the item were retained; the new searches are appended with their exact query text and actual results.

## Not duplicates

No new nodes were created. In particular, no proper-field Noetherianity node, invertible-coherence node, or structure-sheaf-coherence node was created: those would merely name clauses of the item. The broader existing pqf-lem-coherent-ft-locnoeth and pqf-lem-locnoeth-lft statements are reused.

## Review by Q149

I read coherent.tex at lemma-coherent-Noetherian, including the equivalence and its final sentence, and morphisms.tex at lemma-finite-type-noetherian with its proof. I also read properties.tex definition-noetherian (01OV) and schemes.tex lemma-spec-sheaves (01HV), which justify the exact conventions used for Noetherianity and the affine structure sheaf. There are no new nodes requiring their own source review.

For Step 1 I opened the statements of def-weil-field, def-weil-pbc-noetherian-ring, def-weil-affine-spectrum and pqf-def-locnoeth. They provide precisely field inverses, the finite-generation-of-ideals definition, the global ring of the affine spectrum, and the affine-cover definition. The proof that a field is Noetherian is written, rather than attributed to a definition: every nonzero ideal contains 1. Its sole affine chart gives the required cover without invoking an unrecorded theorem about localizations.

For Step 2 I opened def-weil-proper-morphism and def-weil-finite-type-morphism: proper includes separated and finite type, and finite type includes quasi-compact and locally finite type. pqf-lem-locnoeth-lft assumes exactly a locally Noetherian target and a locally finite-type map; Step 1 and properness discharge these. lem-weil-pbc-qcqs-over-affine explicitly includes the separated finite-type-over-field case, so it really supplies quasi-compactness of Y. No extra finite-dimensional, smooth, integral or reduced hypothesis is used.

For Step 3 I checked def-sc-invertible-module really includes both quasi-coherence and a Zariski rank-one frame. The inverse frame map is the finite-type surjection required by pqf-def-coherent; this is elementary and is written out. For the structure sheaf, I checked def-weil-affine-spectrum together with lem-weil-pbc-spec-module-tilde-sections. The latter supplies the actual associated sheaf, its principal-open localization sections and the localization restriction maps, not merely a definition of quasi-coherence. With module A, these are the same sections and restrictions as the affine structure sheaf (01HV); equality on the principal-open basis identifies the sheaves. Thus the claimed quasi-coherence is justified. The identity map supplies its one generator. This avoids applying the coherence criterion before its quasi-coherence hypothesis has been proved.

For Step 4 I checked the statement of pqf-lem-coherent-ft-locnoeth, not its proof: it is the iff between coherence and quasi-coherent finite type on a locally Noetherian scheme. Both hypotheses are established separately in Steps 2 and 3. It can be applied twice, to N and O_Y. I did not rely on the weaker predicate Scheme.Modules.isCoherent in Modules/Coherent.lean, whose docstring expressly distinguishes it from Stacks coherence on general schemes.

I tested the empty scheme, a nonreduced proper zero-dimensional scheme Spec(k[e]/e^2), and a disjoint union of two proper schemes. The argument works in all three cases; local-generation assertions on the empty scheme are vacuous, and neither reducedness nor connectedness enters. Properness is used for finite type and quasi-compactness, and local Noetherianity is retained in the coherence application. All four steps are below 2000 characters, with no hidden long sublemma. I checked delivery-errors B through E: no new statement-only/duplicate/Mathlib-leaf issues arise, every cited statement is open and quoted in citations.json, every non-elementary ingredient is an existing cited node, and the proof carries the argument rather than moving clauses into fresh nodes. No statement dispute was found.

## Unfinished work

None in the stage-1 split. Server dry run and push are the remaining delivery operations.
