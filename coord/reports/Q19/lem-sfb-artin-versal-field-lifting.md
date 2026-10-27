# Q19: lem-sfb-artin-versal-field-lifting

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-artin-versal-field-lifting.json: split, with five steps following Stacks 07XT and expanding 07XG using the explicit construction of 07WX.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-type-field-point-characterization.json: statement, unsplit; no Mathlib match for arbitrary schemes (01TA).
- dag/nodes/sec-six-functors-basics/lem-sfb-artinian-finite-type-residue-criterion.json: statement, unsplit; no Mathlib match for the ordinary finite-type criterion (02HV, 07DT(2)).
- dag/nodes/sec-six-functors-basics/lem-sfb-artinian-finite-residue-restriction.json: statement, unsplit; no Mathlib match for the inverse-image ring under a finite residue extension (07W8).
- citations.json records a verbatim statement quotation for every dependency of every proof step. searches.jsonl is the actual msearch log; work/search-results.jsonl and work/item-search-*.txt retain the outputs read. No Lean, repository, or launcher file was written.

## Attachments

None. Searches by the exact blueprint tag and the words versal/Schlessinger in lean/WeilConjectures found no corresponding declaration. Artinian and essential-finite-type project declarations have different statements and are not attachments.

## Literature

No WANTED source. Read literature/stacks-project/artin.tex: 07XF (definition-versal), 07XG (lemma-versal-change-of-field), 07XT (lemma-versal-smooth), and 07WX (lemma-change-of-field), especially the explicit two restriction maps and the RS equivalence. Read formal-defos.tex 07W8 (situation-change-of-fields), its length proof that B times_l k is Artinian and its surjection assertion, and 07WD (lemma-change-of-fields-smooth). Read morphisms.tex 01TA (lemma-point-finite-type) and 02HV (lemma-artinian-finite-type), plus algebra.tex 07DT(2) and 00J8. The proof uses exactly the finite-extension comparison route of 07XT/07XG, expressed without introducing categories of predeformations as extra definitions.

Read the latest blueprint, literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. The newest direct-image proof differs from the historical alteration expansion recorded in this node's long ancestry; this delivery does not alter the unit route or assert that those old paragraphs occur verbatim in the newest snapshot. It proves the assigned local supporting fact needed by the existing Artin-smoothness parent. tools/blueprint_refs.py ancestor reports null for the nearest imported ancestor; retain that existing ancestry, with an explicit place rather than inventing an imported node. Whole-blueprint searches for versal at, Schlessinger, finite type point, field point, Artinian local, 01TA, 02HV, 07W8, and residue restriction found no equal statement. Broader searches for versal and residue field were also read; their hits concern universal constructions, fields, or unrelated residue objects.

## Corrections and unfinished work

The assigned statement is unchanged and needs no STATEMENT-DISPUTED correction. Its initial proof was empty. The new proof supplies the residue-extension argument rather than moving its conclusion to a new 'change-of-field versality' node. New nodes are general geometric or ring facts and contain no proof sketch or proof dependencies. The ordinary-finite-type criterion is deliberately stronger than the existing essentially-finite-type implication; that implication alone cannot check the RS hypothesis.

During review I removed an unnecessary nilpotence clause from the new residue-restriction node and cited the existing Artinian-local nilpotence node instead. There is no assumption that the Artinian rings contain a coefficient field, no separability assumption, and no descent hypothesis beyond the stated RS equivalence. No mathematical gap is left in the item; the three new statement-only nodes remain for future splitting as required by the one-level contract.

## Not duplicates

lem-sfb-finite-type-field-point-characterization vs lem-sfb-finite-type-points-detect-open: the latter asserts enough finite type points and detection of open subsets; it does not characterize a given field-valued finite type morphism or give its finite residue extension. The shared 01TA in that node's proof is not its statement.

lem-sfb-artinian-finite-type-residue-criterion vs lem-weil-pbc-artinian-local-essentially-finite-type-residue: ordinary finite type, with both directions, is needed here; the existing node only gives essential finite type from essential finite type of the residue field. Localization is not eliminated by its statement.

lem-sfb-artinian-finite-type-residue-criterion vs lem-weil-pbc-popescu-artinian-flat-subalgebras: the existing node constructs flat essentially finite type subalgebras in positive characteristic under a cotangent-complex hypothesis; it does not give the ordinary finite-type criterion for an arbitrary base ring.

lem-sfb-artinian-finite-residue-restriction vs lem-sfb-ferrand-scheme-pushout: the new node proves the Artinian local nature of a residue-restricted ring and preservation of surjections, not existence or the universal property of its scheme pushout. The latter is cited directly from the existing node.

lem-sfb-artinian-finite-residue-restriction vs lem-weil-pbc-artinian-local-noetherian-nilpotent: the new node concerns a different ring constructed inside B; the existing node assumes a ring is Artinian local. Its nilpotence conclusion is reused, not recreated.

## Review by Q19

I read the source statements and proofs listed above against the five steps, and opened the full statement of each cited node. Step 1 uses the new 01TA characterization exactly for the finite extension l/k and the finite-type-point assertion. I wrote out the finite-generation argument making alpha a finite type morphism; Artin--Tate is then applied to the actual R-subalgebra k of l, with l finite over k and R Noetherian. This verifies k is finite type over R without an illicit inference from the definition of residue field or from l being only finitely generated as a field.

Step 2 uses the residue-restriction statement for C and C-prime being Artinian local and the map being surjective with residue field k. It uses the ordinary finite-type residue criterion for all four Artinian rings, and the existing Artinian-local structure statement for nilpotence. The kernel of C-prime to C is the kernel of B-prime to B with zero k-coordinate; thus it lies in the nilpotent maximal ideal. These checks ensure every scheme in the RS squares is finite type over R, a hypothesis the proof cannot omit.

Step 3 takes only the affine pushout assertion from lem-sfb-ferrand-scheme-pushout, quoted in citations.json. Both input schemes are affine, the maps to l are surjective, and the field extension is integral: linear dependence among powers of a field element gives a monic polynomial. Thus every hypothesis of that node holds, and its categorical pushout property gives a_C. I did not use the Ferrand node to assert Artinianness. Step 4 uses only the RS equivalence already assumed in the item's statement: essential surjectivity glues w-prime, and full faithfulness gives the chosen comparison over C. Its two components are described explicitly and agree over l. Step 5 is the definition of versality already written in the item, applied to the verified surjection C-prime to C; restriction to B-prime gives the lift, and restriction to B recovers the specified theta by its explicitly chosen B-component. These last two steps are elementary uses of the hypotheses and definitions, not black-box deformation theorems.

For each new node I read its source: arbitrary-scheme 01TA for the first, 02HV and 07DT(2) for the second, and the comparison construction 07W8 for the third. Tested the field case B=l, where C=k, and the identity extension l=k, where C=B. Tested q an isomorphism and a nontrivial nilpotent quotient. For B=l[epsilon]/epsilon^2 and l/k finite, C=k+l epsilon has finite length; this includes inseparable extensions, so no etale argument is being smuggled in. Zero rings cannot be Artinian local rings with the specified nonzero field residue. In the characterization no Jacobson hypothesis was inserted: the image is closed only in some affine neighbourhood. The finite-type criterion does not assume a coefficient-field section or characteristic zero.

Against delivery-errors B--E: every new statement introduces its own rings, fields and maps, supplies inline Artinian/local meanings, cites definitions for the remaining notions, has the precise Stacks label/tag, and contains no proof. Exact mathlib queries were run with msearch, all hits read and recorded. Jacobson-only finite-point criteria, essential-finite-type residue lemmas and finite-type-to-finite results do not state these nodes. New nodes are not clauses of the deformation-lifting item. Existing statements and citations have been checked without using their proofs as interfaces, dependency directions do not point back to this item, and no proof step exceeds 2000 characters. The existing Ferrand and Artin--Tate facts are reused. The Artinian-local structure lemma is declared as a generic off-unit tool. All work authorized for this delivery is complete before running preflight.
