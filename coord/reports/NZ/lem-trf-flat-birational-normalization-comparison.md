# Stage-1 worker report

Item: lem-trf-flat-birational-normalization-comparison. Group: NZ. Date: 2026-10-23.

## Files written

- dag/nodes/sec-trace-formula/lem-trf-flat-birational-normalization-comparison.json: statement, split; eight explicit argument steps; no whole-item Mathlib match.
- citations.json: thirteen step/node entries, quoting the cited statements verbatim.
- report.md: this report. searches.jsonl is the unmodified msearch.py log; write_split.py is a sandbox-local writing helper.

There are zero new nodes and zero new Mathlib leaves. The proof reuses existing leaves rather than duplicating the common algebra facts.

## Attachments

None. Searched lean/WeilConjectures for the exact id and the birational/total-fraction notions. The normal-ring/total-fraction files, normalization morphisms, and algebraic-domain fraction-ring results do not state this arbitrary-flat-base-change comparison and all its explicit clauses. No complete project declaration was found for the item.

## WANTED

None. All cited sources are available locally. No SGA source was used.

## Findings and corrections

The item was unsplit and the sandbox contained no earlier node or report, so I copied the live item. There is no repair note for this id. I preserved the statement byte for byte, the previous searches and source, and its full blueprint ancestry. No statement dispute was found.

The source is varieties.tex, Tag 0C3V, label lemma-normalization-same-after-completion, especially the proof paragraph saying a finite normal subalgebra inside the localized base is the integral closure. The source specializes to henselization and completion of a reduced Nagata local curve. This item intentionally isolates the algebra comparison for arbitrary flat scalar extension; its proof_origin is therefore agent, not a claim that Stacks states this generalization verbatim. I made the two total-fraction inverse maps and every denominator argument explicit, rather than relying on a domain fraction-field result or asserting a birational comparison without proof.

Read the trace-formula chapter, unit sk-i-curve-zero, the current main-20261015 proof of lem-trf-local-term-locality, and the parent lem-trf-curve-normalization-completion. This is the inherited historical auxiliary branch normalization input. It changes neither the unit nor its contraction route. The item is not the unit's key statement; no unit record is edited.

## Searches and reuse

Before writing the split I searched the whole DAG by flat/injective/tensor, total quotient/fraction, non-zero-divisor, localization and finite/integral notions. I opened the statements of all eight reused dependencies. The exact existing injection, localization and finite-integrality leaves suffice; none of their proofs is being used as an unstated conclusion. Whole-blueprint searches using tools/blueprint_refs.py for flat tensor, localization, birational, total quotient and total fraction found no statement-identical blueprint node. The ancestor command returns lem-trf-local-term-locality, agreeing with the inherited ancestry. No new node needed a duplicate check.

Fresh msearch.py searches (all in searches.jsonl, copied accurately into mathlib_searches) were:

- grep: `([Ff]lat.*[Bb]irational|[Bb]irational.*[Ff]lat|[Tt]ensor.*[Ff]raction[Rr]ing|[Ff]raction[Rr]ing.*[Tt]ensor)` in RingTheory; one PicardGroup hit, an invertible-ideal theorem, not the item.
- leansearch: `Flat base change of a finite birational algebra and its integral closure in the total quotient ring`; eight hits, including flat base change and TensorProduct.toIntegralClosure_injective_of_flat.
- loogle: `TensorProduct, IsLocalization`; twelve hits, describing tensor products of localizations and localization scalar structures.
- leanfinder: `Flat scalar extension of a module finite intermediate algebra in a total quotient ring embeds in the new total quotient ring and has the same total fractions`; eight hits, including IsFractionRing.trans and localization flatness.
- grep: `isBaseChange_of_isFractionRing|toIntegralClosure_injective_of_flat|isFractionRing_range_mapToFractionRing` in RingTheory; seven hits.
- leanfinder, second phrasing: `Clearing a regular common denominator in a finite intermediate subalgebra identifies the total quotient rings after flat base change`; eight hits, including Algebra.IsAlgebraic.isBaseChange_of_isFractionRing.

I read the returned signatures and Mathlib sources: Flat/Basic.lean:113-134; Localization/Defs.lean:488-546; IntegralClosure/Algebra/Basic.lean:64-73; Smooth/IntegralClosure.lean:38-56; Algebraic/Integral.lean:510-531; Localization/AsSubring.lean:34-75; Localization/BaseChange.lean; PicardGroup.lean:921. The ambient tensor-product integral closure is not Q(R); localization tensor results assume an actual localization; the algebraic fraction-ring result assumes a domain extension. They are not one-line matches for the item. Existing leaves already cover the generic facts these searches did find. The older 2026-10-22 search entries, including the explicitly unavailable LeanSearch request, are retained as inherited history rather than represented as fresh calls.

## Review by NZ

I checked delivery-errors B through E with the node and the sources open. There are no new statements, proof-carrying unsplit leaves, definition-only citations disguising an additional theorem, or clause-restatement nodes. All non-elementary inputs are already named DAG statements. The eight steps are 380-692 characters, so none exceeds the 2000-character long-step threshold. The elementary steps are explicit ring identities or tensor-generator arguments, not an assertion that the whole result follows from a definition.

For step 1 I read algebra.tex Tags 00HB (definition-flat), 00HD (lemma-flat), 00CP (proposition-universal-property-localization), including the preceding fraction-kernel calculation. def-weil-pbc-flat-ring-map says exactly that R is flat over A. lem-trf-flat-tensor-preserves-injection states tensor injectivity for an arbitrary injective linear map, so it applies to multiplication by a regular element on A (no finite presentation or faithful-flatness condition). def-weil-module-base-change supplies the base-changed map. The cited ring-localization node is the ring result, not the similarly named category-localization result: it supplies existence, fraction formula and uniqueness, with images of all denominators units. That units hypothesis has just been established.

For step 2 I read the finite-module definition (Tag 0518) and the denominator paragraph in 0C3V. def-weil-finitely-generated-module supplies finite linear combinations only. The displayed product calculation proves the common denominator and regularity directly; it does not cite a general conductor theorem with extra Noetherian hypotheses.

For step 3 I checked the same injection leaf on both B -> A, b -> sb, and B -> B, b -> sb. Both maps are injective because B is a subring of Q(A), where s is a unit. The flat module being tensored is R, not B; the proof never claims B is flat. The base-change node gives the formula for d_R and compatibility with composition. The two displayed tensor identities prove the relations with i and prove injectivity of i without requiring f injective.

For step 4 I read algebra.tex Tag 00CX (lemma-tensor-product) and def-weil-pbc-module-tensor-product. That statement includes the bilinear universal property and pure-tensor generation, exactly the inputs used to define j and extend the displayed multiplicativity identity to finite sums. The formula alpha*j(c)=d_R(c) and the two previously proved injections prove injectivity of j. This also proves that the image is in R[1/alpha]; it is not merely inferred from an unspecified localization comparison.

Step 5 uses no new black box. I checked separately both directions of regularity needed by the localization maps. In particular t regular on C need not lie in R: alpha*t does lie in R by step 3, and the proof tests its annihilator in R by passing into C and canceling t and alpha there. Its inverse in Q(R) is written explicitly. This is the critical calculation that would be missing if one simply wrote Q(C)=Q(R).

For step 6 I reopened the ring-localization leaf and verified its hypotheses for J and H using step 5. Uniqueness applies to JH by agreement on R, and to HJ only after proving agreement on all C. The latter is proved using i(d_R(c))=alpha*c and alpha regular on C, not by unjustified agreement on R alone. The fraction formula, regular denominator and compatibility with C are explicit. This also proves independence of all denominator choices.

For step 7 I read algebra.tex Tag 00GK (lemma-finite-is-integral) and its Mathlib leaf lem-weil-pbc-finite-algebra-is-integral. Its only hypothesis is module finiteness, proved here by displaying the generators b_h tensor 1 and using the tensor-generation clause of def-weil-pbc-module-tensor-product. The finite-module definition supplies the meaning of that condition. Applying j to a monic equation gives the claimed inclusion in the integral closure.

For step 8 I read def-weil-pbc-integral-closure and its sources 00GI/00GP. Applying H to a monic equation over R explicitly produces a monic equation over C, so integral closedness is used in exactly Q(C), as the item assumes. Applying the already constructed inverse J then proves the opposite inclusion. No assertion that a reduced ring is automatically integrally closed is used.

I tested edge cases: B=A gives C=R with the identity comparison; s=1 gives a denominator-free construction; the empty generating family can occur only for the zero ring, where s=1 and every ring/fraction formula is still valid. If R=0 (a permitted flat algebra), all injections and fractions are maps between zero rings. A nonfaithful flat projection A=k x k -> R=k kills one component; the proof only preserves regular elements and never asks phi or f to be injective. The normalization of k[x,y]/(xy) and its identity flat base change test the zero-divisor case: regularity concerns elements regular on the whole ring, and alpha*t is tested by its annihilator, not by being merely nonzero. Reducedness is retained even though the comparison proof does not need it. No statement or target was weakened.

The citation file contains a verbatim full statement for each used node at each step; this allows the server quote check to verify the exact text. Every cited node is existing and unmerged, every use is included in proof_deps, and all reused theorem nodes are Mathlib leaves. No off-unit unsplit tool declaration is necessary.

## Unfinished work

None in this stage-1 split. The required dry run and delivery are recorded by the delivery tool; no Lean was written, no compiler or Lake/build command was run, and no repository or launcher file was edited.
