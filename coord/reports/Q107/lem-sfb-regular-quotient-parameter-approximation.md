# Stage-1 report: lem-sfb-regular-quotient-parameter-approximation

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-regular-quotient-parameter-approximation.json: item, split into three proof steps; statement unchanged; not in Mathlib.
- dag/nodes/sec-six-functors-basics/lem-sfb-regular-local-graded-cotangent-criterion.json: one new statement-only node, unsplit; no Mathlib match. This is Milne 13.2(a), a general regularity criterion, with the canonical maps and dimension conclusion stated explicitly.
- citations.json: literal statement excerpts for every step/node pair.
- searches.jsonl: unmodified msearch log of actual searches.

## Attachments

None. Searched WeilConjectures by the exact blueprint tag and by regular quotient, parameters, approximation, jets, symmetric cotangent, and associated graded terminology. Existing RegularLocalGeneratorsRegularSequence proves the parameter-quotient tool, not the arbitrary ideal finite-jet criterion. RegularLocalQuotientKernelParameters concerns a quotient already assumed regular. Neither states the item. No compiler was invoked.

## WANTED

None. The necessary Milne PDF and Stacks TeX are present.

## Corrections and scope

No statement dispute or source error. Milne Lemma 13.3 permits the regular system of parameters to vary with the jet order. Its proof uses a canonical degree-wise symmetric-power map, not a compatible inverse system of parameter choices. I retained that distinction, J contained in the maximal ideal, all integers n at least one, s between zero and d, and the empty-tuple convention.

The source's n=0 test is automatic because both ideals are contained in the maximal ideal. The imported formulation starts at n=1, which suffices for all positive graded pieces. Nakayama supplies the omitted explicit passage from a cotangent basis to generators of the maximal ideal. Every proof step is below 2000 characters (578, 731, 1049 when first written).

Read GOAL.md, the chapter record, unit record, and latest blueprint unit and direct-image proof. This commutative-algebra input is below the existing alteration/fixed-scheme smoothness chain. No unit or chapter route is changed. The inherited blueprint ancestor is null; blueprint_refs.py ancestor returns None for the item. I retained its place/via history and extended the new node's place to the exact Milne 13.2(a) input.

## Not duplicates

lem-sfb-regular-local-graded-cotangent-criterion vs lem-sc-regular-local-domain: the latter only concludes that a regular local ring is a domain; its use of Tag 00NO is in its proof, not its statement. It supplies neither canonical graded multiplication maps nor the converse regularity criterion.
lem-sfb-regular-local-graded-cotangent-criterion vs lem-sfb-regular-hypersurface-initial-form: that node assumes a regular ambient ring and a nonzero hypersurface equation; its polynomial associated-graded clause does not characterize regularity for an arbitrary Noetherian local ring, and cannot be applied to a field or arbitrary J quotient as the converse criterion here requires.
lem-sfb-regular-local-graded-cotangent-criterion vs lem-weil-pbc-symmetric-algebra-graded: that node supplies the grading of a symmetric algebra of an arbitrary module. It asserts nothing about the multiplication map to the maximal-ideal associated graded of a local ring or its regularity.
lem-sfb-regular-local-graded-cotangent-criterion vs lem-weil-pbc-regular-local-generators-regular-sequence: the latter proves regularity of quotients by fixed partial parameters, not the converse canonical tangent-cone criterion for arbitrary local rings.
lem-sfb-regular-local-graded-cotangent-criterion vs lem-per-noetherian-local-colimit-regular: that node proves regularity of a Noetherian directed colimit of regular local rings; no such colimit is given here.

lem-sfb-regular-local-graded-cotangent-criterion vs lem-weil-pbc-completion-dimension: only compares the dimensions of a ring and its completion; it has no canonical symmetric-power criterion.
lem-sfb-regular-local-graded-cotangent-criterion vs lem-weil-pbc-noetherian-local-dimension-le-generators: only bounds dimension by a number of maximal-ideal generators, without a regularity converse or graded map.
lem-sfb-regular-local-graded-cotangent-criterion vs lem-weil-pbc-noetherian-local-finite-krull-dimension: asserts finite Krull dimension for any Noetherian local ring; it gives no criterion for regularity.
lem-sfb-regular-local-graded-cotangent-criterion vs lem-weil-pbc-noetherian-local-system-of-parameters: constructs an ideal of definition with dim R generators, which need not generate the maximal ideal; it does not identify the tangent cone or characterize regularity.
lem-sfb-regular-local-graded-cotangent-criterion vs lem-sfb-henselian-parameter-root-regularity: concerns the explicit finite algebra adjoining parameter roots to a henselian regular ring, not an arbitrary local ring or the symmetric-cotangent criterion.
lem-sfb-regular-local-graded-cotangent-criterion vs lem-trf-artin-rees-principal-colength-difference: bounds Hilbert colength differences for a principal quotient of a domain; there is no regularity conclusion or canonical symmetric map.
lem-sfb-regular-local-graded-cotangent-criterion vs lem-trf-formal-monoid-ring-dimension: computes dimensions of completed monoid rings and their parameter hypersurfaces, under completeness and regularity hypotheses; it gives no converse criterion for arbitrary local rings.
lem-sfb-regular-local-graded-cotangent-criterion vs lem-trf-hilbert-samuel-growth-dimension: identifies the degree of the eventual length polynomial with Krull dimension. It does not assert that regularity is equivalent to canonical symmetric multiplication being an isomorphism.
lem-sfb-regular-local-graded-cotangent-criterion vs lem-trf-monomial-boundary-localizations: proves that certain localizations at monomial boundary primes are DVRs and computes valuations; it does not supply the general tangent-cone criterion.
lem-sfb-regular-local-graded-cotangent-criterion vs lem-trf-parameter-ideal-colength-bound: gives surjections and upper bounds for powers of an ideal of definition, not isomorphisms characterizing regularity.
lem-sfb-regular-local-graded-cotangent-criterion vs lem-trf-prime-chain-bound-from-colength-polynomials: deduces a prime-chain upper bound from supplied colength polynomial data; no symmetric-cotangent map or equivalence with regularity is stated.

The DAG was searched by regular local, cotangent, associated graded, symmetric, the source tags 00NO/00KQ, and Milne 13.2. blueprint_refs.py searches for regular local, symmetric algebra, cotangent, parameter, regular-graded and 13.2 found no equivalent blueprint statement. The item itself was also searched before writing this new node. The new criterion is not a clause of the item: it has no ambient regular ring, ideal J, s, or approximating tuples. The jet comparison is proved in the item's own steps, not moved into a replacement lemma.

## Review by Q107

I read Milne Algebraic Groups 13.2 and the full proof of Lemma 13.3, printed pp.254--255, in the local PDF. For the new node I read 13.2(a), the statement of Stacks Tag 00NO (algebra.tex, lemma-regular-graded), its canonical polynomial evaluation proof, and Tag 00KQ (proposition-dimension). Milne supplies the two directions of the symmetric-cotangent criterion; the Stacks places supply the regular associated-graded statement and dimension support. The new node is statement-only, with every ring, residue field, graded component, symmetric power and multiplication map introduced. Its meaning does not depend on a tag.

Step 1 uses the full explicit statements of quotient-local-structure and surjective-image-noetherian to make B nonzero Noetherian local. J is proper because it is contained in the maximal ideal. The new graded criterion applies to regular A, giving dim A=d; it does not assume the desired regularity of B. The maximal ideal is finite by the definition of a Noetherian ring, so the existing nakayama-local-generators statement applies with M=m, and M/mM=m/m^2. The given basis spans, hence the d lifts generate m. The existing regular-local-generators-regular-sequence statement explicitly includes the clause that every initial c-element quotient is regular local of dimension d-c; applying it with c=s gives C_n. I read all five cited statements rather than borrowing their proofs. Supporting source passages 00DV (lemma-NAK), 00NQ (lemma-regular-ring-CM), 00FN (lemma-Noetherian-permanence) and the local-ring quotient definitions were also checked.

Step 2 is the elementary quotient-module comparison in Milne's proof. I checked both numerator and denominator: equality modulo m^(n+1) implies equality modulo m^2 since n>=1, and adding m^n gives the common degree-n numerator. Restricting the quotient map to m^q has exactly the kernel written in the step. This identifies the actual graded pieces, not the larger rings A/J and A/I_n. The residue maps are the identity on A/m. This argument is fully written and needs no additional lemma node.

Step 3 invokes exactly the canonical maps and both directions of the new criterion. Equality of the two multiplication maps is checked on every spanning product; it is not inferred from an arbitrary isomorphism of vector spaces. The inverse symmetric-power comparison sends products by the inverse degree-one map. C_n is regular by Step 1, so its canonical map is an isomorphism. This proves the corresponding map for B in the single degree n. Universal quantification over n is legitimate even though C_n varies. The new criterion then gives regularity of B, and its dimension clause together with the n=1 cotangent basis quotient gives dim B=d-s. The entire argument, including this comparison, remains in the item.

Edge cases: d=0 forces m=0 and J=0, so the quotient is the field A. For s=0 the comparison ideals are zero, giving all the same positive graded pieces as A; the argument still works. For s=d the quotient cotangent space is zero, and the criterion gives a regular local ring of dimension zero. In dimension one, a nonregular quotient A/(t^2) fails the hypothesis already at n=2: its ideal modulo (t^3) is neither zero nor an ideal generated by a parameter. For the new criterion a field has zero positive pieces on both sides; k[t]/(t^2) fails the degree-two isomorphism. No excellence, coefficient-field section, characteristic condition, completion, or compatibility of approximants is used.

Mathlib searches were actually run through msearch.py for both nodes, including alternate natural-language phrasings, Loogle, and source grep. I read the returned types. IsRegularLocalRing.iff_finrank_cotangentSpace only characterizes regularity by dimension; it does not provide the symmetric-power associated-graded criterion. Regular-sequence hits and cotangent generation hits do not state either item. A grep with the nonexistent narrow AssociatedGraded directory was uninformative and was replaced by a RingTheory-wide grep; it is retained in the raw search log but not used as evidence. All new-node search records preserve the exact tool and query of their logged invocation.

I checked B1--B10: statement-only new node, self-contained hypotheses and notions, source places and tags read, TeX escaped once, honest searches, no false leaf or attachment, and inherited blueprint provenance. I checked C1--C8: every non-elementary input has a node whose statement was opened, each quote is literal, no cycle was introduced, existing generic off-unit tools are declared in split_report.tool_uses. I checked D1--D5: the item carries the finite-jet argument, and the sole new node is the distinct general criterion. I checked E1--E7 against the source and edge cases above; no omitted hypothesis, wrong quotient or unproved transport remains. No long step hides an extracted lemma. No SGA source was used.

## Unfinished work

Only the new general criterion remains unsplit, as required for a one-level split. Nothing in the assigned item is left unfinished. The required deliver.py --no-push finished successfully: OK (not pushed), commit 57a83f5ddd6, preflight passed (including the server DAG and split checks). The initial duplicate gate was repaired by reading all eleven additional nodes sharing 00KQ and recording the statement distinctions above. The direct push is the next authorized step.
