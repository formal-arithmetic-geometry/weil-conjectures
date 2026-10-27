# Worker report: lem-sfb-field-finite-type-over-subring-localization

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-field-finite-type-over-subring-localization.json: item, statement unchanged, split into four steps; no direct Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-type-domain-image-open.json: one new statement-only node, unsplit; no Mathlib match. Its statement is the domain/injective-map specialization of Stacks 00FH, not a field-localization statement.
- citations.json: seven entries, one per step/node citation, quoting the verbatim statements actually read.
- searches.jsonl: authentic command log; existing search records in the live item are retained and the searches actually run in this sandbox are appended to the relevant node records.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and field/finite-type/subring terminology. No declaration stating the whole item was found. GroupScheme/Basic.lean:670 gives an image-open consequence with IsLocallyNoetherian Y, so it cannot attach either this item or the new general-domain input. GenericIrreducibility.lean's Chevalley calculation also uses a Noetherian coefficient ring. No source declaration was treated as proved merely because it exists.

## WANTED

None: all sources used are present in literature/stacks-project/algebra.tex.

## What was wrong or incomplete

The original item was statement-only, with no proof. Its statement is correct, and no statement change or dispute is needed. The proof of 00FY explicitly uses the arbitrary-finite-type image theorem 00FH. The existing Chevalley node assumes local finite presentation, and the affine-constructible-open blueprint node assumes finite type over a field; neither is sufficient for the arbitrary subring in this item. I have not added Noetherianity, finite presentation, a base field, or a Jacobson assumption. This is the main hypothesis check in the split.

The newest blueprint direct-images proof was read at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, together with its _section.md, the chapter record and the inherited unit record. This deeply nested algebra input serves the retained 00FY supporting step below direct images; it changes no unit or chapter route. tools/blueprint_refs.py ancestor reports a null blueprint ancestor for the inherited chain; the item preserves that lineage and the child prepends the item to via, with its exact supporting 00FH place appended.

## Not duplicates

lem-sfb-finite-type-domain-image-open vs lem-weil-pbc-chevalley-constructible-image: the existing node requires a quasi-compact locally finitely presented scheme morphism and concludes constructibility; the new node assumes only an injective finite-type ring map of arbitrary domains and concludes a neighbourhood of the zero prime in its spectrum image. Finite type over a non-Noetherian domain need not be finite presentation, so that existing node does not specialize to this statement.

lem-sfb-finite-type-domain-image-open vs lem-wf-affine-constructible-open: the existing node concerns affine schemes of finite type over a field; R here is an arbitrary integral domain, with no such hypothesis.

lem-sfb-finite-type-domain-image-open vs lem-sfb-field-finite-type-over-subring-localization: the item requires a field target and concludes both existence of a field localization and finite-dimensionality of its field extension. The new node is a spectrum-image input for arbitrary domain targets, with no field-localization or extension-finiteness conclusion. The item's steps still construct the localization, prove it is a field, and prove finiteness.

lem-sfb-finite-type-domain-image-open vs lem-exc-j0-finite-type-domain-descent: the existing node assumes Noetherianity and a nonempty regular locus upstairs, and concludes a regular open downstairs; neither its conclusion nor its hypotheses are the required arbitrary-domain image theorem.

No existing DAG statement or blueprint match for Tag 00FH or its label was found. Searched the whole DAG by tag, image/open/domain terminology, and parsed statement searches, and ran blueprint_refs searches for 00FH, image of spectra, finite type domain and generic point. Searches for 00FY and finite type field likewise found no duplicate blueprint statement for the item. Reused the three existing proof-result nodes rather than creating principal-open, maximal-ideal or Zariski-lemma nodes.

## Review by NV

I read Algebra Tag 00FY (lemma-field-finite-type-over-domain), algebra.tex:6611-6627, in full. It first invokes 00FH, chooses a nonzero principal open consisting only of the generic point, observes the localized domain is a field, and applies 00FV. The four proof steps implement exactly this route.

For the new node I read Tag 00FH (lemma-characterize-image-finite-type), algebra.tex:5770-5816, including its proof. Take E to be the whole Spec S, which is constructible, and xi the zero prime of R. The zero prime of S contracts to xi because the map is injective. The closure of xi is all of Spec R. The theorem therefore gives an open dense subset contained in the image; every nonempty open of a domain spectrum contains its zero prime, as follows by taking a principal open and using that a nonzero element is not in the zero ideal. This verifies the exact neighbourhood clause in the new statement, without a Noetherian or presentation hypothesis. The source uses generic finite presentation 00FG and Chevalley internally: these are deliberately left inside the new statement-only lemma for its future split. This delivery does not pretend that finite type alone implies Chevalley constructibility.

Step 1 uses exactly the new node's statement that an open U containing (0) lies in the spectrum image. R is a nonzero domain since it is a unital subring of the nonzero field K; the map is injective and finite type by the item's hypotheses. A prime of a field contains no nonzero element, so its only prime is zero, and its contraction is zero. Thus the image is precisely the singleton used by the step.

Step 2 uses both clauses of lem-weil-pbc-spec-localization-away-basic-open: clause (i) supplies s with (0) in D(s) inside U, while clause (ii) gives Spec R_s homeomorphic to D(s). I read the complete node statement and Algebra 00E0 (lemma-Zariski-topology), including its basic-open basis clause, and 00E4 (lemma-standard-open), algebra.tex:3207-3220. These are valid for arbitrary rings. The cited def-weil-ring-localization-away states the fraction equivalence and operations; substituting into K respects the equivalence because s is nonzero there. Equality with zero in K forces a zero numerator. This proves injectivity, nontriviality and the domain property rather than assuming them. The unique prime in the localization is zero because its embedding in K makes zero a prime.

Step 3 cites the full statement of lem-weil-pbc-proper-ideal-contained-in-maximal, which supplies a maximal ideal above every proper ideal. I read its source 00E0 (lemma-Zariski-topology), item (2) and the quotient-ring argument. For a nonunit a, the ideal (a) is proper because 1=ba would give an inverse. The step explicitly proves that the maximal ideal is prime, so singleton prime spectrum forces that ideal to be zero, contradicting a nonzero member. This argument needs only maximal-ideal existence, not a separate hidden field criterion. def-weil-field says precisely nontrivial commutative ring with inverses for nonzero elements; Step 2 supplied nontriviality.

Step 4 cites the polynomial-generation equivalence in def-weil-pbc-finite-type-algebra: any finite R-generating list also generates over the intermediate subring R_s because all the same polynomial expressions remain available. It then cites lem-weil-pbc-zariski-lemma, whose complete statement is a field K finitely generated as algebra over a field k being finite-dimensional over k. Here k=R_s is a field by Step 3. I read that node and Algebra 00FV (theorem-nullstellensatz), first clause and its extension to finite type algebras. It gives the entire claimed finite-dimensionality, with no algebraic hypothesis assumed in advance.

I checked delivery-errors B-E: the one new node is self-contained, introduces both rings, defines domain inline, states the spectrum map, cites its notion nodes, and has no proof or proof dependencies; its source has the exact tag and TeX label. Every non-elementary result in the item is a cited node, and every citation was compared with its statement. citations.json quotes those statements verbatim. The short fraction, ideal and generator arguments are written out as parts of steps, not inflated into new nodes. No step exceeds 2000 characters; the whole assembly proof has 1648 characters. No SGA source is used. No repository or launcher file, Lean file or compiler was changed or invoked.

Small cases: R=K works with s=1 and extension degree one. For a DVR R inside its fraction field K, a uniformizer s gives R_s=K; this checks why the conclusion is only a principal neighbourhood rather than R itself being a field. Z inside Q does not satisfy finite type, and therefore is not a counterexample. For the new domain-image lemma, identity maps and polynomial extensions have the whole target spectrum as image, and localization inclusions R to R[1/t] for a nonzero t have image D(t); all satisfy the asserted zero-prime neighbourhood. Zero rings and maps with nonzero kernel are explicitly excluded in the new node. No finite-presentation inference was used.

## Unfinished work

Only the future split of the new statement-only node remains outside this item's one-level scope. The required remote dry run and push are recorded below when completed.
