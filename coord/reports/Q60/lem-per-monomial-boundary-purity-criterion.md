## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-monomial-boundary-purity-criterion.json`: statement, now split into six steps; no Mathlib match.
- No new nodes; no Mathlib leaves created.
- `citations.json`: one verbatim supporting statement excerpt per cited node in every step.

## Attachments

None. I searched the item id and its blueprint tag in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/`, and searched monomial, coordinate-divisor, Kummer and punctual-purity terminology. No project declaration states the item. The `IsPunctuallyPure` results under `Purity/RealSheaves/` concern Frobenius weights, not the closed-point Kummer purity property here.

## WANTED

None. The source PDF is present and was read.

## Audit of the input and route

The input statement is retained exactly. It correctly restricts boundary components to positive exponents and assumes regularity of V. ILO XVI Lemma 3.5.13(iv), printed p.251, is exactly this criterion; the proof identifies the H_i with affine spaces over the residue field, covers the special fibre by their supports, handles the generic fibre over a field, and invokes Proposition 3.2.3.

The original node had no proof. The source's phrase about a generic fibre smooth over an extension of the generic field is unnecessary here: the existing `lem-per-prime-field-punctual-purity` applies to every regular Noetherian scheme over a prime field, with no finite-type hypothesis. Applying it to the regular open D(pi) handles also purely inseparable exponent tuples in equal characteristic. This uses the same field-piece argument and does not invoke monomial purity itself, smooth ascent over a trait, trait-relative purity, or absolute purity above the item. I checked the dependency closures of the prime-field theorem and the two-of-three criterion: neither reaches this item, so this reuse is not circular.

The chapter and unit records were read (`sec-deligne-laumon-a1`, `sk-p-dl-a1-perverse`), together with the node's historical blueprint ancestry. No unit or chapter record changes. The split realizes the monomial-model boundary test within the recorded regular finite-coefficient duality input to the historical Step 3 of `lem-per-artin-gabber-affine-curve`. It uses no prohibited source route.

Mathlib queries were run only through the required `msearch.py` command and the generated `searches.jsonl` was read before copying records into the node. Two semantic phrasings, Loogle, grep and LeanSearch returned only ordinary scheme morphisms, etale-locus facts, Kummer field theory, polynomial facts and DVR facts. These signatures do not state an etale cohomological purity criterion. The first Loogle query had an unknown identifier; this failed query is explicitly recorded as unavailable, and a valid `"Kummer"` query followed it. Earlier inherited searches of Q36 are preserved, not attributed to Q60. Blueprint searches for monomial, punctual purity and coordinate divisor found no duplicate statement, and the existing general prime-field and regular-pair nodes were reused.

## Not duplicates

No new nodes were created. The item specializes neither semistable-coordinate-divisor purity nor monomial-trait punctual purity: those assert purity unconditionally for a particular model or for all models, while this item proves an equivalence of boundary and pointwise purity. No duplicate node was needed for either direction.

## Review by Q60

I read ILO XVI Lemma 3.5.13(iv) and its proof at printed p.251, Definitions 3.1.4 and 3.2.1--3.2.2, Proposition 3.2.3 and the field-scheme input Proposition 3.2.5. I compared the statement with the unchanged item and opened the statement of every cited DAG node. There are no new-node sources to check.

Step 1 uses the finite-type definition for the finitely generated quotient presentation, finite-type-over-Noetherian for V, open-subscheme Noetherianity for D(pi), and the local-ring characterization of regularity for restriction to this open. Each cited statement explicitly gives that property. R is Noetherian by hypothesis, and the finite presentation has finitely many variables. Invertibility of ell passes to the quotient and localization simply by mapping its inverse.

Step 2 writes actual inverse coefficient-and-variable homomorphisms for B/(T_i), using a_i>0. Thus H_i is affine (n-1)-space over k even when other exponents vanish. The finite-type definition and Noetherian ascent give its Noetherianity; the affine-space projection theorem gives its smoothness; the geometric-calculus statement says a scheme smooth over a regular scheme is regular. A field is regular directly from dimension and maximal ideal. The same geometric-calculus statement defines the codimension of a regular immersion as the length of a regular sequence, which gives one for the assumed effective Cartier divisor. None of this asks a definition node to supply a missing theorem. The resulting pair meets all hypotheses of the two-of-three criterion.

Step 3 uses only the statement of `lem-per-prime-field-punctual-purity`, which explicitly allows arbitrary regular Noetherian schemes over Q or F_p, without finite type or excellence. The field k and the generic field each contain such a prime field. I wrote out why R[1/pi] is a field using the dimension-one prime-chain condition, instead of assuming the generic smoothness hypothesis of the separate primitive-monomial geometry lemma. No regularity is inferred from a possibly inseparable generic presentation: it is the restriction of the assumed regularity of V. Pointwise purity at a point of the open is precisely purity at that point of V because the local schemes are identical.

Step 4 is elementary: primality applied to the finite monomial product gives the asserted set-theoretic cover. It does not replace the scheme-theoretic special fibre by a reduced divisor. The assumption that the exponent tuple is not identically zero ensures the boundary index set is nonempty. An exponent zero contributes the factor one and yields no required boundary condition.

Step 5 applies the (b),(c) implication of the two-of-three statement, whose conditions are quoted verbatim in citations.json. The ambient and closed schemes are regular Noetherian, ell is a unit, and codimension is one. Purity of H_i came from Step 3, and purity of V is exactly the forward hypothesis. The regular-immersion class-calculus statement identifies the codimension-one class with the supported Cartier Kummer class, including its sign. Thus it is the requested map that is invertible, not an unspecified equivalence of objects.

Step 6 applies (a),(b) of the same criterion in the other direction and obtains pointwise purity of V along each H_i. Combining this with the generic-open purity and the explicit cover proves the converse at every point. No exceptional inverse-image base-change assertion is added implicitly to this use: the criterion's own statement already supplies precisely the pointwise-to-pair comparison.

I checked B--E of delivery-errors: self-contained unchanged statement; no new nodes or new proof sketches hidden in statements; valid single TeX escapes; preserved provenance and existing searches; actual logged fresh queries; no circular dependency; every non-elementary input cited by its statement. All six steps are below 2000 characters, and the only purely elementary step is the finite-product prime-ideal calculation. The scalar/variable substitution in Step 2 and the field argument in Step 3 are written out rather than hidden in transport language. The cases n=1, exponent tuple (a,0,...,0), residue characteristic dividing a, ell dividing a, and arbitrary nonexcellent/nonhenselian traits use exactly the same proof. In particular no perfection, completion, finite type over the prime field, or invertible-exponent hypothesis was added. No correction to the input statement was necessary.

## Unfinished

None in the mathematical split. Required remote dry run and delivery follow this report.

## Generic tools for maintainer recording

The cross-unit statements used as generic tools are `lem-weil-pbc-finite-type-over-noetherian` and `lem-weil-pbc-noetherian-open-subscheme-noetherian` for Noetherianity, and `sbc-lem-affine-space-smooth` for the smoothness of the explicit affine spaces. No node of this unit supplies these general scheme facts; none replaces a step of the perverse-sheaf route. `def-weil-finite-type-morphism` is only a definition. The maintainer, rather than the worker, records any required `tool_uses`. I removed the inherited worker-written `split_report.tool_uses` during this continuation.

## Continuation review

The first resumed dry run exited with two too-short citation excerpts, both for finite-type-over-Noetherian. I expanded these to the whole current statement, including its finite-type and Noetherian-base hypotheses, and also expanded the finite-type definition excerpts. The mathematical proof and all logged searches were retained.
