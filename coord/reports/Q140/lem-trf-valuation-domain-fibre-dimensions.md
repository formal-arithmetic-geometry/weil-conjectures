# Worker report: Q140

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-valuation-domain-fibre-dimensions.json`: statement node, split into eight steps; statement retained; Mathlib searches found no match.
- `dag/nodes/sec-trace-formula/lem-trf-quasi-finite-polynomial-kernel-dimension-drop.json`: one new statement-only node, status `unsplit`; Mathlib searches found no match.
- `citations.json`: 23 verbatim statement quotations, one for each cited node in each proof step.
- `searches.jsonl`: actual search-command records, retained with the delivery.

There is one new node and no new Mathlib leaf. The valuation coefficient-normalization argument is elementary and is written out in step 6, not made a separate node.

## Attachments

None. Searches of the project declarations in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item ID, blueprint tag, valuation domains and fibre dimensions found no declaration stating every clause. Searches of the read-only upstream master did not supply a completed proof either. Related DVR and relative-component declarations are not attachments to this statement.

## WANTED

None. The statement and full proof of Stacks Algebra Tag 00QK are available in `literature/stacks-project/algebra.tex`.

## Findings and changes

The item agrees with Tag 00QK, including the hypotheses that the valuation ring embeds in the finite type domain and that the special fibre is nonzero, and including equidimensionality. No statement correction or coefficient-category change is needed. The imported proof was empty. I expanded the source argument into finite generic dimension, the semicontinuity inequality, a quasi-finite polynomial chart, scalar extension of that chart, a generic polynomial relation, explicit coefficient normalization, the residue-relation contradiction, and the component conclusion.

The one auxiliary lemma is the general strict dimension estimate for a quasi-finite map from a polynomial algebra with nonzero kernel. It is the field-algebra inference used in the last sentence of the proof of 00QK. It does not mention valuation rings, compare fibres, or assert any clause of the item. It is left statement-only, as required for a newly created node. The finite coefficient-divisibility induction and tensor reassociation are instead spelled out directly.

I searched the whole DAG by 00QK, polynomial kernel, quasi-finiteness and dimension terminology, and used `tools/blueprint_refs.py search` for the same concepts. I inspected the existing 00QG non-strict dimension bound and the 00QF-related dimension tools: none states the strict kernel bound. The new node's blueprint ancestor and complete `via` chain are inherited through the item. The item's pre-existing ancestry describes a semistable/nearby-cycle subchain. The current `main-20261015` ancestor proof of `lem-trf-local-term-locality` instead quotes Varshavsky's contracting-correspondence theorem and normal-cone specialization; it does not spell out that inherited subchain. I have recorded that ancestry discrepancy here and have confined this delivery to the assigned algebraic lemma and its existing source, without changing the ancestor or substituting a new proof of the unit.

Mathlib searches for the item and helper were run with `msearch.py`, using LeanFinder, Loogle, grep and LeanSearch, including a second semantic phrasing. The signatures returned concern DVRs, polynomial dimension formulas, one-variable quasi-finiteness, weak quasi-finiteness under quotients, power-basis vector-space dimensions, and scheme affine charts. None gives the item or the helper, nor a one-line specialization of either. Queries and results are preserved in the node records. An earlier dry run detected that helper searches had been logged under the helper ID rather than under the assigned delivery item; the required searches were subsequently run under the assigned item and their actual results read and recorded. The final delivery uses those records.

## Unfinished work

The new auxiliary node remains unsplit for the queue. No Lean code was written and no compiler, Lake, or library build was run. No external literature is missing.

## Review by Q140

I checked delivery-errors sections B through E against the source and the actual node statements, especially the requirement that every non-elementary inference has a dependency and that the dependency states the claimed fact. I read the item and its chapter/unit records, the current blueprint ancestor proof, Stacks Algebra Tag 00QK's statement and complete proof, and each of the statements cited below. `citations.json` copies the statements verbatim rather than paraphrasing a stronger assertion. Every step is shorter than 2000 characters.

1. `lem-weil-pbc-generic-fibre-localization-domain-irreducible` states the required localization/domain identification. The generator expansion using `def-weil-pbc-finite-type-algebra` verifies finite type for both tensor fibres. `lem-weil-pbc-finite-type-domain-dimension-trdeg` applies to the nonzero finite type domain over the field K and supplies the finite integer d and its transcendence-degree description. `lem-weil-pbc-dimension-at-point-components` and `lem-weil-pbc-spec-topological-krull-dimension-ring` identify every local topological dimension of this irreducible generic fibre with d. I checked that this is topological dimension at a point, not the dimension of the local ring.

2. `lem-weil-pbc-fibre-ring-primes-bijection` gives exactly a prime of D over the residue-field prime. The component formula makes n a finite nonnegative integer. `lem-weil-pbc-fibre-dimension-bounded-open-upstairs` assumes finite type, which holds, and gives an open containing the selected prime with local fibre dimensions at most n. The proof writes out why the domain's generic prime belongs to that nonempty open, and why its fibre point is the generic point of the generic fibre. Step 1 then gives d <= n. No irreducibility assumption on the special fibre is made.

3. `lem-weil-pbc-quasi-finite-over-polynomial-algebra` has exactly the local fibre-dimension hypothesis established in step 2 and supplies g and the n-variable chart. The fact that g avoids the chosen prime implies g is nonzero, so the localization remains a domain containing A. I expanded the two inverse tensor-balancing maps before applying `lem-weil-pbc-localization-base-change`; this avoids assuming that the cited localization lemma itself states an unrelated tensor associativity theorem. `lem-weil-pbc-spec-localization-away-basic-open` gives the open containing Q, and `lem-weil-pbc-dimension-at-point-open-subspace` preserves its local dimension n. This also checks that the localized special fibre is not the zero ring.

4. `lem-weil-pbc-polynomial-scalar-extension` gives the two polynomial source rings. `lem-weil-pbc-quasi-finite-four-rings` explicitly requires every element of the bottom-right ring to be a finite sum of products from the other two rings. The displayed pure-tensor expansion verifies that hypothesis for both field fibres, so the dependency really supplies both finite type and quasi-finiteness. The finite generating set for the field algebras is also written out.

5. Using `def-kun-transcendence-degree`, injectivity of the generic polynomial map would give n algebraically independent elements in L, contradicting d < n. The fraction field of F localized at a nonzero g is still L by the explicit fraction argument. This step invokes no unquoted dimension-preservation theorem for open subsets.

6. The elementary finite induction uses only the defining valuation dichotomy applied to nonzero ratios of coefficients. It works for valuation rings of arbitrary rank: no discrete value group and no minimum in an infinite set is assumed. Dividing by the selected nonzero coefficient yields a coefficient equal to 1. Injectivity of localization of the domain B then transports the relation back from H to B, with cancellation written out. This is a proof step, not a new auxiliary node.

7. Reduction preserves the coefficient 1, giving the nonzero kernel required by `lem-trf-quasi-finite-polynomial-kernel-dimension-drop`. All its field, finite type and quasi-finite hypotheses were established in step 4. The only additional comparison is local dimension <= global dimension, which follows directly by taking the whole space as an open neighbourhood in `def-kun-topological-dimension-at-point`. Thus the strict bound contradicts the local dimension n in step 3.

8. `lem-weil-pbc-dimension-supremum-local-dimensions` applies to the constant local dimension. `def-weil-pbc-krull-dimension-ring` explicitly states that having no primes is equivalent to the zero ring, so the nonzero special fibre makes that supremum nonempty. The spectrum/ring comparison yields the claimed ring dimension equality. `lem-weil-pbc-spec-irreducible-components-minimal-primes` states that components are V(p) for minimal primes. The inclusion argument proving uniqueness of the component through p is written out, and the component/local-dimension formula then gives every component dimension d. This proves equidimensionality without presupposing it.

For the new helper, I read the last strict-dimension inference in 00QK and checked that its generalized statement is true for reducible targets as well: a nonzero relation forces each component image into a proper hypersurface of affine n-space, and quasi-finiteness prevents a larger component dimension. This is a genuine dimension theorem, not coefficient arithmetic or a restatement of the item, and is left for its own future split. Its zero-ring case is included explicitly.

I tested the item with A a field (the two fibres coincide), with a DVR family A[x,y]/(xy-pi) (the two special-fibre components have the same generic dimension), and with A[1/pi] (the special fibre is zero and the stated hypothesis excludes it). The coefficient argument was tested with one nonzero coefficient and higher-rank valuation rings. For the helper, n=0 and T=0 give -infinity < 0; n=0 and T nonzero admit no nonzero kernel from the field. The examples k[x,y]/(xy) and k[x]/(x) give dimensions 1 < 2 and 0 < 1. The identity polynomial map has dimension n and no kernel, confirming why the nonzero-kernel hypothesis is essential. No SGA source is used.

## Not duplicates

lem-trf-quasi-finite-polynomial-kernel-dimension-drop vs lem-trf-valuation-domain-fibre-dimensions: both cite 00QK, but the former is a strict dimension bound for a single quasi-finite field-algebra map with nonzero polynomial kernel; the latter compares two fibres over a valuation ring and proves equidimensionality. Neither statement is a clause or specialization of the other.

lem-trf-quasi-finite-polynomial-kernel-dimension-drop vs lem-weil-pbc-dimension-quasi-finite-over-polynomial-algebra: the existing 00QG statement gives dimension <= n with no kernel hypothesis; the new statement requires a nonzero kernel and concludes dimension < n, which does not follow by specialization of the non-strict inequality.
