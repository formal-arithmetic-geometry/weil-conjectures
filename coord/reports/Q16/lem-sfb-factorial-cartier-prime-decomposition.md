# Q16 stage-1 delivery: lem-sfb-factorial-cartier-prime-decomposition

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-factorial-cartier-prime-decomposition.json`: statement, split into eight proof steps; scheme statement has no Mathlib match.
- No new nodes and no Mathlib leaves are introduced.
- `citations.json` records a verbatim statement quote for every citation in every step. `searches.jsonl` holds the actual five additional Mathlib searches; the item's earlier Q40 search records are retained unchanged.

## Attachments

None. Searches of `lean/WeilConjectures/` by the exact blueprint id, factorial, Cartier decomposition, and prime-component concepts found no declaration with every clause. I read the related divisor files, in particular `Divisor/Image.lean` and `Mathlib/RingTheory/UniqueFactorizationDomain/Ideal.lean`: their principal-radical and local-principality results do not state finite component ideal factorization with generic dimensions. They are not attachments.

## WANTED

None. The Stacks sources are available locally.

## Findings and corrections

The statement is unchanged and true. Its source is Stacks 0BCP, `lemma-effective-Cartier-divisor-is-a-sum`, together with 0BCN(2), `lemma-effective-Cartier-codimension-1`. I read their statements and proofs in `divisors.tex`, and the supporting 0AGA (`lemma-weil-divisor-is-cartier-UFD`), 0AGB (`lemma-codim-1-part`), and 0AG8 (`lemma-effective-Cartier-in-points`). The proof uses exactly the item's UFD-stalk hypothesis, writing out its finite prime-factor arithmetic; it does not assume that an arbitrary affine chart is itself a domain or a UFD. It also avoids assuming the divisor itself is reduced. The proof is marked agent-written because this is an explicit UFD specialization of the source's valuation/divisorial-part argument, rather than a verbatim assembly through its general codimension-two result.

The sandbox held only dispatch markers at resumption, with no node, report, search log or delivery receipt. There was no active Q16 delivery process for this item. I copied the live unsplit item and retained its full statement, initial searches, source, creation stamp, and blueprint ancestry. No repair note exists for this item. `blueprint_refs.py ancestor` returns None, matching the inherited null `from.node`; its detailed place and via list are retained. Whole-blueprint searches for Cartier and factorial, and the DAG statement/source searches, found no equivalent general statement. The nearby curve decomposition assumes a smooth curve; the regular-prime-divisor lemma assumes a regular integral ambient scheme. Neither covers the item. Existing component/stalk calculus and stalk-Cartier spreading do cover the non-elementary tools needed, so no new nodes are justified.

The five fresh searches were run with the required msearch command: LeanFinder with two formulations, LeanSearch, Loogle for Cartier, and the AlgebraicGeometry Cartier grep. All services returned successfully. The semantic hits concern ideals and fractional ideals of Dedekind domains; I checked `Mathlib/RingTheory/DedekindDomain/Factorization.lean` (ambient hypothesis at lines 66-68 and the ideal factorization theorem at 196-198). A scheme whose local rings are factorial need not have dimension one, and these hits do not supply the stated sheaf decomposition. Both Cartier name searches returned no hits.

## Unfinished work

None in this stage-1 split. No Lean was written or compiled.

## Not duplicates

No new node is created. The existing `lem-sfb-closed-component-stalk-calculus` supplies reduced components and their minimal-prime correspondence; `lem-sfb-stalk-nonzerodivisor-cartier-spreading` supplies the stalk-to-neighbourhood Cartier criterion. I cite them instead of creating new versions. `lem-per-regular-prime-divisor-local-equations` requires regularity and ambient integrality, neither of which is assumed here. `lem-sfb-single-cartier-divisorial-part` has a single already-Cartier support and is not the required decomposition; the proof here does not cite it or the parent divisor-extension node.

## Review by Q16

I checked the unchanged item against the four source proofs named above. No source error or statement dispute was found. No new node needs a source or independent edge-case audit. The chapter and unit records and the current blueprint direct-image proof were read; this is a divisor-extension prerequisite below the unit, and changes no higher proof route. The null imported ancestor is a pre-existing metadata condition, not a newly fabricated blueprint reference.

Step 1 uses the reduced induced structure theorem for existence, reducedness and support, the closed-component-stalk theorem for finite distinct integral components and their ideal correspondence, and scheme sobriety for the generic points. All three assertions occur in those nodes' statements. Their hypotheses hold because W is Noetherian and H is reduced by construction. The distinctness and integrality are not inferred from possibly nonreduced E.

Step 2 reads the effective-Cartier definition for a regular equation in the actual stalk, the affine radical description of the reduced structure, and the component theorem's ideal-stalk formula. I wrote out the radical/localization calculation with a denominator t: this works even if the affine coordinate ring has zero divisors. The nonzero equation is required only after passing to the UFD stalk A.

Step 3 uses precisely the component theorem's bijection from components through x to minimal primes over the reduced ideal, including its unit-ideal assertion for absent components. The prime-factor and minimal-prime calculation is explicit from the hypothesis of unique factorization; it does not cite the definition of flatness or a codimension lemma in place of a theorem. Distinct nonassociated prime generators are incomparable, and every prime over the finite product contains one of them. This gives each actual component ideal, not merely its support.

Step 4 applies the scheme clause of the spreading theorem. I verified local Noetherianity and the nonzerodivisor generators at all points, including 1 outside a component. The effective-Cartier definition then supplies the requested terminology. No regularity or globally factorial affine ring is used.

Step 5 uses scheme sobriety to exclude a proper generalization in the divisor and the canonical Spec-of-stalk theorem to identify all generalizations, with their local rings. At a component generic point there is exactly one reduced component, so the maximal ideal is generated by a prime factor. The written UFD calculation excludes every nonzero prime below it. The dimension definition therefore gives exactly one, rather than only an upper bound. The empty scheme has no such point, so the argument never assumes a nonexistent nonzero local ring there.

Step 6 defines the positive exponents by the assumed unique prime factorization at each generic stalk. Changing a nonzero principal generator multiplies it by a unit; the cancellation argument is included. No unproved choice of a valuation or uniformizer is being used.

Step 7 uses the canonical-morphism theorem's local-ring isomorphism, scheme sobriety for identification of the component generic point, and the tilde-stalk fraction formula for the localized ideals. The formulas identify the actual equation and component ideal under the same map. Every other prime factor is outside the chosen prime and becomes a unit. The remaining prime stays prime and nonunit because its localized quotient is a nonzero localization of a domain. Hence uniqueness of factorization identifies the exponent with a_i. This explicitly checks the compatibility that an unsupported word such as 'transport' would hide.

Step 8 uses the ideal-product definition and the germ/equal-on-a-neighbourhood description of stalks to justify products, powers, and equality of ideal subsheaves. The finite sums/products have common neighbourhood representatives. Membership of a section in the other ideal is local, so gluing gives both inclusions. The component theorem supplies the unit stalk ideal when E is empty. All these arguments are written in the step.

I checked the cases W empty, W the spectrum of a field, E empty, a nonreduced divisor V(x^2), intersecting components V(x^2 y^3) at the origin of the affine plane, a point lying on only one of those components, and a finite disjoint union of factorial schemes. In the plane example the two stalk exponents remain 2 and 3 at the generic points, so the proof retains scheme multiplicities. Domain and UFD assumptions are always applied to a local ring, and Noetherianity is used only for the finite component and spreading theorems. Every step is below 2000 characters. I also checked B–E for missing notions, citation mismatches, circularity, hidden hypotheses, duplicate nodes, and clause-restatement splits; the proof creates no new lemma and cites no node depending on this item.

The generic reduced-structure, Spec-of-stalk, and tilde-stalk facts are declared in `split_report.tool_uses` as general tools. Their statements provide geometric foundations without replacing a step of the six-functor unit. The other cited statements are definitions, Mathlib leaves, or same-unit tools.
