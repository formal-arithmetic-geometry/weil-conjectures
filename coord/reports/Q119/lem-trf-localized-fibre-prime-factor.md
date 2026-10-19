# Q119: lem-trf-localized-fibre-prime-factor

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-localized-fibre-prime-factor.json`: statement, split; retained the imported statement, source, blueprint ancestry, creation record and previous Mathlib searches. Eight proof steps; no new nodes and no new Mathlib leaves.
- `citations.json`: one entry for each step/use pair, quoting the actual cited statement verbatim.
- `report.md`: this report. `searches.jsonl` was produced by the authorized search command.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint tag, the item id, localized fibre/fiber, irreducible factors and prime ideals, including the RingTheory and Mathlib/RingTheory directories. No project declaration states the item. The item has no attached slopmaster2 declaration. The upstream master checkout is reference material, not evidence of a finished proof; no attachment is inferred from it.

## WANTED

None. The item source is available in `literature/stacks-project/algebra.tex`.

## Findings and route

I read the chapter and unit records, the requirements at the three blueprint levels in SETUP.md, the current main-20261015 proof of `lem-trf-local-term-locality`, and the item's inherited blueprint ancestry. The item is an algebraic input deep below the etale-refinement chain in that ancestor's contracting-correspondence proof. Its immediate parent `lem-trf-standard-etale-finite-free-prime-lifts` uses exactly its polynomial membership test; no replacement of the unit route is involved. The item's current source is Stacks Tag 00UF, `lemma-standard-etale-finite-flat-Zariski`, algebra.tex lines 40070–40133. I read the entire proof, especially the paragraph beginning “Let overline f denote the image of f” and its assertion that q is an irreducible factor avoiding g.

The statement is true as written. It needs neither etaleness nor a derivative condition: the fibre-polynomial argument only uses monicity and the existence of q. No statement or statement dependency changed. The source's brief factor assertion did not itself supply the explicit localization-membership formula, normalized uniqueness, or the justification that equality after contraction determines the fibre ideal when R -> k is not surjective. Those details are now written out. This is marked `proof_origin.by = agent` because it expands those omitted arguments, following the 00UF identification rather than pretending the expanded proof is printed there.

Before introducing any new lemma I searched all DAG statements and the whole blueprint. `blueprint_refs.py search` was run for localized fibre prime factor, irreducible factor f_1, 00UF, polynomial field principal, and irreducible factor. The only irreducible-factor blueprint hit was the unrelated representation-theoretic `def-rp-weight-blocks`. The existing `lem-pur-polynomial-field-pid` supplies exactly the only substantive ideal-structure theorem needed. The existing coprimality and Euclid leaves supply saturation for a competing factor. Consequently no new node is justified; residue evaluation, normalization, kernel identification and denominator clearing are explicit elementary steps from those cited statements and definitions.

I ran and read the Mathlib searches logged by msearch.py. Queries cover both the whole arbitrary-ring correspondence and the more general nonzero prime-ideal generator question. Loogle's two hits lift coprime factorizations or descend irreducibility; they do not classify primes. LeanFinder/LeanSearch returned Kummer–Dedekind and Dedekind localization results with stronger hypotheses. I read KummerDedekind.lean around 160–179 and DedekindDomain/PID.lean around 175–193, together with their ambient hypotheses; neither specializes to arbitrary R. I also read the fibre-spectrum equivalence in LocalRing/ResidueField/Fiber.lean around 150–179; it is infrastructure and still needs the polynomial argument. Polynomial.exists_monic_span (Ideal/MonicSpan.lean:27) is a component result, already covered by the existing PID leaf. All query text and actual summaries are retained in mathlib_searches; the inherited Q77 records are preserved.

## Not duplicates

No new nodes. In particular no second PID theorem, prime/fibre correspondence, localization-membership lemma, or restatement of a clause of the item was created.

## Review by Q119

I checked this split against delivery-errors B–E with the source and every cited statement open. For the item I read Tag 00UF and its complete local proof; there are no new nodes whose independent sources need auditing. I read the complete statements of all six cited existing nodes, rather than relying on titles or proofs. Each of them is a Mathlib leaf, and their literal statements are quoted in citations.json.

Step 1 uses `def-weil-pbc-localization-at-prime` for the local fraction model and residue quotient, not as an unquoted theorem about the kernel. The kernel equality is proved there using common denominators and the primality of q. Its assumptions are exactly that B is a commutative ring and q is prime; no finite type or reducedness is used.

Step 2 uses that same fraction model to construct the coefficient field injection explicitly. Since the composite R -> L kills precisely p, denominators outside p have nonzero images, so the formula factors through k and is injective. `def-weil-polynomial-ring` gives the coefficient operations used to define evaluation, and `def-weil-ring-localization-away` explicitly says the image of g is invertible. This proves f_k belongs to the kernel and g_k does not. Monicity guarantees f_k is nonzero over the nonzero field k. I did not cite a general definition node as if it stated a residue-field functoriality theorem: the formula and its check are in the step.

Step 3 invokes exactly the statement of `lem-pur-polynomial-field-pid`: every ideal of k[t] is principal and k[t] is a domain. The field hypothesis has been checked in Steps 1–2. The generator is nonzero because the ideal contains the nonzero f_k, and is not a unit because evaluation sends 1 to 1.

Step 4 normalizes that generator by its nonzero leading coefficient using the explicit polynomial definition. Irreducibility is not assumed from a definition: the step proves it by primality and cancellation in the domain obtained in Step 3. This also proves both divisibility clauses without adding separability or squarefreeness.

Step 5 uses precisely the fraction formula of `def-weil-ring-localization-away`. The evaluated denominator is nonzero from Step 2; membership in q is exactly the zero-residue criterion proved in Step 1. Thus it obtains every numerator and every exponent in the statement, not just polynomial classes before localization.

Step 6 proves, on every fraction, that the kernel of F -> L is the extension of the image of (h). Both inclusions are explicit: h is killed, and a zero fraction has numerator hV. The quotient relation is allowed because f_k is killed, and the localization relation is allowed because g_k evaluates nonzero. This is the actual ideal appearing in the statement. Equality after pulling back along j follows from the displayed equality of maps, not from an unspecified base-change identification.

Step 7 checks uniqueness for a factor satisfying only the three advertised conditions, without assuming it already has the membership clause. The common-divisor characterization and Bezout equivalence are actually present in `def-weil-coprime-polynomials`; irreducibility and h' not dividing g_k verify their hypotheses. `lem-weil-coprime-divides-product` says exactly that a coprime factor dividing a product divides the remaining factor, so it legitimately removes every power of g_k. The localization ideal-membership calculation is proved from the fraction equality, with the f_k error term retained until h' divides it. This repairs the potential gap between a fibre ideal and its contraction.

Step 8 checks the finite common coefficient denominator explicitly, using precisely the residue-field fraction model and finite support in the two cited definitions. The product s stays outside p by primality, so its image is a unit. Consequently the contraction equality tests every polynomial of k[t], although R -> k need not be surjective. Mutual divisibility plus cancellation gives inverse polynomial factors, and the explicit top-coefficient calculation makes those factors constants; monicity then forces equality.

I tested f=1 (B=0, so no q), g=0 or g_A nilpotent (again no q), constant-unit g, positive characteristic, repeated factors such as f=t^2 and h=t, nonreduced R, non-Noetherian R, and nonmaximal p with nonsurjective R -> kappa(p). No squarefree, injective coefficient map, algebraic closure, or finite residue extension was silently used. The empty polynomial support uses s=1. All proof steps are below 2000 characters, and none conceals a standard comparison theorem: the maps, kernels, fractions and coefficient lifting are displayed. The only non-elementary ideal theorem is cited at Step 3; the coprimality equivalence and Euclid statement are explicitly cited where needed. No new statements, cycle, off-unit proof route, SGA source, Lean edit, compiler, or build is involved.

## Unfinished work

None in the split. The required delivery dry run and push are performed after this report is written; their process output is the delivery evidence.
