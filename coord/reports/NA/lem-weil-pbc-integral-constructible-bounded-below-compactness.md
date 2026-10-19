# Worker report: lem-weil-pbc-integral-constructible-bounded-below-compactness

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-integral-constructible-bounded-below-compactness.json`: existing item split marked `split`; no new nodes.
- `citations.json`: 42 verbatim step-to-node statement quotes.
- `searches.jsonl`: required LeanSearch, Loogle, LeanFinder, and Mathlib grep searches (including second phrasings).

## Attachments

None. I searched the reference source under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and found no declaration tagged `(blueprint: lem-weil-pbc-integral-constructible-bounded-below-compactness)` and no declaration stating this item. The imported `lean` metadata is a new-target binding, not a finished source declaration.

## WANTED

None. The cited Bhatt--Scholze PDF and all cited DAG statements are present locally.

## What I checked and corrected

The statement and nine proof steps were read against Bhatt--Scholze, *Pro-étale topology*, Lemma 6.8.12, Proposition 6.8.11(3), and the local argument of Lemma 6.3.14. The coefficient ring remains the completed integral ring sheaf `A_T`; no rational coefficient or constant-ring identification is introduced. The common lower bound is an arbitrary integer, and the conclusion is the canonical global derived-Hom map in `D(A)`. The blueprint ancestry is `thm-weil-pbc-finite-extension`, at its first sentence (“Choose an integral lattice for K”), through the integral realization node; no alternate blueprint node states this item.

## Review by NA

I reread the item source and every statement cited by every step. Step 1 uses the Grothendieck module-category statement to obtain bounded-below representatives, the standard t-structure definition for the common lower bound, the derived-coproduct theorem for termwise sums, the affine weakly contractible hypercover and its totalization theorem, and evaluation-colimits on weakly contractible affines. These statements together justify the finite interchange of the family sum with the total-complex sums; the finite range is `N ≤ q ≤ r` in total degree `r`. Step 2 uses the bounded-below injective-resolution, internal-Hom, localized K-injective, exact restriction, weakly-etale site-equivalence, affine evaluation, global-Hom, and localized-ringed-site statements exactly for the uniform bound `N-b` and for transport to every slice. I checked that the localization citation supplies a canonical equivalence preserving covers, rather than an unjustified equality of chosen sites, and that the ring sheaf is transported by inverse image.

Step 3 uses affine evaluation and hypercover descent to test the cone, exact internal-Hom restriction and sheaf-colimit preservation to identify restrictions of the comparison, and the qcqs finite-family geometry statement for the covering fibre products. Step 4 uses exact internal-Hom, derived coproducts in a Grothendieck category, and the internal-Hom definition to establish closure under shifts, finite sums, summands, and triangles and then build finite-projective complexes by stupid truncations. Step 5 uses the open-closed adjunction/exactness statement, sheaf-colimit preservation, qcqs stability, the internal-Hom definition, K-injective derived adjunction, and global-Hom identification; I verified that restriction preserves both the lower bound and coproducts on every qcqs slice.

Step 6 uses the ind-etale basis and affine closed-site lifting statements to lift a finite trivializing cover from the closed stratum to ambient pro-etale objects. The pro-etale operations statement supplies the pointwise closed-pushforward formula, and the open-closed statement supplies exactness and the localization triangle; qcqs finite-family geometry verifies the lifted objects and complements. Step 7 applies the existing integral stratified-perfect characterization under precisely the finite extension, noetherian finite-dimensional base, and invertibility-of-`ell` hypotheses. The constructible-stratification statement supplies the finite strata, the reduced-induced-closed-subscheme statement supplies the reduced filtration, pro-etale operations supplies exact inverse-image transport, and the Noetherian-open statement supplies quasi-compact complements. I checked the membership-pattern filtration and the empty-complement endpoint on the empty and one-stratum cases. Step 8 uses only the open-closed localization and pro-etale operations statements: the adjunction calculation identifies the first vertex, inverse-image restrictions compose, and descending through the finite filtration gives `K` in `C_T`. Step 9 is the final specialization to `W=T`; it is elementary once the definition of `C_T` and the preceding steps are in place, including the empty-family case and A-linearity.

The long steps (2, 6, 7, and 8) were inspected for hidden independent lemmas. Each is one continuous local or finite-filtration argument whose non-elementary inputs are explicitly cited above; no additional lemma node is needed. There are no new nodes to review for duplicates or Mathlib status. I checked the small edge cases (empty family, empty final open, one stratum, and zero complex) and found no statement error. The recorded Mathlib searches returned only generic derived-category or constructible-topology infrastructure, so the item is not a Mathlib leaf.

No source or statement correction was required, and no unfinished part remains.
