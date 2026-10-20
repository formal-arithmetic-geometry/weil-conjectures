## Files written

- dag/nodes/sec-trace-formula/lem-trf-source-hyperext-module-target.json: statement item, seven-step split; no exact Mathlib match. Statement and original statement dependencies retained verbatim.
- citations.json: 16 verbatim statement quotations, covering every step/node citation.
- searches.jsonl: actual search-tool log; five new searches, including two distinct LeanFinder phrasings, Loogle, LeanSearch and Mathlib grep.

No new DAG nodes or Mathlib leaves were created. report.md and write_split.py are sandbox report/support files.

## Attachments

None. Searching lean/WeilConjectures for the blueprint tag and hyperExt/hyper-Ext variants found no declaration. The Mathlib hits concern Ext groups and injective-resolution comparisons; none states the spectral sequence and its finite abutment filtration.

## WANTED

None.

## Faults and corrections

The item was statement-only. Its statement is correct as written, including arbitrary commutative rings, no finite-generation assumption, the lower bound j >= -u, and the zero abutment when t < -u. No statement dispute or correction was necessary.

The split expands the module-target case of Stacks 0G20 by a first-quadrant Hom double complex. This avoids treating the source's omitted filtered-complex details as a proof. The source-versus-target hyper-Ext distinction matters: lem-per-bounded-above-rhom-hyperext varies the target cohomology and does not give this source-cohomology E2 page. It was read and deliberately not cited for the wrong assertion.

## Not duplicates

No new nodes, hence no new/existing-node pairs. Whole-DAG searches for 0G20, hyper-Ext, double-complex spectral sequences and injective resolutions led to the reused nodes. tools/blueprint_refs.py searches for spectral sequence, hyper-Ext and 0G20 found no blueprint node stating the item. The ancestor command confirms lem-trf-local-term-locality, whose precise existing from.place/via ancestry is retained. I read the chapter and sk-i-curve-zero unit and the current main-20261015 locality node; this is an algebraic tool beneath that route, not a replacement for its contracting-correspondence argument.

## Review by ND

I read Injectives remark-spectral-sequences-ext-variant (Tag 0G20) and the preceding remark-ext-from-filtered-complex (0G1Z) in injectives.tex. The former gives the source-cohomology E2 sequence and bounded convergence when the source is bounded above and the target bounded below. N[0] supplies precisely that target bound. I also read Homology section-double-complex (012X), lemma-ss-double-complex (0130), lemma-first-quadrant-ss (0132), and Derived Categories lemma-injective-resolutions-exist (013K) and lemma-bounded-below-injectives-K-injective (070J). No SGA source is used. Since the explicit signed Hom-double-complex realization and row calculation are my expansion, proof_origin.by is agent; it is not attributed as a verbatim proof from the blueprint or Stacks.

For step 1 I opened def-sbc-standard-tstructure-derived-category: its statement explicitly equates the cohomological upper bound with a representative having zero terms above u. The truncation inclusion argument is written in the step and needs no separate lemma.

For step 2 I opened lem-weil-pbc-ring-modules-enough-injectives and def-sp-injective-resolutions. The former really supplies an embedding of every module into an injective and abelianity of the module category; the latter really gives the extension property and meaning of a resolution. I did not cite the definition as an existence theorem. The recursive cokernel construction, differential and kernel/image equalities are explicit, giving I^r = 0 for r < 0 without any Noetherian assumption. This elementary construction is the proof of 013K(1), not an unsplit theorem moved into a new node.

For step 3 I opened lem-weil-pbc-bounded-below-injectives-kinjective: it is stated for an arbitrary abelian category and says the actual bounded-below injective complex is K-injective. This avoids using a theorem stated only for etale sheaves. def-pur-derived-internal-hom explicitly allows any K-injective representative of the second variable, and def-pur-hom-complex states the product formula and differential. The one-object identity-covering site is exactly modules and ordinary linear Hom, not the quasi-coherent derived category on an affine scheme.

For step 4 I checked the terms and commuting-differential/total conventions in def-sp-double-complex-total against the actual Hom differential in def-pur-hom-complex. I corrected the initially implicit total comparison by spelling out the coefficient (-1)^(i+b-u+1) = (-1)^(t+1). There is no hidden invocation of shift conventions: Tot degree t+u is identified with Hom degree t with the same differential. The possible source degrees in Hom degree t are -t <= a <= u, so the product is a finite sum even if M is unbounded below and I unbounded above.

For step 5 the only input is the injective extension property of def-sp-injective-resolutions. I checked both directions of the cohomology identification: extend from Z^a/B^a into M^a/B^a for surjectivity, and from B^(a+1) into M^(a+1) for the kernel to consist of boundaries. These two extensions are written explicitly; this is a few-line cycles/boundaries computation, not an uncited exactness-of-Hom assertion. The b=0 endpoint works because M^(u+1)=0. The maps commute with postcomposition, so the next differential is the actual differential of Hom(H^(u-b)K,I).

For step 6 I opened thm-sp-double-complex-spectral-sequences. Its first sequence really has E1 = vertical cohomology and E2 = horizontal cohomology, and its convergence assertion is for first-quadrant double complexes in any abelian category. Our coordinates are (i,b), so no interchange of the two filtrations is hidden. I opened lem-sc-rhom-cohomology-ext-ring: it is about arbitrary modules over any commutative ring and the derived-Hom cohomology/derived-category Ext comparison for all nonnegative integers, exactly the comparison needed after using def-pur-derived-internal-hom. I also read the Mathlib hits extEquivCohomologyClass (Injective/Ext.lean:40) and Ext.homEquiv (DerivedCategory/Ext/Basic.lean:160): they supply comparisons, not the item's spectral sequence. The elementary scalar check is postcomposition with a times the identity of I. def-sp-spectral-sequence explicitly identifies each next page with homology, hence with kernel modulo image in Mod(A).

For step 7 the same double-complex theorem explicitly supplies a finite image filtration, convergence to total cohomology and eventual stabilization. Translating b=j+u preserves the differential bidegree, gives total degree t+u and converts 0 <= i <= t+u into -u <= j <= t. I checked def-sp-filtration's finite/exhaustive/separated meanings: F^0=H and F^(t+u+1)=0 imply all three properties. For t+u<0 the total term itself is zero, which proves the empty-interval clause without inferring vanishing from an unproved convergence claim.

I checked the small cases K=0, N=0, the zero ring, u negative, and K consisting of a single module in degree a <= u. In the last case the only source-cohomology row is j=-a and the abutment is Ext^(t+a), as required; the zero-degree/sign conventions agree. No finiteness or projectivity of source terms, and no finite injective dimension of N, is used. Every proof step is under 2000 characters. Every non-elementary construction/comparison is an existing cited statement, and every elementary identification is written out. The three generic off-unit tools are declared in split_report.tool_uses with their mathematical purpose. No new statement, duplicate, restated clause or cycle is introduced.

## Unfinished work

None in the authorized stage-1 split. The independent maintainer review remains the normal next stage after delivery.
