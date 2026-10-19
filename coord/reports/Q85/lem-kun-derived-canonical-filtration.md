# Q85: lem-kun-derived-canonical-filtration

## Files written

- `dag/nodes/sec-smooth-purity/lem-kun-derived-canonical-filtration.json`: item split into five proof steps; statement and hypotheses unchanged.
- `dag/nodes/sec-smooth-purity/lem-kun-bounded-derived-roofs.json`: new statement-only auxiliary node; no exact Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-kun-canonical-truncation-filtration.json`: new statement-only auxiliary node; no exact Mathlib match.
- `citations.json`: verbatim statement quote for every cited node in every proof step.
- No Lean files, compiler, Lake, or live-project files were written.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the item id, its blueprint tag, canonical truncation terminology, and filtered-derived declarations. No sorry-free declaration states this item exactly. The source checkout is read-only reference material and contains no declaration to attach.

## WANTED

None. The named Stacks files are present locally. The proof follows the local Stacks copies of Tags 0118, 05RW, 05S2, 05S6 and 0H7Z, with Mathlib's derived-category fraction declarations used only to identify the bounded-roof ingredient.

## Issues found and repaired

The imported statement is mathematically coherent and was left unchanged. It does not assert a termwise functorial choice of representatives; the construction is made on bounded roofs and then descended through the filtered localization. The two new nodes are strictly smaller than the item: one supplies bounded representatives and bounded common refinements, and the other supplies the finite truncation filtration and its two-term graded quotient. Neither node restates the functor or either natural isomorphism of the item.

The item is not a key node of its unit, so no unit record was edited. The nearest blueprint ancestor is `lem-kun-0f0f`; its preliminary integral homological-algebra paragraph is the stated source of the bounded-roof and canonical-truncation route.

## Not duplicates

- `lem-kun-bounded-derived-roofs` vs `lem-kun-filtered-quasi-isomorphism-fractions`: the existing node gives a right calculus for uniformly finite filtered quasi-isomorphisms; it does not give bounded representatives of ordinary (D^b(R)) objects or bounded ordinary-derived roofs.
- `lem-kun-bounded-derived-roofs` vs `lem-trf-filtered-bounded-localization-comparison`: the trace-formula node compares bounded and bounded-below *filtered* localizations and truncates filtered complexes; it assumes a filtered object and does not state bounded ordinary-derived representatives or common bounded roofs for arbitrary (D^b(R)) morphisms.
- `lem-kun-canonical-truncation-filtration` vs `def-sbc-standard-tstructure-derived-category`: the existing definition states the standard t-structure and the individual upper truncation triangle; it does not state the finite filtration by all truncations, its two-term successive quotients, or the chain-homotopy naturality package.
- `lem-kun-canonical-truncation-filtration` vs `lem-trf-filtered-truncation-triangle`: the existing node truncates an already filtered derived object by filtration index and identifies a pure-grade localization with an ordinary derived category; it does not construct the canonical filtration on an ordinary bounded complex or identify its (i)-th grade with (H^{-i}(K)[i]).
- `lem-kun-canonical-truncation-filtration` vs `lem-kun-filtered-page-localization`: the existing node identifies stationary filtered pages with the image filtration on cohomology; it does not state the representative-level two-term quotient or the shifted-cohomology comparison for canonical truncations.
- `lem-kun-canonical-truncation-filtration` vs `lem-kun-bounded-tensor-tor-spectral-sequence`: that node uses the canonical truncation calculation as one step in a larger tensor spectral-sequence proof but has no statement asserting this truncation lemma.


Additional duplicate pairs reported by the delivery checker were opened individually and differ as follows:

- `lem-kun-bounded-derived-roofs` vs `lem-kun-derived-canonical-filtration`: the new node concerns bounded representatives and roofs in ordinary (D^b(R)); the item constructs a filtered functor and graded/underlying natural isomorphisms.
- `lem-kun-bounded-derived-roofs` vs `lem-weil-pbc-bounded-below-cochain-localization`: the existing node gives the universal localization of bounded-below complexes; it does not give bounded representatives or common bounded roofs for (D^b(R)).
- `lem-kun-bounded-derived-roofs` vs `def-trf-uniform-filtered-homotopy-localization`: the existing definition sets up a uniformly finite filtered localization and its fraction class; it does not discuss ordinary derived roofs.
- `lem-kun-bounded-derived-roofs` vs `def-trf-uniform-finite-filtered-localization`: the existing definition defines filtered complexes and graded quasi-isomorphisms; it does not provide bounded ordinary-derived representatives or roof refinements.
- `lem-kun-bounded-derived-roofs` vs `lem-trf-bounded-filtered-localization-embedding`: the existing statement embeds bounded filtered localizations into bounded-below filtered localizations; it assumes filtered objects and gives no ordinary (D^b(R)) roof theorem.
- `lem-kun-canonical-truncation-filtration` vs `lem-kun-derived-canonical-filtration`: the new node is the representative-level finite truncation calculation; the item adds the functor on (D^b(R)), localization independence and both natural comparisons.
- `lem-kun-canonical-truncation-filtration` vs `def-sp-map-good-upper-truncation`: the existing node compares an additive functor applied to one truncation with truncation after applying the functor; it does not form the full filtration or identify its graded quotient with shifted cohomology.
- `lem-kun-canonical-truncation-filtration` vs `lem-sp-ce-good-cut-identification`: the existing node concerns a good cut in a first-quadrant Cartan–Eilenberg bicomplex and a derived truncation; it does not state the ordinary bounded-complex canonical filtration.
- `lem-kun-canonical-truncation-filtration` vs `lem-sp-derived-upper-truncation-comparison`: the existing node compares one smart truncation with one canonical derived truncation; it does not state all successive quotient comparisons or truncation homotopy naturality.
- `lem-kun-canonical-truncation-filtration` vs `lem-sp-double-complex-truncation-decalage`: the existing node is a decalage identification for a filtered bicomplex total; it has no two-term (operatorname{im}d\hookrightarrow\ker d) quotient for an arbitrary bounded complex.
- `lem-kun-canonical-truncation-filtration` vs `lem-sp-vertical-cutoff-column-quasiiso-equal`: the existing node proves a special quasi-isomorphism between vertical cutoff cokernel and window when (a=b); it does not identify canonical truncation grades.
- `lem-kun-canonical-truncation-filtration` vs `lem-sp-vertical-cutoff-column-quasiiso-strict-nonpositive`: the existing node treats nonpositive vertical cutoffs under explicit bicomplex hypotheses; it does not give the canonical filtration statement.
- `lem-kun-canonical-truncation-filtration` vs `lem-sp-vertical-cutoff-column-quasiiso-strict-positive`: the existing node treats positive vertical cutoffs under explicit bicomplex hypotheses; it does not give the canonical filtration statement.
- `lem-kun-canonical-truncation-filtration` vs `lem-sp-vertical-cutoff-column-quasiiso-strict`: the existing node treats a vertical cutoff/window comparison; it does not give the canonical filtration statement.
- `lem-kun-canonical-truncation-filtration` vs `lem-sp-vertical-cutoff-column-quasiiso`: the existing node treats general vertical cutoff windows and a projection equation; it does not identify truncation grades with shifted cohomology.
- `lem-kun-canonical-truncation-filtration` vs `lem-sp-vertical-cutoff-comparison-epi`: the existing node proves an epimorphism for a pair of smart truncations; it does not give a graded quasi-isomorphism or homotopy-natural filtration.
- `lem-kun-canonical-truncation-filtration` vs `lem-sp-vertical-cutoff-comparison-kernel-two-term`: the existing node describes a two-term kernel in a nonnegative vertical-window construction; it is not the arbitrary bounded-complex canonical truncation quotient.

## Mathlib searches

For `lem-kun-bounded-derived-roofs`, I ran and read LeanFinder for bounded representatives and bounded common roofs, LeanSearch for bounded derived roofs, Loogle for `DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE`, and Mathlib grep for the bounded representative and fraction declarations. The relevant declarations are `DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE` and `DerivedCategory.right_fac_of_isStrictlyLE_of_isStrictlyGE` in `Mathlib/Algebra/Homology/DerivedCategory/TStructure.lean` and `Fractions.lean`. They provide the two ingredients separately; no single declaration states the complete bounded-roof independence package, so the node remains statement-only.

For `lem-kun-canonical-truncation-filtration`, I ran and read LeanFinder for the shifted graded piece, LeanSearch for the good-truncation quotient, Loogle for `CochainComplex.shortComplexTruncLE_shortExact`, and grep over `Mathlib/Algebra/Homology/Embedding` and `DerivedCategory`. Mathlib supplies truncation functors, the short exact truncation row and quasi-isomorphism instances, but not the finite filtration, explicit two-term quotient, and chain-homotopy naturality as one statement. The valid and exploratory queries, including the two rejected compound Loogle patterns, are retained in `searches.jsonl`.

## Review by Q85

I read the item, the fixed chapter `sec-smooth-purity`, the unit `sk-prop-sf-kunneth-ordinary`, the nearest blueprint node `lem-kun-0f0f`, and the local Stacks source at Tags 0118, 05RW, 05S2, 05S6 and 0H7Z. I also read the full statements of both new nodes and every existing node cited by the five item steps.

Step 1 uses `def-weil-pbc-bounded-derived-subcategories` for the bounded cohomology hypothesis and `lem-kun-bounded-derived-roofs` for the actual bounded complex representative, bounded middle roof, and common bounded refinement. The latter statement includes arbitrary (R)-modules as terms and does not add finite-generation or projectivity assumptions. I checked that the representative interval is a cochain-degree interval, matching the item's “bounded termwise complex” language.

Step 2 uses `lem-kun-canonical-truncation-filtration` for all substantive truncation facts: the finite bounds, preservation by chain maps, the quotient (operatorname{im}d^{-i-1}hookrightarrowker d^{-i}), its map to (H^{-i}(K)[i]), and the filtration-preserving homotopy. `def-sp-filtration` and `def-sp-filtered-complex-subquotients` supply the filtered-complex and graded-quotient meanings. I checked the sign/index convention: the quotient is in degrees (-i-1,-i), so its cohomology in degree (-i) is represented by (H^{-i}(K)[i]).

Step 3 uses the canonical-truncation node to verify that a denominator quasi-isomorphism is a quasi-isomorphism on every grade, exactly the condition (W) in `def-kun-finite-filtered-module-homotopy`. `lem-kun-filtered-quasi-isomorphism-fractions` supplies two-out-of-three and right fractions. The bounded common-refinement clause of the roofs node is what connects equality in the ordinary derived localization to equality after filtered localization; no proof of a node's construction is used in place of its statement.

Step 4 reads the underlying roof through the localization (Q) from `def-weil-abstract-derived-category`. The component of (omegamathcal T) is the representative identification (Q(K)cong C), and the roof-independence statement from Step 3 makes it natural for every derived morphism. No extra boundedness or representative choice is imposed on (D(R)).

Step 5 uses the canonical graded quasi-isomorphisms and their chain-map/homotopy naturality from the truncation node. The filtered-fraction node ensures that these comparisons descend across every denominator in (W). Thus the map attached to a roof is exactly (H^{-i}(u)[i]), while Step 4 gives the underlying map (u). This verifies compatibility of both natural isomorphisms and the representative-level formulas.

I tested the new statements on the zero complex, a complex concentrated in one degree, and a two-term complex with zero differential. The filtration is finite in each case; the only nonzero grade is the expected shifted cohomology, and a quasi-isomorphism of such complexes induces the claimed grade quasi-isomorphism. I also checked an arbitrary bounded complex with zero terms at both ends, where the extreme truncation pieces are zero. No hypothesis on termwise projectivity or finite generation is used.

All citations in `citations.json` are exact substrings of the cited node statements. The proof steps contain the representative construction, localization argument and graded comparison rather than moving an item clause into a new node. No long step hides a separate lemma, no cycle was introduced, and no off-unit tool citation was needed.

## What could not be finished

The two new nodes are intentionally statement-only non-Mathlib leaves for later stage-1 workers. The item split itself is complete; no Lean or compiler work is authorized in this run.
