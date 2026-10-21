# Stage-1 report: lem-pur-finite-pullback-localization-cohomology

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-finite-pullback-localization-cohomology.json`: statement, now split into six steps; statement unchanged; not a Mathlib leaf. All statement dependencies and original metadata retained.
- `citations.json`: 11 verbatim statement quotations, one for each cited node in each proof step.
- `searches.jsonl`: six actual Q96 searches, appended by the required msearch command. The item's seven inherited Q80 search records are preserved in the item; they are not presented as Q96 searches.
- `report.md`: this report. `write_split.py` is a sandbox-only reproduction script and is not part of the DAG delivery.

New nodes: 0. New Mathlib leaves: 0. No unit record is changed: this item is not the unit's key statement.

## Attachments

None. Searched the live read-only `lean/WeilConjectures/` by the exact blueprint tag, the item id, pro-etale/restriction terminology, and the generic exact-derived homology comparison name. The generic project declaration `CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso` in `WeilConjectures/Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean:263` has the abstract cohomology comparison, but does not state the pro-etale graph-coprojection or coefficient-ring comparison. The Zariski localized-stalk declarations likewise have different sites and coefficients. None supplies every clause of this item. No source declaration is claimed as an attachment.

## WANTED

None. All sources used are present locally.

## What was wrong and what changed

The existing node was a statement-only dependency created in Q80's split of `lem-pur-etale-iso-descent`. Its statement is coherent and unchanged. The missing work was the proof connecting the specified finite-level pullback to the exact restriction functor, and the normalization and naturality of the cohomology comparison on the actual unbounded derived category. The proof now carries that argument rather than placing either clause in a new node.

The graph comparison, exactness of module restriction, exact-derived factorization, lifting of natural isomorphisms, cohomology of an exact functor, and the natural-transformation universal property of localization already have DAG nodes. I reused their statements. In particular no new generic exact-functor or localization node was needed. The cohomology calculation is in the abelian category of module sheaves; it does not replace sheaf cohomology by the cohomology of sections on an object.

No STATEMENT-DISPUTED issue was found. No coefficient category, boundedness, surjectivity, constructibility, or finiteness-of-schemes hypothesis was added. This item is entirely at the finite ordinary coefficient level, not the completed integral or condensed level. It does not assert geometric stalk conservativity for all pro-etale sheaves.

## What remains unfinished

No part of this item's stage-1 split is left unfinished. Its existing dependencies retain their own states; stage 1 does not prove them in Lean. No Lean was written or compiled and no library build was run.

## Sources and Mathlib searches

I read the current blueprint `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-cohsm/lem-pur-etale-iso-descent.md` and `.proof.md`, and the unit's `_section.md`. I also read the recorded chapter and unit JSON, and SETUP's three-level route. The ancestor's first proof sentence needs cohomology pullback compatibility; the present split realizes that ingredient and leaves the unit's smooth-purity route intact. The item's inherited `blueprint.from.place` already specifies that location and was retained; `same_as` is searched and remains empty.

For the site calculation I read `sites.tex`, Tag 03CE, `lemma-localize-given-products`: base change to the slice gives the localization morphism. For exact derivation I read `derived.tex`, Tag 015F, `lemma-right-derived-exact-functor`, including its unbounded clause and the assertion that every complex computes it. For the cycle and boundary calculation I read `homology.tex`, Tag 010N, `lemma-exact-functor`. I checked these tag-label pairs in `literature/stacks-project/tags/tags`. The natural-transformation enhancement of the localization property is recorded explicitly as Mathlib rather than attributed to a Stacks sentence that does not state it: I read `Mathlib/CategoryTheory/Localization/Predicate.lean:278-361`, including the lifting formula and liftNatIso. The exact-homology instance at `Mathlib/Algebra/Homology/ShortComplex/PreservesHomology.lean:60` was also read. There are no new nodes requiring separate sources.

The required search command was used for these exact Q96 queries:

- leanfinder: `Derived pullback of finite constant coefficient sheaves along an object of the small pro etale site is naturally termwise slice restriction, commuting with cohomology`
- loogle: `"homologyFunctorIso"`
- grep: `pro[Ee]tale.*[Rr]estrict|[Rr]estrict.*pro[Ee]tale|overPullback`
- leansearch: `Inverse image on the pro etale site along a weakly etale object equals restriction to the slice site, naturally on derived categories and cohomology`
- leanfinder (second phrasing): `Canonical inverse image for sheaves of modules on a localized ringed site is the exact restriction functor and its left derived functor commutes with all cohomology functors`
- grep: `restrictFunctorIsoPullback|homologyFunctorIso|liftNatIso`, scoped to `AlgebraicGeometry/Modules`.

All six services returned successfully. The first semantic query returned pullback-of-free-module-sheaf comparisons and the general presheaf-pullback/sheafification formula. I opened `Sheaf/PullbackFree.lean:118` and `Sheaf/PullbackContinuous.lean:106`: neither identifies the particular pro-etale pullback with slice restriction or supplies the graph normalization. LeanSearch's `Scheme.Modules.restrictFunctorIsoPullback` was read at `AlgebraicGeometry/Modules/Sheaf.lean:453`; it concerns structure-sheaf modules on Zariski open immersions. The second semantic query returned abstract derived-functor results and sheaf-module abelianness. The exact-derived results are tools already represented in the DAG, not a one-line specialization giving the site's normalized comparison. Loogle's homologyFunctorIso results are likewise generic tools, represented by the existing exact-functor-complex-cohomology node. No search was fabricated or recorded as an outage.

DAG and whole-blueprint searches used inverse-image, restriction/cohomology and exact-functor terminology, and the relevant source labels. Whole-blueprint queries included `restriction cohomology`, `cohomology restriction`, `inverse image`, and `exact functor`. The generic exact-derived-natural-iso and proper-base-change exact-functor leaves were found and reused. No blueprint node states this full normalized finite comparison in another form.

## Tool uses

The four non-leaf off-unit generic tools are declared, with reasons, in `split_report.tool_uses`:

- `lem-sfb-proetale-object-inverse-image-restriction`: ordinary graph-coprojection and ring normalization.
- `lem-weil-proetale-weakly-etale-localization`: the pro-etale slice and constant coefficient identifications.
- `lem-pur-site-restriction-module-adjunction-exact`: exactness on module sheaves on a localized site.
- `lem-weil-pbc-exact-functor-derived-functor`: exact functors compute their own unbounded derived functors.

Each is a black-box site or homological-algebra tool; none replaces a step of smooth purity by a different geometric route. The other homological-algebra statement citations are existing Mathlib leaves. No SGA source is used.

## Not duplicates

No new nodes. Exact-functor cohomology and derived natural-isomorphism descent were specifically found as existing nodes and cited instead of duplicated.

## Review by Q96

I read delivery-errors B through E in full and reviewed the split against the cited statements, not the proofs hidden inside them. There are no new nodes to test for B's standalone-statement, notion, source-tag, metadata or Mathlib-leaf requirements. The item preserves its original statement and metadata; every proof entry has an explicit source, every elementary flag is Boolean, and proof_deps is exactly the union of uses. The 11 citation quotes are literal substrings of the corresponding statements. No cited node is merged or missing in the read snapshot. All six steps are below 1100 characters, so no long-step threshold conceals a sublemma.

Step 1 uses clauses (1)-(3) of the graph-comparison node: its statement explicitly supplies the initial graph pair, the induced inverse-image isomorphism, the identification of the specified coefficient structure map, and the natural module isomorphism. The weakly-etale-localization statement explicitly supplies both the equivalence of sites with the localized topology and the unique constant-section-fixing ring isomorphism. The restriction-adjunction statement explicitly says restriction of module sheaves is exact; its additional extension-by-zero assertions are not used. I checked that the object-of-small-pro-etale-site hypothesis is exactly available. Exactness transported by equivalences and an isomorphism of functors, and additivity checked sectionwise, are routine consequences, not extra geometric assertions.

Step 2 uses the exact-derived-factorization statement for preservation of quasi-isomorphisms and the factorization with no boundedness hypothesis. The exact-functor-derived-functor statement's clause (1) is the unbounded left-derived assertion; its bounded-below clause is not used. The finite-level part of the pullback definition identifies precisely which sheaf-level module pullback is being derived and specifies the same coefficient map and K-flat convention. The normalized comparison is checked on a resolution by the actual map F(q), so its direction is fixed. I did not cite only a definition for the assertion that an exact functor computes its derived functor: the theorem node supplies that assertion.

Step 3 applies the exact-derived-natural-iso leaf, whose statement gives the unique normalized derived isomorphism and explicitly says its cochain components are the ordinary components in each degree. Both functors are additive and preserve finite limits and colimits by Step 1. I checked the displayed normalization's direction against the leaf's equation. The commutative square at the resolution map is written out; it shows the comparison is independent of resolutions with the required graph normalization, rather than asserting this by an unspecified transport.

Step 4 uses the exact-functor-complex-cohomology statement. It explicitly gives a natural isomorphism in the direction H(RK) to R(HK), and its last clause gives precisely the inclusions of cycles and projections onto cohomology that the item demands. The cohomology-sheaf definition identifies the quotient in module sheaves, not the quotient of sections. There is no hidden flatness assertion or use of sectionwise cokernels for sheaves.

Step 5 uses the abstract-derived-category statement to identify Q as localization at quasi-isomorphisms and to factor cohomology. It uses clause (2) of the localization-universal-property leaf to lift the natural isomorphism, including its specified component formula and invertibility. I checked both input functors invert quasi-isomorphisms, the codomain is the A_U-module sheaf category, and the factorizations used to normalize them are exactly those already introduced. This proves naturality on the derived category; merely citing functor factorization without the transformation statement would not suffice.

Step 6 is elementary composition of the two constructed natural isomorphisms. I wrote the two naturality equations in the required order and explicitly inverted the equation for a denominator q of a roof. Thus the assertion for roofs uses the same c, including for derived morphisms that are not represented by single chain maps. No new lemma restates either of the item's clauses and no circular induction or derived comparison is assumed.

I tested identity u (all graph and ring maps become identities), the empty object U (the zero module-sheaf category), non-surjective open objects, and objects u that are not monomorphisms (the graph comparison still applies; no uniqueness of a map to U is asserted). For complexes I checked a sheaf in one degree, an acyclic complex, a genuinely unbounded complex, and a roof with a quasi-isomorphism denominator. Exactness and localization apply uniformly in all integer degrees; no boundedness, stalk-conservativity, or geometric descent assumption enters. The finite coefficient ring need not be a field, and no tensor-flatness of individual sheaves is used. I found no mathematical or source statement needing correction.

The initial server review_split check passed before writing this report. The first full dry run rejected one exactness quotation because it was shorter than the gate's 40-character minimum; I replaced it with the full cited statement. No mathematical step changed. The full deliver.py dry run and final push are the delivery gates; their terminal outputs determine the final delivery answer.
