# Q95 stage-1 delivery: lem-pur-comparison-pullback-open-unit

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-comparison-pullback-open-unit.json`: statement, split into five steps; no Mathlib match for the whole site-specific equation.
- No new nodes, no new Mathlib leaves, no unit or chapter changes.
- `citations.json`: all 15 step/node citations, with verbatim extracts of their statements.
- `searches.jsonl`: retained command-generated search log. `prepare.py` is sandbox-only preparation, not project tooling or a delivered node.

## Attachments

None. I searched the project source under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact blueprint tag, comparison/pullback names and unit/restriction language. The relevant constructions are `AlgebraicGeometry.ProEtale.comparisonAdjunction` in `SixFunctors/ProEtale/Comparison/Defs.lean`, `lowerStarCompComparisonLowerStarIso` in `Comparison/LowerStar.lean:59`, and `comparisonUpperStarCompUpperStarIso` in `Comparison/LowerStarAcyclic.lean:153`. The last definition is an adjoint conjugate of the direct-image comparison. These construct the maps but do not assert this item's open-restriction unit equation. The nearby unit isomorphism theorem and the direct-image comparison-mate theorem concern different assertions. No finished declaration supplies every clause of this item. No Lean was written or compiled.

## WANTED

None. All sources used are available locally.

## Statement clarified

STATEMENT-DISPUTED (map specification, repaired): the imported item requires the canonical isomorphism of `lem-weil-pbc-comparison-pullback`, while that node's statement itself only asserts existence of an isomorphism with coherence clauses. The construction of that specific isomorphism must be supplied to make this item's normalization unambiguous to a reader of statements alone. I added its defining data: the two composite adjunctions and the conjugate of the sectionwise direct-image identity. This is the construction in the existing DAG split of the comparison theorem (step 2), and in the upstream definition `comparisonUpperStarCompUpperStarIso` just read. It agrees with the blueprint's canonical base-change comparison. This is a specification of the intended map, not an assumption of the desired equation.

Why the specification matters: an arbitrary isomorphism cannot replace the canonical map. For the identity open immersion on a nonempty geometric point and coefficients Z/3, replacing the identity comparison by minus the identity sends the unit section 1 to -1 rather than 1. Thus deriving the equation from bare existence of some natural isomorphism would be invalid. The added clause selects the intended construction, and step 3 then derives its normalization from the independent generic conjugate-unit theorem. No hypotheses or conclusion have been added or removed. I also changed doubled TeX backslashes to single TeX backslashes; this is a typography repair only.

## Blueprint and searches

I read the chapter and unit records, the current `main-20261015` supported Kunneth proof, paragraph 4, and the current and older comparison-pullback blueprint files. This item is a site-theoretic refinement below `lem-pur-kunneth-supported`, through the existing supported-comparison ancestry. I preserved the historical chapter/unit binding and blueprint ancestry. The existing unit binding is `sk-prop-a1-kummer`; this generic normalization is not a replacement for any Kummer or purity argument.

Whole-DAG searches for `00WX`, `unit_conjugateEquiv`, `adjoint-sheaves`, comparison/unit language, and blueprint searches for `conjugate`, `comparison pullback`, `adjunction unit`, and `open restriction` found the existing conjugate-unit, composite-adjunction and restriction nodes used here. No other blueprint node states this exact equation. I used those nodes instead of inventing a site-specific restatement or a new generic categorical lemma.

All six Mathlib searches were executed with the required `msearch.py`, and their actual hits were read. The first LeanFinder wording and LeanSearch return Zariski module restriction-unit results, which do not concern the two small etale/pro-etale topoi. Loogle returns `CategoryTheory.unit_mateEquiv`; the second LeanFinder wording returns composite-left-adjoint comparison results. The adjunction grep locates `unit_mateEquiv` at Mates.lean:136 and `unit_conjugateEquiv` at :300; I read `unit_conjugateEquiv_symm` at :311, which is precisely the existing generic Mathlib leaf's equation. The site-specific grep returned no hits. None is a one-line specialization to the item without the site and open-unit calculations written here. Every search recorded in the item is in the generated log; no unavailable service is represented as a negative search.

## Not duplicates

No new nodes. In particular, the generic mate-unit lemma is already present, and I did not create another one. The existing conjugate-isomorphism unit lemma suffices without even adding the mate-unit lemma as a dependency.

## Review by Q95

I checked the actual sources and every cited node's statement rather than relying on dependency names. For the item I read Stacks `sites.tex`, Tag 00WX (`lemma-adjoint-sheaves`, lines 2579ff), `categories.tex`, Tags 0B65 (`lemma-transformation-between-functors-and-adjoints`, lines 3542ff) and 0DV0 (`lemma-compose-counits`, lines 3576ff), the etale restriction discussion following Definition 03S3 in Tag 03S2, the localization lemma 03CE in `sites.tex`, and the pro-etale open-immersion lemma 09BN in `proetale.tex`. Stacks does not state this entire refinement verbatim, so the proof origin is explicitly agent-written. No forbidden SGA route is used. There are no new-node sources to audit.

Step 1 uses exactly the two direct-image formulas in `def-weil-pbc-direct-image` and `def-weil-proetale-inverse-image`, and restriction along the inclusion in `def-weil-pbc-site-comparison-morphism`. Their statements give the section values and arrow formulas used. Equality on constant scalars proves linearity here; no claim about arbitrary ringed-topos coefficient comparisons is smuggled in.

Step 2 uses the inverse-image and comparison definitions for the actual adjunctions and the complete unit formula in `def-weil-pbc-composite-adjunction`. I checked the order: L1 is nu_V^* after J and R1 is K after nu_V,*; L2 is P after nu_T^* and R2 is nu_T,* after Q. Thus the two displayed composite units have the stated targets. Fixed constant finite commutative coefficients are exactly the assumptions under which these adjunctions are used.

Step 3 cites `lem-weil-pbc-conjugate-iso-unit-equation`, whose statement gives exactly R1(gamma) eta1 = delta eta2 for delta:R2 -> R1. This is the formula needed, with no reversed mate or reversed comparison. The item now defines its canonical gamma explicitly, so this step does not take an unmentioned normalization from the proof of another node. The expanded unit terms come from the separately cited composite-adjunction definition.

Step 4 uses clause (2) of `lem-weil-pbc-etale-inverse-image-restriction` for the etale unit, the displayed unit formula of `lem-pur-proetale-open-unit-evaluation` for the actual module unit, and clause (3) of `lem-sfb-proetale-object-inverse-image-restriction` for the module restriction identification already fixed in the statement. Their statements contain these precise assertions. The latter node is not being cited for a unit formula it lacks; that was why the separate pro-etale unit-evaluation node was necessary. The etale abelian formula extends to fixed-A modules by naturality for each scalar, as stipulated in the item. The definition of open immersion identifies it with the inclusion of an open subscheme, so an object entirely over that open has W times_T V = W. No quasi-compactness, finite type, algebraic closure or constructibility is used. These generic off-unit tools are individually declared in `split_report.tool_uses` for review.

Step 5 only evaluates the already-proved equality, uses the three identity components just computed, and cancels the inverse isomorphisms gamma and a. It then checks equality on every object and every section. The comparison definition gives the sectionwise direct image, and the module-category definition says that module morphisms are underlying natural transformations with linear components, so this equality is indeed in the required category. This is an elementary calculation, not an inline comparison theorem left unproved.

I checked small cases: V empty (no nontrivial section test remains), V=T (both open units are identities and the equation reduces to the comparison unit), F=0 and the zero coefficient ring (all displayed maps agree), and nonzero constant Z/3 sections (the direction of a and gamma is detectable). The proof never assumes that comparison direct image is faithful. The source-specific normalization was the issue corrected, not the statement's coefficient category. All five steps are below 900 characters, so no step reaches the 2000-character long-step threshold. Citations quotes were checked as exact substrings of the statements, and the proof-dependency list is exactly the union of step uses. The first server `review_split` passed with no new nodes; the full dry run is the final delivery gate.

## Unfinished

None in this one-level split. Existing dependencies keep their own states and are not edited by this delivery.
