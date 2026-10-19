# Worker report: lem-fix-geometric-stalk-topos-point

## Files written

- `dag/nodes/sec-smooth-purity/lem-fix-geometric-stalk-topos-point.json`: repaired split. The statement, Lean record, and proof steps 1, 2, 4, 5, 6, 7 are unchanged. Step 3 is now 1058 characters, with an extracted section-existence lemma.
- `dag/nodes/sec-smooth-purity/lem-fix-weakly-etale-algclosed-section.json`: one new statement-only, unsplit node; no matching Mathlib result found.
- `citations.json`: one verbatim statement quotation for every node cited by every item step.
- `report.md`: this report. Earlier report and unsubmitted draft node are retained under `scratch/lem-fix-geometric-stalk-topos-point/`; `searches.jsonl` is retained and extended.

## Attachments

None. Searched the read-only `WeilConjectures/` source by the item blueprint tag, `geometricStalkToposPoint`, geometric-stalk/point concepts, and weakly-etale point/section concepts. No declaration states the whole item or the new lemma. The item's existing `Sheaf.AlgebraicGeometry.GeometricStalkToposPoint` stage-2 record is preserved; it is not a sorry-free upstream attachment.

## WANTED

None. All source TeX passages needed for this repair are present.

## What was wrong and what changed

The human returned the 2349-character non-elementary step 3 and required the statement and existing Lean record to remain unchanged, the route and other steps to remain intact, and hidden arguments to become cited nodes. I compared the retained sandbox copy with the current repository item and the return JSON. The existing repository still has the original seven-step proof. Only its third step is replaced; its statement and Lean record compare equal, and its other six steps compare equal as JSON objects.

The retained attempted repair had moved geometric-cover lifting into `lem-fix-proetale-cover-geometric-lift` and then cited details of that node's unwritten proof. Its four recorded search queries were not in `searches.jsonl`; the first dry run exited 1 with SEARCH CHECK FAILED and did not push. I archived that unsubmitted draft rather than delivering unsupported search records. It never became an existing DAG node. I preserved the old report and all logged searches. Fresh searches and source readings below concern the narrower replacement lemma; they are recorded verbatim from actual `msearch.py` calls. Earlier irrelevant or failed searches remain in the log but are not claimed as evidence for the new node.

The replacement retains the source route: first form the geometric fibres of the covering; use fpqc base change and its stated joint-surjectivity consequence to choose a nonempty fibre; use weakly-etale base change to check the hypothesis of the new lemma; obtain a section of that fibre; compose with the other projection and write the scheme-morphism equality. The new lemma extracts only the substantial passage from a nonempty weakly-etale scheme over the algebraically closed field to a section. It asserts neither the cover-lifting conclusion nor any sheaf or adjunction conclusion of the item. The residual-field algebra and the affine-spectrum construction are no longer accessed through another node's proof. The fibre-product and representative equations remain elementary explicit equations in the item. `proof_deps` is now exactly the union of `uses`.

## New nodes

`lem-fix-weakly-etale-algclosed-section` states: a nonempty scheme weakly etale over Spec of an algebraically closed field has a section over that same field. Its source is the residue-field argument in Stacks Tag 0F6C, `proetale.tex`, `lemma-geometric-lift-to-cover`, extracted after geometric base change. I read also Tag 092Q, `more-algebra.tex`, `lemma-absolutely-flat-over-field`, including the paragraph proving that local rings at primes are separable algebraic field extensions.

For a later splitter, the retained argument is as follows. Choose a point z and an affine open W = Spec B around it. Source-locality of weak etaleness (`lem-weil-pbc-weakly-etale-source-locality`) makes W weakly etale over Spec Omega; the affine convention `def-weil-pbc-ind-etale-algebra` identifies this with the weakly-etale Omega-algebra condition. The residue-field clause of `lem-weil-pbc-weak-etale-field` gives kappa(z)/Omega separable algebraic. An algebraically closed field is separably closed directly from the polynomial-root definitions. Apply `lem-weil-pbc-separable-extension-embeds-separably-closed` with base and target Omega and its identity algebra structure, obtaining an Omega-algebra map kappa(z) to Omega. Compose B to its stalk, the residue quotient (`def-weil-residue-field`), and that map. The resulting B to Omega map is an Omega-algebra map, so its Spec map into W, followed by W to Z, is a section: the composite on Omega is the identity. Affine contravariance and functoriality are stated in `def-weil-affine-spectrum`. This is the original local residue-field route, with no finite-type or quasi-compact assumption. The new node itself carries only its statement, not this future split.

Before introducing it I searched the whole DAG by 0F6C, weakly-etale/algebraically-closed/nonempty/rational-point/section words, and read the nearby candidate statements. I searched the whole blueprint with `blueprint_refs.py search` for `weakly etale`, `weakly etale field`, `nonempty weakly`, `weakly etale scheme over`, `algebraically closed field` and `0F6C`. No blueprint node states this section result. Its ancestor is `fix-lem-finite-tor-perfect`; the new ancestry includes the item as `via`, and it inherits the item's chapter and unit. It does not depend on the item, so the extraction creates no cycle.

Mathlib searches used LeanFinder twice, Loogle, LeanSearch, and grep in `AlgebraicGeometry/Morphisms`. All five selected searches succeeded. The semantic hits were etale scheme definitions, `Algebra.FormallyEtale.iff_exists_algEquiv_prod`, `Algebra.Etale.iff_exists_algEquiv_prod`, and the residue-field morphism declarations. I opened `Morphisms/WeaklyEtale.lean`, `ResidueField.lean` and `RingTheory/Etale/Field.lean`: the first supplies locality and stability, the second supplies the map from Spec kappa(z), and the third requires finite-type etale hypotheses for its product result. None supplies the same-field section for an arbitrary nonempty weakly-etale scheme as an exact result or one-line specialization. Therefore the new node is unsplit with `mathlib_match: null`. The node records the exact selected queries in `searches.jsonl` and their actual successful results; the previous draft's inaccurate unavailable verdict is not reused.

## Not duplicates

lem-fix-weakly-etale-algclosed-section vs lem-fix-geometric-stalk-topos-point: the new node concerns sections of weakly-etale schemes over an algebraically closed field; the item constructs a stalk adjunction and proves finite-limit preservation for two sites.

lem-fix-weakly-etale-algclosed-section vs lem-pur-proetale-inverse-image-stalk: the existing node compares stalks after inverse image along a scheme morphism, rather than constructing a section of a nonempty weakly-etale scheme.

lem-fix-weakly-etale-algclosed-section vs lem-cbc-proetale-sheafification-geometric-stalk: the existing node concerns invariance of abelian stalk colimits under sheafification; it gives no section of a scheme morphism.

lem-fix-weakly-etale-algclosed-section vs lem-weil-proetale-constant-sheaf-stalk: the existing node computes stalks of constant module sheaves, rather than rational sections of schemes.

lem-fix-weakly-etale-algclosed-section vs lem-cbc-proetale-extension-zero: the existing node concerns the exact extension-by-zero adjunction and its stalk formula, rather than sections over an algebraically closed field.

lem-fix-weakly-etale-algclosed-section vs lem-weil-pbc-weak-etale-field: the existing node gives finite-etale finitely generated subalgebras and separable algebraic residue fields of a weakly-etale algebra over a field; it does not make the affine-local scheme construction or provide a section of an arbitrary non-affine scheme.

lem-fix-weakly-etale-algclosed-section vs lem-weil-pbc-etale-cover-geometric-point-lift: the existing node assumes an etale covering; it does not cover a general weakly-etale morphism over an algebraically closed field without finite-presentation hypotheses.

## Review by Q14

I read `proetale.tex` Tags 0991 and 0F6C, `etale-cohomology.tex` Tag 04FM, and `sites.tex` Tag 00Y8 against the item. They construct the same geometric-lift functor, stalk and right adjoint; the right adjoint's restriction is precomposition, and the stalk is its left adjoint. The new node's source subargument is read together with Tag 092Q as described above. I opened the chapter and unit records and the parent `fix-lem-finite-tor-perfect`: this remains the topos-point justification used by its first proof paragraph, with no change of unit route and no SGA source.

For step 1 I read the statements of `lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered`, `def-weil-proetale-geometric-stalk`, `def-weil-size-convention`, `def-weil-pbc-geometric-stalks`, and `def-weil-pbc-category-colimit`. They respectively provide etale cofilteredness, the stated filtered pro-etale index and stalk diagram, the universe bounds, the etale colimit interpretation, and the cocone uniqueness used for functoriality. I checked the opposite direction of pointed arrows and the representative-isomorphism formulas. Step 1 is 1917 characters and its remaining argument is the one explicit construction of the stalk functor from that colimit.

For step 2 I read `def-weil-pbc-etale-site`, `lem-weil-pbc-etale-cover-geometric-point-lift` and `def-weil-geometric-point`. They give exactly jointly surjective etale arrows and a lift over the same algebraically closed field. No enlargement of Omega is used.

For repaired step 3 I read `def-weil-pbc-proetale-site` for fpqc covers and weakly-etale covering arrows; `lem-galois-fpqc-covering-base-change` for the base-changed covering; `def-weil-pbc-fpqc-covering` for its expressly stated joint surjectivity; and `lem-weil-pbc-weakly-etale-composition-base-change` for weak etaleness of each first projection. Thus the new section lemma is applied only to a nonempty scheme and a weakly-etale morphism with the algebraically closed base field Omega. Its conclusion is precisely q_i composed with s equals the identity, not just a point above a point. `def-pc-fibre-product` gives f_i composed with r_i equals u composed with q_i, which proves the displayed lift equation. The final representative calculation cancels e with its inverse explicitly. Each fact taken from a citation is in its statement, with a verbatim quote in `citations.json`; no proof text is used as a black box.

For step 4 I read both site definitions, `def-pc-fibre-product`, the weakly-etale composition/base-change statement, and `def-weil-pbc-sites-and-cohomology`. Their statements ensure the overlap is an object of the relevant site and provide the overlap lift and sheaf equalizer condition. The remaining matching-family construction is written out: choose a lift, evaluate, use the overlap to prove choice independence, and use surjectivity to prove uniqueness. Its elementary designation refers to that set-theoretic gluing calculation after the cited scheme facts.

For steps 5 and 6 I checked the colimit statement's cocone identity and uniqueness against both displayed adjunction maps. The sheaf-category definition identifies morphisms with natural transformations. The two inverseness calculations and naturality in the sheaf and the set are explicit evaluations; they require no additional theorem.

For step 7 I read `lem-weil-pbc-site-sheaf-sets-limits-sectionwise` and `lem-weil-pbc-filtered-colimits-commute-finite-limits`. They state exactly sectionwise set limits and the canonical comparison for a small filtered category and finite diagram category. Step 1 supplies the same small filtered category for all objects. The comparison uses projections and coprojections as required, including the empty finite diagram, so it proves finite-limit preservation rather than just preservation of nonempty products.

For the new lemma I tested the empty scheme (excluded explicitly; without that hypothesis there is no section), Spec Omega (identity section), disjoint unions of copies of Spec Omega (choose a component), and an arbitrary affine weakly-etale algebra (a chosen prime supplies the residue-field map). No finite-type hypothesis is imported from Mathlib's etale results, and no characteristic, noetherian, separation or quasi-compact hypothesis was added. Algebraic closedness matters: Spec C over Spec R is etale and nonempty but has no R-section. These tests distinguish the new lemma from a merely surjective morphism assertion. The item retains the empty lift-set case in step 4 and the empty finite-limit case in step 7.

I checked B1-B9: the sole new node is self-contained, introduces all its objects, cites definition nodes for algebraic closedness, schemes, affine spectrum and weak etaleness, defines a section inline, uses ordinary TeX backslashes, names its Stacks label, has no proof in its statement, has all actual search kinds and filled blueprint provenance, and is not a Mathlib leaf without evidence. B10's upstream attachment search found none. For C1-C4 I read every cited statement and rebuilt every verbatim quotation; the only non-elementary extracted argument now has its own statement node. For C5-C8 I checked duplicates, ancestry and acyclicity and kept the same source route. For D1-D5 the new lemma is a strict scheme-theoretic subargument, leaving the covering, sheaf, adjunction and finite-limit work in the item. For E1-E7 I checked the field, nonemptiness, weak etaleness, smallness and site hypotheses above, including equality of morphisms and representative changes. No disputed statement or source error was found. I corrected the inaccurate retained search records, unnecessary old proof dependencies and the unsupported reference to a new node's proof. Every non-elementary step is below 2000 characters; the six steps outside the returned step are unchanged.

## What remains

The new section-existence lemma is deliberately unsplit, as required for newly introduced nodes. No other unfinished work in this item is claimed complete. Dry-run and delivery results are recorded below after the required server checks.
