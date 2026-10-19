1. Files written:
- item `lem-weil-pbc-localize-ringed-site-morphism` (statement, split proof; no Mathlib match).
- `lem-weil-pbc-slice-site-localization` (statement-only dependency; no Mathlib match).

2. Attachments: none.

3. WANTED: none.

4. The item follows Stacks sites-modules Tag 04J0 and its underlying sites Tag 03CF. I added one genuinely smaller node for the underlying slice-site morphism and kept the ringed/module conclusions as proof steps. The existing localized ringed-site definition is reused rather than duplicated. Mathlib searches found only the internal `Over.map` localization API, which does not state the arbitrary continuous-functor comparison, so the new node remains unsplit.

5. Nothing remains unfinished in the split.

## Review by NG
I read the complete item source at sites-modules.tex Tag 04J0 and the underlying construction at sites.tex Tag 03CF. Step 1 uses the new node, whose statement explicitly supplies continuity of u_V, the induced f_V, inverse-image comparison, and direct-image comparison. Step 2 uses the localized-site definition for O|_U and the Step-1 inverse-image isomorphism to define the restricted ring map; all hypotheses (small sites, continuous u, ring map c) are present. Step 3 uses the module-adjunction statement for the tensor formula, the module-category definition, and the sheaf tensor-product definition; it checks sectionwise that both direct images are G(u(T)) with the same restricted R(T)-action. I tested the construction on V terminal (recovering the original morphism) and on u=id (the localization square is the identity/relocalization square). Citations.json quotes are verbatim excerpts from each cited node statement.

## Not duplicates
lem-weil-pbc-slice-site-localization vs lem-weil-pbc-localize-ringed-site-morphism: the new node is the underlying unringed Tag 03CF construction, while the item adds a ring map and module pullback/direct-image comparisons from Tag 04J0.
lem-weil-pbc-slice-site-localization vs lem-weil-pbc-etale-restriction-pullback-unit: the existing node is restricted to cartesian squares of scheme etale sites and a pullback unit; the new node treats arbitrary small sites and a continuous functor, with no schemes or etaleness.
lem-weil-pbc-slice-site-localization vs lem-weil-pbc-etale-underived-exchange-restriction: the existing node proves an underived exchange formula for scheme etale sites; the new node constructs the general localized site morphism and its inverse/direct image comparisons.
lem-weil-pbc-slice-site-localization vs lem-weil-pbc-pullback-sections-comparison: the existing node compares sections over a scheme fibre product; the new node is a categorical slice-site/topos statement for arbitrary continuous functors.
lem-weil-pbc-slice-site-localization vs lem-weil-pbc-etale-object-sections-base-change: the existing node is a scheme-etale sections compatibility result; the new node gives the general u_V site morphism and sheaf-level localization identities.

## Second reading by NG
- Item statement: compared every hypothesis and conclusion with sites-modules.tex Tag 04J0, lemma-localize-morphism-ringed-sites, and sites.tex Tag 03CF, lemma-localize-morphism; PASS. The tensor-pullback comparison is the consequence of the commuting ringed-topos square, now justified by adjunction rather than an unexplained tensor identification.
- Step 1: read the full statement of lem-weil-pbc-slice-site-localization against Tag 03CF; PASS after making the original inverse image's finite-limit preservation explicit. The item supplies precisely this hypothesis; continuity alone is not used to claim exactness.
- Step 2: compared the coefficient-map composite with the displayed composite in the proof of Tag 04J0; read the restriction definition and Step-1 comparison; PASS, elementary composition and restriction of c.
- Step 3: read the module-adjunction theorem, localized-site/module-category definitions and tensor definition; PASS after writing the right-adjoint Hom calculation, coefficient adjunct compatibility, the four module Hom bijections, the tensor-unit maps for localization, and the direct-image action a_T(r). No tensor/sheafification commutation theorem is assumed.
- New node lem-weil-pbc-slice-site-localization: compared its small-site, morphism-of-sites, object V and U=u(V) hypotheses and both comparisons with Tag 03CF, lemma-localize-morphism; PASS after explicit finite-limit preservation and TeX repair. Statement only, no proof/proof dependencies; both notion definitions were opened and checked, and the unused module-definition dependency was removed. It is a genuinely smaller unringed slice-topos theorem: its non-elementary content is exactness of the induced inverse image, proved in the source through the slice-topos equivalence, not ring maps or scalar extension.
- Small cases: u=id gives identical restriction functors and actions; terminal V (when present) recovers the original morphism up to slice equivalence; zero module gives zero on both sides and zero coefficient rings are allowed. Empty sites have no V to which the quantified assertion applies. No scheme, field, degree n or invertibility assumption is introduced.
- Existing-node audit: searched the complete DAG for 03CF and localization keywords, and the whole blueprint for localization (83 results) and "localization morphism sites" (zero results); none states the general slice-site theorem. Blueprint ancestor is lemma-weil-pbc-perfect-projection-formula. Read the relevant slopmaster2 site-source localization/Over search results; no exact finished declaration was found. The read-only archived master declarations are not used as finished proofs.
- Independent Mathlib audit: ran leanfinder "geometric morphism induced functor on over categories restriction sheaves", grep "mapSlice|slice.*[Cc]ontinuous|[Cc]ontinuous.*slice", and loogle '"Sheaf", "pushforward", "over"'; recorded actual results in searches.jsonl and the new node. overMap/overPullback concern one site's internal object morphisms; overPushforwardOverAdj assumes binary products and supplies a restriction adjunction, not the arbitrary-site inverse-image square. No Mathlib leaf.

Changes: clarified the new node's original exactness hypothesis; repaired its mathematical TeX and removed an unused definition dependency; replaced Step 3's unsupported tensor identification with explicit Hom adjunctions and coefficient/action checks; regenerated citations.json with one verbatim full statement for each cited node at each step; recorded independent searches. The first worker's sections are retained.

## Not duplicates (second-reader additions)
lem-weil-pbc-slice-site-localization vs lem-weil-pbc-etale-localization-exchange: the latter is a derived exchange theorem for scheme etale sites; the former constructs an arbitrary unringed slice-site morphism and its underived inverse-image square.
lem-weil-pbc-slice-site-localization vs lem-weil-pbc-ringed-projection-restriction: the latter concerns derived module operations and projection maps on pro-etale scheme sites; the former is the general underlying unringed slice-topos theorem.
lem-weil-pbc-slice-site-localization vs lem-weil-pbc-etale-resolution-section-canonical-whole-to-open: the latter is compatibility of resolution-section cohomology comparisons on scheme opens, not slice-site construction.
lem-weil-pbc-slice-site-localization vs lem-weil-pbc-limit-pullback-sections-colimit: the latter is a directed-limit theorem for sections on affine etale objects, not arbitrary-site localization.
lem-weil-pbc-slice-site-localization vs lem-weil-pbc-open-restriction-pullback-unit: the latter identifies units on etale sections for scheme open restrictions, not arbitrary-site localization.
lem-weil-pbc-slice-site-localization vs lem-sbc-restricted-comparison-generator-pullback: the latter identifies specified free-abelian generators under scheme pullback, not arbitrary-site localization.
lem-weil-pbc-slice-site-localization vs lem-weil-pbc-etale-restriction-pullback-unit-eq: the latter is an equality of homomorphisms with specified etale structure, not arbitrary-site localization.
