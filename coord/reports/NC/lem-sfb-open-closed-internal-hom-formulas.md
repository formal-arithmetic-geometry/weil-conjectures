# Stage-1 report: lem-sfb-open-closed-internal-hom-formulas

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-open-closed-internal-hom-formulas.json`: statement; split into 11 proof steps using 27 existing nodes. Mathlib verdict: no match for the two formulas; no new nodes and no new Mathlib leaves.
- `citations.json`: one verbatim statement quotation for every node cited by every numbered step. Whole statements are quoted so the qualifying hypotheses stay visible.
- `searches.jsonl`: genuine msearch queries and returned declarations. The JSON retains inherited searches and appends only searches actually run in this sandbox.
- `write_split.py`: sandbox-only preparation script; no Lean or project tools modified.

## Attachments

None. I searched the slopmaster2 project source for the blueprint tag and the Hom/open/closed notions. The pro-etale Derived/Hom file defines the closed internal Hom and tensor adjunction, not either immersion formula. No project declaration located states every clause of this item. The initially missing node appeared during shared-repository synchronization; there was no previous sandbox node/report to resume.

## Literature wanted

None.

## Corrections and scope

The statement is true with the stated quasi-compact open complement. I kept its statement and statement dependencies unchanged, including the ordinary uncompleted unbounded coefficient categories. No STATEMENT-DISPUTED and no hypothesis added. The new proof fills the initially empty proof, records the exact union of step citations and declares off-unit generic tools in `split_report.tool_uses`. Maintainer-owned chapter, unit, ancestry and all other imported fields are preserved. This is a child supporting the coefficient-continuity proof, not the key node of the restricted-functors unit; no unit realization was changed.

The main subtlety is totalizing unbounded complexes on an arbitrary scheme. The existing locally closed projection node `det-lem-int-tensor-projection` assumes the standing finite-type setting and its proof uses qcqs to obtain closed direct-image coproducts. It cannot be cited here for its statement. Instead I prove the needed sheaf projection maps and totalization arguments as steps. The existing support adjunction makes i_* a LEFT adjoint on sheaves, so the colimit-preservation theorem gives its coproducts under exactly the item's hypotheses. This avoids silently adding qcqs. I do not use the bounded-below condensed recollement statement for an unbounded complex.

The source points to the formal calculation inside Bhatt–Scholze Lemma 6.7.13, not its constructible-preservation assertion. I explicitly expand that calculation, and its open counterpart, by testing against every derived module T. The inverse representing morphisms and evaluation normalization are written out, so the result is an internal sheaf-valued derived Hom formula. No SGA source or trace/purity route is used.

## Not duplicates

No new nodes. The whole-DAG keyword searches and blueprint_refs searches for internal Hom, projection, j_!L and i_*P were read. Existing projection statements either concern abelian sheaf tensor alone or impose the standing scheme/finiteness conditions. The support-adjunction node states the sheaf and derived adjunction but explicitly does not identify internal Hom sheaves on different sites. No blueprint node located states both formulas with this generality. The existing generic interfaces are reused directly; none was copied into a new node.

## Review by NC

I read the item and its provenance, the current chapter `sec-six-functors-basics`, the restricted-functors unit, the current derived-tensor-Hom section, and the ancestor's final coefficient-localization sentence. The child's original `from.place` already names the precise coefficient-continuity use; I retained it. The chapter's distinction between internal modules over the actual pulled-back condensed ring and sheaves valued in a fixed module category is respected throughout. The ancestor proof's finiteness references are not invoked by this formal child.

For the mathematical source I read Bhatt–Scholze Lemma 6.7.13 and its proof (printed p. 57), and the neighboring projection calculation in Lemma 6.7.14. Their actual constructibility/excellence assumptions are not imported into the purely formal argument. I read Stacks proetale.tex Tags 09AA (lemma-closed-immersion), 09BM (lemma-closed-immersion-complement-retrocompact-exact), 09BN (lemma-open-immersion), and 09AH (lemma-ses-associated-to-open); sites-modules.tex Tag 03EL (lemma-tensor-product-pullback), including its balanced bilinear universal property; sites-cohomology.tex Tags 06YS (lemma-K-flat-resolution), 0G7D (lemma-factor-through-K-flat), 08J9 (lemma-internal-hom), and 08JB (lemma-restriction-RHom-to-U); and derived.tex Tag 08BJ (lemma-adjoint-preserve-K-injectives). The proof uses the derived closedness interface rather than an unproved closed-slice restriction of internal Hom. There are no new-node sources to review.

I opened and read the statement of each of the 27 cited nodes. The per-step checks were:

1. The module-object action equations, relative tensor coequalizer, and sectionwise-module definitions give exactly the action and balancing identification written out in the step. The sheaf-tensor node supplies the sheafified tensor, and the pulled-coefficient node gives commutativity. `lem-sfb-alpha-iso` applies to every condensed ring and every scheme map, unlike an admissible-coefficients-only statement. The definitions of module pullback, pushforward, linear extension, and open extension specify their precise actions, so the comparison does not replace Lambda_X by Lambda(*).
2. `lem-weil-pbc-proetale-ringed-open-closed` states exactness, both own-locus identities, both complementary vanishings and the full localization sequence for a quasi-compact open complement. The immersion-limit node states exactness with an inverse-image coefficient ring and transport along an isomorphism. These statements supply all the facts used; detection follows by kernels and cokernels and the displayed sequence. Its separate qcqs filtered-colimit clause is not used.
3. The pullback-tensor node states the relative tensor comparison for small ringed topoi with any ring map, and the module upper/lower-adjunction node supplies the closed unit and counit. The open adjunction and zero restrictions have already been established in step 2. The two maps are written explicitly and each is checked on both restrictions; this is an elementary consequence, rather than a new projection-formula node.
4. Clause (1) of the support-adjunction statement says Gamma_Z is right adjoint to i_* on module sheaves. The ringed-site Grothendieck statement gives all small colimits, and the left-adjoint-colimits statement applies to an arbitrary small diagram. Thus all four functors preserve the degreewise coproducts. In particular I checked that no global qcqs assumption entered here.
5. The total-tensor definition states direct sums over p+q=n and the differential sign (-1)^p. The comparisons from step 3 commute with each differential by naturality, and step 4 permits summing. Both signs of the symmetry are checked, not hidden in a claim about transport.
6. The K-flat definition quantifies over every acyclic complex, exactly the tests written in this step. Flat sheaf modules are defined by exactness of tensor. The acyclicity and flat-term preservation arguments explicitly use only the already proved exactness, projection comparison, and re=1. This is elementary and is not made into a node.
7. The K-flat-resolution statement gives flat-term models for arbitrary complexes on a ringed site. The exact-functor statement gives their termwise derived images. The descent node supplies the equivalence of the localized flat-term K-flat category with D(R) and the derived tensor computation. I apply the equivalence separately on each site; I do not misapply its same-ring bifunctor clause. The homotopy signs and inverse quasi-isomorphism naturality show that the projection isomorphisms descend naturally.
8. The module-derived-pushpull statement gives Lf^* adjoint to Rf_* on unbounded categories for all commutative condensed rings. Exactness from step 2 and the exact-functor interface identify the exact derived functors. The support-adjunction statement's clause (2) gives i_* adjoint to RGamma_Z without boundedness. The termwise-homotopy-adjunction statement gives the actual open unit, counit, and triangle identities, so their descent establishes the unbounded open adjunction and its normalization.
9. The derived-tensor-Hom statement defines the INTERNAL right adjoint with no finiteness condition. The five natural Hom bijections use that statement and the projection and derived adjunctions already proved in steps 7–8. They are valid for every T, L, N, not merely degree-zero modules or global sections of the coefficient unit.
10. The same closedness interface and the closed projection, support, and ordinary pullback/direct-image adjunctions give each line of the closed calculation. Ri^! is exactly RGamma_Z from clause (2) of the support node. Since i_* is exact under the quasi-compact-complement assumption, no Ri_* or extra resolution is inserted.
11. Natural representability is proved by evaluating the bijection and its inverse at identity morphisms. Its naturality then gives fg=1 and gf=1 and the source/target functoriality. I traced evaluation through every tensor comparison and adjunction transpose, including the direction of the inverse projection comparison, so the maps agree with the prescribed units and counits, not just some abstract isomorphism.

I tested the edge cases: zero coefficient ring and empty X give zero categories; with U empty the closed unit/counit calculations give the identity formula, and with Z empty the open calculation gives the identity formula. If the closed immersion is a nilpotent thickening with empty complement, the argument uses i^*i_*=id and the localization sequence, not an equality of schemes. With an arbitrary nonperfect or torsion source nothing in the K-flat tests or Hom chains needs finite rank or dualizability. Arbitrarily negative and positive complex terms are handled by the explicit coproduct totalization; no bounded-below resolution has slipped in. Arbitrary non-qcqs X is allowed because the coproduct proof uses the support adjunction, and the only scheme finiteness condition is the one already assumed on j.

Mathlib searches were run through msearch in this sandbox with two semantic phrasings, a valid quoted-name Loogle query, LeanSearch, and two source grep patterns. I read the returned general closed-monoidal evaluation/coevaluation and ordinary sheaf pullback/pushforward adjunction candidates. `CategoryTheory.ihom.adjunction` and its evaluation are the generic closedness API, not either immersion formula. I read Mathlib/CategoryTheory/Monoidal/Closed/Basic.lean at these definitions. The second semantic result is retained in searches.jsonl; it returns generic evaluation/coevaluation and internal-precomposition declarations. No service outage was recorded as absence. No unsupported new Mathlib leaf was declared.

A read-only traversal of the actual statement/proof dependency lists found no path from the proposed dependencies back to this item and no merged citation. Required check_dag/review_split/preflight validation is run by the delivery dry run on the server, never by invoking those scripts on this machine.

The first server preflight returned one B2 wording diagnostic in step 4: the phrase "the item's hypotheses". I replaced it with the explicit closed immersion, quasi-compact complementary open immersion, and coefficient ring already introduced in the node. No mathematical dependency or statement changed. The next dry run validates this repair.

## Unfinished work

None in the one-level mathematical split. Existing cited nodes retain their own queue status and are not split or modified by this delivery. The second reader independently reviews this sandbox and performs delivery after the required successful dry run.

## Second reading by NC

- Item statement: compared every coefficient, immersion, quasi-compactness, site-size, unbounded-derived, and naturality clause with the imported node and the formal calculation in Bhatt--Scholze Lemma 6.7.13; zero ring, field, empty scheme, empty open, and empty closed cases agree.
- Step 1: checked the module-object actions, balanced relative tensor, coefficient transport, and derived tensor identification against all cited definitions; added the missing explicit citation to `sk-def-sfb-derived-tensor-hom`.
- Step 2: checked exactness, localization, vanishing restrictions, inverse-image exactness, and detection of isomorphisms against the two cited pro-etale nodes; the quasi-compact complement is the only finiteness used.
- Step 3: checked both projection maps against the pullback-tensor and adjunction statements; corrected the closed map to be the counit map `i_*(G tensor i^*M) -> i_*G tensor M`, then inverted it after the detector proves it is an isomorphism.
- Step 4: checked coproduct preservation from the four displayed adjunctions and Grothendieck colimits; no ambient qcqs assumption is introduced.
- Step 5: checked totalization coproducts, differential signs, symmetry, and pullback tensor comparison against the tensor-complex and ringed-topos nodes; added the explicit pullback-tensor citation.
- Step 6: checked both K-flat and flat-term preservation tests using exactness, projection, and the definitions; arbitrary unbounded complexes remain covered.
- Step 7: checked K-flat representatives, exact derived functors, localization descent, and two-site naturality against the resolution, factorization, and tensor-descent statements.
- Step 8: checked the unbounded open, pullback, and support adjunctions and their units/counits against the derived-pushpull, support, and termwise-adjunction nodes.
- Step 9: checked each open Hom bijection against closedness and the preceding projection and adjunction steps for an arbitrary test object; marked this substantive calculation non-elementary.
- Step 10: checked each closed Hom bijection and the exact direct-image endpoint against the same closedness and adjunction data; marked this substantive calculation non-elementary.
- Step 11: checked the Yoneda representability, inverse maps, evaluation normalization, and three-variable naturality; the identity-and-inverse argument is elementary once the displayed bijections are established.
- New nodes: none; every supporting fact was searched for and reused from an existing DAG node, so B1--B7 introduce no new node to audit.

Changes made: repaired the closed projection-map direction, added two omitted proof citations, marked the substantive multi-line projection and Hom calculations non-elementary, and corrected the inherited `created.item` and group metadata from the parent NV split to this NC item. No target statement was changed.
