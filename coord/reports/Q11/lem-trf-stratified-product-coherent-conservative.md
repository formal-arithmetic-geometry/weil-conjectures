# Worker report — repair of returned head 43716514d6

Files written:
- `dag/nodes/sec-trace-formula/lem-trf-stratified-product-coherent-conservative.json`: repaired split, six proof steps; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-finite-coproduct-topos-coherent.json`: one new statement-only node for the finite coproduct of Grothendieck topoi, its geometric morphisms, and componentwise coherence; no Mathlib match.
- `citations.json`: one verbatim statement quotation for every dependency cited in every proof step.

Attachments: none. I searched the read-only `WeilConjectures/` sources in both checkouts by the exact blueprint tag, the item id, and the coproduct/coherent-topos/stratified-product notions. There is no project declaration stating this item or the new lemma. The hits concerned coproducts of sheaves inside a single category, coherent structure-sheaf modules, and unrelated coherent topologies.

WANTED: Orgogozo, “Modifications et cycles proches sur une base générale”, author draft §8.1, printed p. 17, for lem-trf-stratified-product-coherent-conservative. No draft was downloaded or used as if it were present. The local source actually read for the oriented-product argument is ILO XI 1.4, 1.6, 1.8–1.9 and the proof of Lemma 2.5, particularly printed pp. 178–179 (PDF pp. 184–185).

The mathematical assertion is unchanged. The statement now introduces the two maps defining each oriented product, its induced morphism to V_f, and the finite coproduct morphism by the appropriate nodes. “Noetherian” is expanded to the same locally Noetherian plus quasi-compact condition. This is a repair of missing definitions and proof dependencies, not a weakened statement or a new reducedness hypothesis. The previous report is preserved in `report.previous.md`, and historical Mathlib searches remain in `searches.jsonl` and in the item. The current shared item was compared with the retained copy; its maintainer metadata and original source are retained. Its existing unit is `sk-i-curve-zero`, whose chapter and unit records I read; the inherited ancestry through `lem-trf-local-term-locality` is retained, and I changed no unit or chapter binding.

What was wrong, and how each returned point was repaired:
1. The statement attributed a two-map oriented product to a definition of only the vanishing topos and used an undefined coproduct of topoi. It now uses `lem-trf-oriented-product-universal` for P_{αβ} and its induced map, and the new generic lemma defines the disjoint-union site, coproduct topos, inclusions and morphism u.
2. Internal finite extensivity does not describe a coproduct of topoi. That citation is removed. Step 2 proves coherence of the components and target; step 3 uses the new lemma to establish the coherent source and componentwise coherent objects before applying the morphism criterion. This addresses both previously unchecked hypotheses.
3. The module-conservativity node does not state that all points are triples. Step 4 derives that fact from the universal property and the geometric-etale-point theorem, retaining the structural 2-arrow. Step 5 factors each field-valued geometric point through its stratum by the quotient R/I calculation; no factorization of an arbitrary scheme merely from its image is asserted.
4. The old conclusion changed coefficients from set sheaves to modules. Steps 4 and 6 use `lem-trf-finitary-site-enough-points`, whose statement explicitly detects isomorphisms of set sheaves. Step 6 is marked non-elementary because it applies that theorem. No module or derived conservativity is used anywhere.
5. Step 1 establishes Noetherianity of the strata via their closed-into-open factorization. Step 2 explicitly applies the qcqs-morphism permanence lemma to their maps to S, and writes the finite-family pretopology argument from XI 2.5. The proof origin now names the local ILO PDF and is marked agent-written.

Nothing mathematical remains unfinished in the split. The new generic lemma deliberately remains unsplit, with no proof steps, proof dependencies or proof sketch in its statement. No Lean was written and no Lean compiler, Lake or build tool was run.

## Route-pivot/A6 resubmission verification

I read the current dropped-machinery inventory in `coord/route-pivot-dropped.txt` (the 2026-10-18 ordinary-derived route pivot). I compared every active `stmt_deps`, `proof_deps`, and proof-step `uses` in the repaired item, and the active statement dependencies of `lem-trf-finite-coproduct-topos-coherent`, with that inventory: the intersection is empty in both nodes. The active proof uses only the finite-site, etale-point, oriented-product, Noetherian/qcqs, and set-sheaf statements listed in the repaired JSON. No infinity, dg, model-category, rectification, coherent-section, straightening, or operadic node is reintroduced.

There is no item-specific route-pivot repair note at `coord/repair-notes/lem-trf-stratified-product-coherent-conservative.json` in the current shared snapshot. Consequently there are no named pre-pivot steps or machinery children that this resubmission is required to retain. The generic route-pivot inventory was still checked explicitly as recorded above.

For the historical comparison, I used the retained returned version identified in the return as head `43716514d6`, together with `report.previous.md`, and compared it with the repaired files delivered here (the prior delivery head was `ab097a9dc9`). The returned version had no independent finite-coproduct-of-topoi node, attributed the two-map oriented product to the wrong definition, cited internal finite extensivity for a coproduct of topoi, and used an unqualified module-conservativity conclusion. The repaired version adds the statement-only coproduct-topos/coherence node, names both oriented-product maps and the induced morphisms, supplies the Noetherian/qcqs and finite-pretopology checks, derives point triples from the universal property, and applies enough points only to set sheaves. The six-step item assertion is unchanged. This is a substantive repair of the returned split, not an unchanged resubmission.

## Review by Q11

I read the full item, the parent `lem-trf-coherent-set-criterion`, the sibling `lem-trf-proper-base-change-coherent-conservative`, and the statement of every dependency used in the repaired six steps. I read ILO XI 1.8's explicit “Tout point ... est de cette forme” and XI 2.5's Cov(Z) construction, including why finite composites and base changes form the finite-family pretopology. For the new generic lemma I read Stacks sites.tex 00VH (definition-site), 00VM (definition-sheaf-sets), 00W2 (lemma-limit-sheaf) and 00WI (lemma-colimit-sheaves), and the explicit coherent-object definition in `def-trf-coherent-topos`. The new source field describes this as an agent formulation from those tools; it does not pretend Stacks states a named coproduct-coherence theorem there. The quotient-algebra input was checked in morphisms.tex 01QO (lemma-closed-immersion) and finite-type Noetherianity in 01T6. Geometric points of the etale topos were checked against etale-cohomology.tex 04HU; enough points against the exact set-valued statement of the existing 00YQ node.

In step 1, `def-weil-pbc-scheme-conventions` supplies the finite-presentation hypothesis, and the finite-type Noetherian theorem supplies Noetherian X. The closed-immersion definition really gives the required closed-into-open factorization and affine quotient R/I, so the same theorem applies to the closed stratum over its Noetherian open. The open-subscheme node gives Noetherian O, and the locally-Noetherian quasi-separatedness node gives the qs assertions. Thus I have not inferred qcqs just from the word “stratum.”

In step 2, clause (1) of `lem-weil-pbc-qcqs-morphism-permanence` states both morphism properties used, with precisely the qc-source/qs-target hypotheses now established. I checked the actual triple-presentation statement for finite limits, finite generating families, finite covering refinements and the site equivalence. Closing those generating families under base change and finite composition leaves their index sets finite; I included this argument to meet the finite-pretopology hypothesis of the coherent-generators statement. Its coherent-generator and coherent-topos conclusions are both expressly in that statement.

In step 3, the new lemma provides the coherent source and componentwise test, rather than the former internal-extensivity citation. I checked the triple-presentation base-change clause with a=i_α, b=1_S and d=j_β: its middle object is V, not a base change to S_β; its other components are U×_X X_α and W×_S S_β. Its statement asserts the inverse-image isomorphism and that this is a triple in the component site. The coherent-generators node then supplies coherence of each associated representable and the morphism criterion, with both topoi coherent before that criterion is applied.

In step 4, the enough-points statement is for sheaves of sets and requires only the finite-limit finite-refinement site already available. The etale-point theorem supplies representatives for the two projection points, and the universal property, with source Set, supplies both existence and uniqueness for the triple including its 2-morphism. I no longer borrow the proof of the module-conservativity node.

In step 5, the stratification definition says its finite strata partition the underlying space and have immersion structures. For a geometric point over the chosen stratum, I checked the actual algebra map R→Ω: its kernel is the image prime, so the stratum ideal I lies in the kernel and the map factors through R/I. The domain Spec Ω is reduced; the proof does not assume the stratum reduced, and it does not assert the false image-containment factorization for arbitrary source schemes. The closed set-stalk theorem `lem-weil-pbc-sets-etale-inverse-image-stalk-germ` gives exactly the comparison for the images of the two lifted points; its unique germ formula also verifies naturality of these comparisons. The universal property then identifies the composite point, not merely its projections, and the new coproduct lemma supplies its component inclusion.

In step 6, the composition clause in the geometric-morphism definition gives z^{-1}a ≅ ztilde^{-1}u^{-1}a. I checked that the enough-points node concludes that this a:F→G of SET SHEAVES is invertible. The coherent-topos definition uses that same category for conservativity. The final step is marked non-elementary, and there is no change to constant-ring coefficients along the way.

I checked the new statement independently: sheaves and transformations on the disjoint-union site restrict to tuples, because there are no arrows or covering conditions between different components. The two displayed adjoints satisfy Hom((u_i^{-1}A)_i,(B_i)_i)=product_i Hom(A,u_{i,*}B_i)=Hom(A,product_i u_{i,*}B_i). For a finite product of sheaf categories, an object is quasi-compact precisely when its components are: a cover is componentwise epic, and finitely many indices suffice in each component, hence in their finite union; conversely extend a component cover by identities in other components. Pullbacks are componentwise, and testing with objects concentrated in one component gives the quasi-separatedness equivalence. A small family of coherent generators concentrated in the components, enlarged by their finite-limit closure and the terminal tuple, generates the product. This verifies coherence of the source; it is a generic topos fact strictly below the geometry of the item, not a renamed clause about stratified oriented products.

Small cases checked: I empty (the sheaf category on the empty site is degenerate), I singleton (the construction is the original topos), E_1=E_2=Set (coherent objects are pairs of finite sets), a degenerate component, and an infinite set in one component (not coherent). Finiteness of I is essential: infinitely many nonempty components do not give a quasi-compact terminal tuple. For the item I checked trivial one-stratum partitions, X=S=Spec k, X or S empty, empty strata, and a nonreduced ambient scheme or stratum. The field-valued quotient argument works equally in the nonreduced case. The identity-stratification case gives the identity morphism, as expected.

I searched the whole DAG and imported blueprint by “coproduct,” “coproduct of topoi,” “product of topoi,” the componentwise/coherent phrases and the source tags. I read the related diagram-site realization statement: it concerns a diagram of sheaves on one fixed site and does not assert componentwise coherence of a finite coproduct of different topoi. The Mathlib hits were read at their printed signatures and in Sites/LeftExact.lean:313–329 and Sites/Limits.lean:205–230; they assert internal finite coproducts and extensivity, not this generic lemma. Five searches for the new lemma, including a second semantic phrasing, are recorded exactly as run in the authorized item's log. The item has its retained searches plus the new phrasing. The Loogle unknown-identifier results are recorded as unavailable, not evidence of absence. All six non-elementary steps are under 2000 characters; none hides a longer auxiliary comparison.

## Not duplicates

lem-trf-finite-coproduct-topos-coherent vs lem-trf-coherent-epimorphic-quotient: a coherent quotient of one object inside one topos; it does not construct coproduct topoi or give componentwise coherence.

lem-trf-finite-coproduct-topos-coherent vs lem-trf-set-sheaf-finite-extensivity: coproducts of objects inside a single topos; it does not concern coproducts of topoi.

lem-trf-finite-coproduct-topos-coherent vs lem-weil-pbc-site-equivalence-is-morphism-of-sites: transport along a cover-preserving equivalence, not a product of different sheaf categories or coherent objects in it.

lem-trf-finite-coproduct-topos-coherent vs def-weil-pbc-etale-sheaf-of-sets: defines sheaves on a scheme etale site; no coproduct-topos or coherent-object conclusion.

lem-trf-finite-coproduct-topos-coherent vs def-weil-pbc-finite-precoverage: defines finite-family stability conditions, not coproducts of topoi.

lem-trf-finite-coproduct-topos-coherent vs def-weil-pbc-sites-and-cohomology: defines sites, sheaves and cohomology, but has no finite-coproduct-of-topoi coherence theorem.

lem-trf-finite-coproduct-topos-coherent vs lem-weil-pbc-sheafification-exact: exactness of sheafification of abelian presheaves on one site, not the coproduct of topoi.

lem-trf-finite-coproduct-topos-coherent vs lem-weil-pbc-sheaf-algebraic-structures-objects: algebraic objects in one sheaf topos, not coherent objects in a finite coproduct of topoi.

lem-trf-finite-coproduct-topos-coherent vs lem-weil-pbc-site-system-finite-coverings: cover transport under equivalence, not coherent objects in products of sheaf categories.

lem-trf-finite-coproduct-topos-coherent vs def-weil-pbc-indexed-covering-class: defines covering classes and axioms; no topos coproduct or coherence assertion.

lem-trf-finite-coproduct-topos-coherent vs lem-weil-pbc-presheaf-finite-limits-objectwise: limits within presheaves and sheaves on one site, not componentwise coherence across different topoi.

lem-trf-finite-coproduct-topos-coherent vs lem-weil-pbc-finite-presieve-filtered-colimit: commutation of a filtered colimit with a finite sheaf condition; no coproduct of topoi.

lem-trf-finite-coproduct-topos-coherent vs aux-weil-pbc-affine-sections-colimit: evaluation of filtered colimits on an affine etale site; no finite-coproduct topos.

lem-trf-finite-coproduct-topos-coherent vs lem-weil-pbc-site-covering-isomorphic-family: transport of a covering family by object isomorphisms, not construction or coherence of a coproduct topos.

lem-trf-finite-coproduct-topos-coherent vs lem-weil-pbc-site-sheaves-enough-injectives: enough injectives for abelian sheaves on one site, not coherent set objects in a coproduct topos.

lem-trf-finite-coproduct-topos-coherent vs lem-weil-pbc-sheaf-coproduct-finite-subcoproducts: filtered union of internal sheaf coproducts on a topological space, not coproducts of topoi.

lem-trf-finite-coproduct-topos-coherent vs lem-weil-pbc-site-sheaf-sets-limits-sectionwise: sectionwise limits on a single site, not componentwise coherence across topoi.

lem-trf-finite-coproduct-topos-coherent vs lem-weil-pbc-site-system-finite-sheaf-transport: exactness of transported inverse images, not construction or coherence of finite coproduct topoi.

lem-trf-finite-coproduct-topos-coherent vs lem-weil-pbc-site-equivalence-morphism-transport: transport of one site morphism through equivalences, not a coproduct topos or componentwise coherence.

lem-trf-finite-coproduct-topos-coherent vs lem-pur-tate-inverse-limit-base-change: a coefficient-tower comparison morphism and its tensor compatibility; no coproduct-topos construction or coherence.

lem-trf-finite-coproduct-topos-coherent vs cohomology-site-equivalence-covering-iff: cover preservation/reflection for a site equivalence, not a finite coproduct of topoi.

lem-trf-finite-coproduct-topos-coherent vs lem-weil-pbc-diagram-site-realization: diagrams of sheaves on one fixed site are treated there; componentwise coherence of a finite coproduct of different topoi is not stated.

lem-trf-finite-coproduct-topos-coherent vs lem-trf-stratified-product-coherent-conservative: the new lemma has no schemes, strata, oriented products, point lifting or conservative-cover conclusion; the six geometric proof steps remain in the item.
