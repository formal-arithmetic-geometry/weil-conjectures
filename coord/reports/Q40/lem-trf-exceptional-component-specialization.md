# Worker report

1. Files written:
   - `dag/nodes/sec-trace-formula/lem-trf-exceptional-component-specialization.json`: existing statement, split into eight steps. Its statement, provenance, inherited searches and source metadata are retained.
   - `dag/nodes/sec-trace-formula/lem-trf-nodal-generic-component-closure.json`: new statement-only geometric lemma, unsplit, no Mathlib match. It concerns any smooth geometrically integral generic component in a proper curve with a nodal neighbourhood of its closure. It asserts flat finite-presentation closure and relative boundary/marking conservation, without exceptionality, contraction, genus zero or a two-point bound.
   - `citations.json`: whole verbatim statements for every cited node in every proof step, replacing the earlier attempt's truncated hypothesis fragments and invalid final literal newline escape.
2. Attachments: none. Searches of `WeilConjectures/` in the read-only slopmaster2 source by the blueprint tag and exceptional-component/specialization terms gave no exact declaration. A second search for generic-component closures and partial normalization also found no theorem giving the new lemma. No Lean was written or compiled.
3. WANTED: archival copy of Temkin, *Stable modification of relative curves*, arXiv:0707.3953v3, Lemmas 4.4.1--4.4.4 and Appendix B, for `lem-trf-exceptional-component-specialization`. The reference PDF is absent locally. I read the primary arXiv HTML version, https://arxiv.org/html/0707.3953v3, sections 4.4 and B. The old huji PDF URL timed out. The proof is therefore recorded as agent-written, with the missing relative-component argument made a separate statement rather than attributed verbatim to Temkin or Stacks.
4. Problems in the earlier attempt: Step 1 confused the closed modification locus in the target with its inverse image in the source. Step 2 obtained dimension but used it as if it gave flatness, finite presentation, and geometric reduction of the closure. Step 3 claimed projective preparation preserved the whole prescribed closure without locating its image. Step 4 asserted constant genus and a bound on boundary/marking points from whole-source perfect base change; that does not supply the relative component-closure and boundary assertions. It also applied the smooth-target contraction Euler-defect formula without a smooth target point. Step 5 said an arbitrary leaf has at most one external point, whereas one must choose an appropriate leaf. These assertions were replaced, not carried into the delivery.
5. Unfinished: the new geometric lemma is deliberately statement-only, to be split as its own stage-1 item. The eight-step proof uses exactly its stated conclusions. No item clause is postponed wholesale: the numerical calculation and choice of an exceptional component are in the item's proof.

## Searches and reuse

The sandbox initially contained the item and citations but no report or search log. Its existing eight Mathlib search records were retained, and their recorded results read: specializing maps lift points, normalization constructs normalizations, and Weierstrass reduction deals with elliptic equations; none says exceptional rational component specialization. The current repository has exactly the same item statement and those same inherited search records, and remains unsplit.

Before creating the new lemma I searched all DAG statements for persistent nodes, partial normalization, nodal component closures and specialization, and searched the whole imported blueprint with `tools/blueprint_refs.py search` for `component closure`, `persistent`, `partial normalization`, and `0CBY`. There is no existing relative closure statement. The ancestor command returns `lem-trf-local-term-locality`; the new node's via list prepends this item to the inherited list. I opened the related existing chart, subcurve, boundary, normalization, genus and Euler statements before distinguishing them below.

All five new Mathlib searches were actually made with the required msearch.py command and are recorded in searches.jsonl and copied with exactly the same tool and query to the new node: two LeanFinder formulations, LeanSearch, Loogle and source grep. All services answered. The first semantic searches returned smoothness/flatness/etaleness definitions and local smooth presentations; the second returned ordinary normalization maps and their universal properties. None is a relative component-closure theorem. Loogle's nodal results are Lagrange interpolation, as confirmed in Mathlib/LinearAlgebra/Lagrange.lean, lines 543 and 638. The normalization constructions were checked in AlgebraicGeometry/Normalization.lean, notably lines 127, 137 and 377. The AlgebraicGeometry source grep found no nodal family/partial-normalization/component-closure match. No Mathlib leaf is claimed.

## Not duplicates

lem-trf-nodal-generic-component-closure vs lem-trf-stacks-nodal-closed-subcurve: the latter is over one field and describes a given reduced subcurve; it asserts neither relative flat finite-presentation closure nor a finite etale boundary over a valuation base.

lem-trf-nodal-generic-component-closure vs lem-trf-valuation-smooth-branches-strict-chart: that statement gives local charts under smoothness of every fibre component; the new lemma does not assume that and concerns the closure of one generic component and its proper relative boundary.

lem-trf-nodal-generic-component-closure vs lem-trf-formal-local-structure-nodal-family: that is a completed local-ring model over a Noetherian base, not a proper component-closure or relative boundary theorem.

lem-trf-nodal-generic-component-closure vs lem-trf-ordered-nodal-branch-overlap: that compares ordered branch ideals on an etale overlap with nonzero smoothing parameter; it asserts no global closure, properness or boundary conservation.

lem-trf-nodal-generic-component-closure vs lem-trf-valuation-symmetric-nodal-blowup: that constructs a blowup making fibre components smooth near a chosen singular closure; the new lemma performs no blowup and does not claim all fibre components are smooth.

lem-trf-nodal-generic-component-closure vs lem-trf-complementary-pure-subcurve-components: that is a Noetherian single-scheme decomposition into reduced components; it has no relative nodal closure or etale boundary assertion.

lem-trf-nodal-generic-component-closure vs lem-trf-nodal-log-regularity: that constructs a log regular pair over a Noetherian log regular base, without the generic-component closure or conserved relative boundary.

lem-trf-nodal-generic-component-closure vs lem-trf-nodal-etale-chart: that gives local charts for a log regular Noetherian situation, not a proper generic-component closure over a possibly non-Noetherian valuation ring.

lem-trf-nodal-generic-component-closure vs lem-trf-nodal-subcurve-boundary: that describes the finite reduced boundary over one algebraically closed field; the new lemma includes flat finite-presentation closure and identification of the boundaries in all fibres by one finite etale scheme.

lem-trf-nodal-generic-component-closure vs lem-trf-nodal-family-etale-local-model: that is the general local nodal chart theorem. Such charts are an input for a later proof of the new lemma, but do not themselves assert global relative closure, properness or boundary conservation.

The duplicate gate also treats the 0707 in the arXiv identifier as a tag. I opened its listed records and distinguish them explicitly:

lem-trf-nodal-generic-component-closure vs lem-trf-exceptional-component-specialization: the item proves existence of a contracted projective-line component with at most two special points in a prescribed specialized fibre. The new lemma has no contraction map, genus hypothesis, two-point bound or exceptional conclusion; it supplies flat closure and boundary conservation, after which the item performs the Euler, connectedness, graph and leaf arguments.

lem-trf-nodal-generic-component-closure vs def-trf-birational-quasi-modification: this defines a separated finite-type generic-point condition, not a relative nodal closure theorem.

lem-trf-nodal-generic-component-closure vs def-trf-centred-valuation: this defines a morphism from a valuation spectrum centered at a point, without a nodal curve family or boundary assertion.

lem-trf-nodal-generic-component-closure vs def-trf-local-marking-length: this defines a local vector-space length of a marking at a field-valued point, rather than proving etaleness and conservation for a relative marking on a component closure.

lem-trf-nodal-generic-component-closure vs def-trf-modification: this defines proper birational modifications and their generic-base-change condition, whereas the new lemma has no modification morphism and proves relative closure properties.

lem-trf-nodal-generic-component-closure vs def-trf-multipointed-curve-modification: this defines morphisms, semistability, modifications and stability; it does not assert the closure theorem, and the new node does not duplicate these definitions.

lem-trf-nodal-generic-component-closure vs def-trf-multipointed-curve: this defines flat finitely presented curves with a flat marking; the new node proves those relative properties for a specified closure and its boundary.

lem-trf-nodal-generic-component-closure vs def-trf-multipointed-eta-modification: this defines compatible proper morphisms becoming isomorphisms generically, not properties of a generic-component closure.

lem-trf-nodal-generic-component-closure vs def-trf-nodal-dualizing-datum: this defines an invertible module and Jacobian normalization for dualizing data; the new lemma involves no dualizing sheaf.

lem-trf-nodal-generic-component-closure vs def-trf-projective-line-tree: this is a definition of a fibrewise rational tree over an algebraically closed field. The new lemma assumes no genus zero and concludes no tree or projective-line condition.

lem-trf-nodal-generic-component-closure vs def-trf-rational-rank: this defines the rationalized dimension of an abelian group and has no curve-closure content.

lem-trf-nodal-generic-component-closure vs def-trf-schematically-dense-open: this defines injective restriction of functions to an open; it proves neither finite presentation of a closure nor boundary conservation.

## Review by Q40

I read the chapter and unit records, SETUP's three blueprint levels, GOAL, dag-sync and delivery-errors B--E. I read Temkin Lemma 4.4.4 after its normalization reduction, its explicit reference back to Lemma 4.4.2, and the latter's compactification, connectedness and genus calculation, together with Appendix B. I retained the imported existence conclusion, normal-target hypothesis and nonempty specialized-closure condition; I did not replace existence by the source's stronger assertion about every component. This is below the same blueprint ancestor and uses its compactification/genus method.

For the new lemma I read Stacks curves.tex Tag 0CBY, label lemma-etale-local-structure-nodal-family, and Tag 0E38, label lemma-closed-subscheme-nodal-curve. I did not claim either tag already states this relative closure lemma. The intended local argument, for the next worker, is to use the smooth charts and uv=a charts: when a is nonzero in the valuation domain the generic chart is irreducible and the closure selects the entire chart; when a=0 a persistent boundary selects a single branch. The quotient for that branch is a polynomial chart over the base. Etale descent gives flat finite-presentation closure; its boundary charts are the persistent nodes, etale over the base. The closed boundary and the marking restricted to the proper closure are proper and etale of relative dimension zero, hence finite etale. The fibrewise identification then gives the count. This is a genuine relative geometric lemma, with no exceptional-component conclusion, and is not two lines of the cited fieldwise boundary theorem.

Step 1 uses the exact geometric-reducedness conclusion of the nodal-fibre node. The preparation statement gives finite normalization and the eta-normal node says a finite eta-modification of a geometrically reduced flat family is an isomorphism. The valuation base is normal by the monic-equation argument also written in Step 5. Normality of Y is therefore proved before applying preparation to a normal modification. The modification locus is in X, and only its closed inverse image contains W.

Step 2 uses the closure-dimension node only for its actual conclusion dim B=dim C, not flatness. A one-dimensional irreducible closed subset of a pure one-dimensional finite-type fibre is an entire component. The image of B in the quasi-finite target locus is one point. Localizing at t makes its fibre closed; shrinking about x and extending by the identity is exactly the diagram asserted by the preparation statement. Its closed support prevents the closure from escaping to the added compactification boundary. The interval ring is the quotient of V at p_t by p_s, a finite-height valuation ring, with fraction field kappa(s). The separably-closed-valuation node explicitly supplies that residue field's separable closedness. Only the local part of the original W_t is used; it contains B, and every component eventually chosen remains inside the original W_t.

Step 3 applies the base-change statement to preserve semistability and the smooth etale marking on this interval. The new node's properness, finite presentation, flatness, geometric reduction and nodal-neighbourhood hypotheses have been established in Steps 1--2. C is smooth geometrically integral because its geometric extension is a projective line. The new lemma explicitly supplies the relative closure and conserved boundary-plus-marking count, so those are no longer hidden in the Euler step. A smooth projective-line component has no self-node, hence its generic special points are exactly the boundary nodes and markings counted there.

Step 4 uses perfect direct image under its proper-finite-presentation and flat-sheaf hypotheses, now verified for H rather than guessed for a closure. I checked the cited node's arbitrary-base-change clause and the bounded finite-projective clause of the perfect-complex definition. The local-free node applies to its projective terms. The differential-rank cancellation is written out. The projective-line monomial statement at twist zero gives precisely H0 dimension one and H1 zero; the cohomological-dimension statement removes higher terms on the Noetherian finite-type curve. This proves chi=1 and does not assume an equality of genera without a family.

Step 5 checks every hypothesis of the normal-base connectedness statement: properness, integral normal base, reduced integral source with its generic point over the generic base point, and generic global functions equal to the base field. The last fact is exactly clause (2) of the proper-variety global-functions node. No normality of the source is required by that connectedness theorem.

Step 6 uses the nodal normalization node for smooth proper connected normalizations, the absence of other component singularities, and the smooth-locus isomorphism. Its Euler node states exactly chi=v-e-sum(g_i). The nonnegative-integer and spanning-tree calculation is explicit. Genus-zero smooth proper curves become projective lines by the cited genus-zero node; absence of loops removes self-nodes, so the components themselves, not only their normalizations, are projective lines.

Step 7 is elementary: one vertex has only its external points; otherwise a longest path supplies two leaves and the bound d<=2 guarantees a leaf with at most one external point. This corrects the earlier arbitrary-leaf assertion. Internal nodes plus the conserved ambient boundary and marking exhaust the special points.

Step 8 uses precisely the geometric-component bijection for geometrically reduced fibres over the separably closed residue field. This descends the chosen component, including its reduced structure. It then uses the already-established inverse image of the target modification locus to prove contraction; no closed-image hypothesis is added. citations.json contains the full statements, so the relevant conclusions and hypotheses can both be checked verbatim.

I tested the item on t=s, the height-zero base (no strict specialization), empty markings, a single rational tail, a chain with two external points, and a branched rational tree. In the last case an internal trivalent component need not be exceptional; the proof selects a leaf. For the new lemma the local tests are a smooth chart, uv=a with a nonzero smoothing parameter, and uv=0 with one selected generic branch. These give the claimed flat model and distinguish an intrinsic special node from a persistent boundary. A cusp and a nonflat vertical component fail the hypotheses and are not included. No non-elementary proof step exceeds 2000 characters. The generic tools from other units are declared in split_report.tool_uses, and there is no SGA source or compiler invocation.
