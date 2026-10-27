# Stage-1 delivery: lem-sfb-space-fibrewise-lci-source-locus

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-fibrewise-lci-source-locus.json — statement, split; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-lci-etale-pointwise-invariance.json — statement-only, unsplit; no Mathlib match. This is invariance of complete-intersection local rings under an etale map of schemes over a field, not existence or base change of a source locus.
- citations.json — a verbatim statement quotation for each of the 21 citations in the six item steps.
- searches.jsonl — actual msearch logs; all services answered. Existing item searches were retained and the current searches appended. New-node searches include two semantic phrasings, LeanSearch, Loogle and two source greps.

## Attachments

None. Searched lean/WeilConjectures by the exact blueprint tag and syntomic/fibrewise-lci concepts, and by complete-intersection/etale concepts. The hits are ring-theoretic presentation lemmas, not the algebraic-space theorem or the new pointwise invariance statement. No Lean was written or compiled.

## Wanted literature

None. All source material used is already in literature/stacks-project. No SGA source is used.

## Corrections and limitations

The item statement is unchanged: neither closedness nor properness is added, and the result concerns the full lci locus, with no fixed dimension or nodal restriction. The original node had no proof. It cited the general Koszul-locus theorem 06CA; the split supplies the actual atlas argument and its fibre interpretation rather than citing that tag as a proof.

The inherited blueprint ancestor is null, as tools/blueprint_refs.py ancestor reports. This is retained, together with the inherited via chain and exact alteration/isolated-lci supporting place. The newest blueprint was read in literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/ (direct-images proof). Blueprint searches for syntomic, complete intersection, complete-intersection, etale complete intersection, 036S, 01UE and 03BZ gave no matching blueprint statement; the broader etale search was also inspected. The inherited historical supporting place remains the location of this auxiliary algebraic-geometric input, without claiming that the current direct-images proof itself states it.

Nothing mathematical is left unfinished in the item's assembly. The new child is intentionally unsplit, as the one-level split contract requires. Its prospective proof is recorded below as guidance, not inserted in its statement or proof fields.

## Review by Q74

I read spaces-more-morphisms.tex Tag 06CA with its proof: it constructs an open from the Koszul locus and compares it on pulled-back scheme atlases; specializing the intermediate and target spaces to the scheme base gives the intended setting. I checked Tag 06C9's flat-lci interpretation and morphisms.tex Tags 01UE (pointwise syntomic criterion), 01UF (flat lfp with lci fibres), 02V3 (the exact scheme source locus and arbitrary base change), and the affine/local-ring equivalence 01UG carried by the existing pointwise-criterion node. I also read spaces-properties.tex Tag 03BZ with its invariant-open quotient proof, spaces.tex Tag 02WU's hypotheses and construction, and descent.tex Tag 036S with its proof references. These are the sources for the item and the one new node.

For step 1, I opened def-trf-algebraic-space: it gives a representable surjective etale scheme atlas. The local-properties-chart-test statement explicitly includes the case that the target is a scheme. The scheme syntomic-locus node explicitly states openness for flat lfp maps, its fibre-local-ring membership test, maximality and arbitrary base change; I use exactly its openness and membership clauses here. Local finite presentation implies local finite type, so its finite-type hypothesis holds. No quasi-compactness of an atlas is assumed.

For step 2, the algebraic-space definition and space-fibre-products-etale-covers give scheme overlaps and etale projections. On each residue-base fibre they are etale scheme maps, and all schemes concerned are locally of finite type over that field. The new child states precisely preservation and reflection at corresponding points, in both directions; it is not a definition of lci used as a theorem. Applying it to both projections makes the two inverse-image opens equal. This is the substantive previously missing chart-compatibility fact, now explicitly exposed as a node.

For step 3, I read the entire statement of etale-open-chart-morphism-descent. It requires an invariant open in a surjective etale atlas and a map agreeing on the restricted relation. The previous step establishes invariance; the map to S agrees because both projections compose to the same structural map. The lemma gives the open and its precise scheme-test characterization, not merely an unspecified quotient. For any additional chart V the overlap W is a scheme, both projections are etale, and W -> V is surjective. The same new pointwise invariance lemma and the scheme locus membership clause identify both inverse-image opens on W. The descent lemma's stated uniqueness on scheme tests then gives the required chart formula. This comparison does not assume that V -> X is surjective.

For step 4, the lci-pointwise-criterion statement equates the local-ring condition with an affine open cover by spectra of finite type lci algebras. Thus it supplies exactly the bridge from the scheme-locus statement to the item's field-fibre definition. Base-changed etale charts cover each fibre by space-fibre-products-etale-covers. For any other open A satisfying that definition, its pullback to P has only good fibre points, and hence lies in L. Surjectivity of the atlas yields the inclusion on point images; point-open-calculus explicitly reflects that inclusion as inclusion of open subfunctors. No factorization through an arbitrary locally closed stratum is inferred merely from a point image.

For step 5, I opened both scheme permanence nodes. Flat-morphism-base-change gives flatness for every scheme base change. Qcqs-morphism-permanence clause (3), independently of clauses (1)-(2), gives stability of local finite presentation; it has no quasi-separatedness hypothesis for this clause. The chart-test statement transfers those two properties to the space map f_T. The scheme-locus theorem then gives L_T = L x_S T for arbitrary T -> S. Both claimed opens have this exact pullback on the same surjective atlas; the open-descent uniqueness statement, rather than a presumed point-lifting argument for a non-surjective base change, proves equality.

Step 6 is elementary from the proved fibre property and maximality. I tested empty source, empty base and empty fibres: the statements and construction are vacuous where appropriate and the unique empty open is returned. I tested a smooth affine line (all points good), a disjoint union of a smooth family and a non-lci fibre (the good component survives), an etale chart missing the bad component (the chart formula uses inverse image), and base change landing only over good fibres. Reflection in the new node is asserted only at an actual point z of an etale source, not at every point of Y when e is not surjective. No perfectness assumption on k is used.

The new node's proof route is smaller than the item's theorem. Over a field, pointwise lci is the pointwise syntomic condition by 01UE. Syntomic is local in the syntomic topology on the source by 036S, in particular for etale neighbourhoods; etale maps are open. An etale neighbourhood on which the source structural map is syntomic therefore descends this property to its open image. Conversely precomposition with an etale morphism preserves syntomicity. This gives preservation and reflection at a chosen point. This proof guidance is left here for its future worker, not supplied as a fake proof in the unsplit child.

I checked delivery-errors B-E: the new statement introduces every object and uses definition nodes with the right meaning; source places are tags and labels; no proof is hidden inside its statement; searches are exactly those actually run; every citation is a statement citation and has a verbatim quotation; no elementary union or inclusion fact was promoted to a new node; the new child does not state existence, maximality, chart formula, or arbitrary-base-change of the item's locus. No step exceeds 2000 characters, and the base-change comparison is written out. The DAG, blueprint and Lean searches found no duplicate of the new child. Off-unit scheme-locus, pointwise-criterion and open-descent results are declared as generic tool uses, preserving the inherited alteration route.

## Not duplicates

lem-sfb-lci-etale-pointwise-invariance vs lem-trf-syntomic-pointwise-local-model: the existing statement constructs a relative global-complete-intersection presentation near a flat finitely presented fibre point; the new statement compares local rings at corresponding points of an etale map over a field and includes reflection. It does not construct such a presentation.

lem-sfb-lci-etale-pointwise-invariance vs lem-trf-syntomic-locus-base-change: the existing statement constructs and base-changes a source locus under change of the base scheme; the new statement concerns change of an etale source, with no locus construction.

lem-sfb-lci-etale-pointwise-invariance vs lem-trf-syntomic-geometric-fibres-affine-criterion: the existing statement is an affine-local criterion for a flat lfp morphism with geometric lci fibres; it does not compare pointwise lci conditions along an etale map.

lem-sfb-lci-etale-pointwise-invariance vs lem-trf-complete-intersection-fibres-limit-descent: the existing statement descends lci fibres to a finite stage of an inverse limit; no such limits occur in the new node.

lem-sfb-lci-etale-pointwise-invariance vs lem-sfb-proper-nodal-dualizing-base-change: the existing statement concerns the dualizing line of a proper nodal family and its base-change isomorphism; the new statement neither assumes nodality nor mentions duality.

lem-sfb-lci-etale-pointwise-invariance vs lem-sfb-gorenstein-curve-relative-dualizing: the existing statement concerns a relative dualizing line for a Gorenstein curve; the new node has no dimension or dualizing-object assertion.

lem-sfb-lci-etale-pointwise-invariance vs lem-sfb-nodal-family-regular-affine-presentations: the existing statement constructs regular-sequence presentations for nodal families; the new statement is pointwise etale invariance for any locally finite type schemes over a field.
