# lem-sfb-curve-tangent-finiteness — Q70

## Files written

All paths are relative to this item's sandbox.

- dag/nodes/sec-six-functors-basics/lem-sfb-curve-tangent-finiteness.json — item, statement unchanged, split into six proof steps. Current Mathlib searches find no match.
- dag/nodes/sec-six-functors-basics/def-sfb-space-naive-cotangent-complex.json — definition, unsplit; no Mathlib match for the algebraic-space etale-site construction.
- dag/nodes/sec-six-functors-basics/lem-sfb-flat-space-split-deformation-ext.json — statement, unsplit; no Mathlib match for the geometric deformation classification and its linearity.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-naive-cotangent-coherent.json — statement, unsplit; no Mathlib match for coherent cotangent cohomology on algebraic spaces.
- dag/nodes/sec-six-functors-basics/lem-sfb-proper-space-coherent-ext-finite.json — statement, unsplit; no Mathlib match for global Ext finiteness on proper algebraic spaces.
- citations.json — a verbatim statement excerpt for every step/node citation.
- searches.jsonl and search_results.json — actual search log and complete wrapper outputs. The queries, including two distinct LeanFinder phrasings per node, are reproduced in the nodes. The .search.txt files retain the outputs for reading.

There are four new nodes and zero Mathlib leaves. New statements carry no proof or proof dependencies; the new definition is an explicit sheaf construction with no existentially selected data.

## Attachments

None. I searched lean/WeilConjectures for the item's blueprint tag and for infinitesimal automorphisms, proper deformations, and curve deformations. There is no declaration stating this result. Other cotangent declarations found by the notion search concern ring presentations or point tangent spaces, not deformations of the proper algebraic space. No compiler or Lake command was run.

## WANTED

None. All sources used are present in literature/stacks-project/.

## Findings and changes

The item is already the arbitrary-field version of Stacks 0D57, and it is correct. I preserved its entire statement and statement dependencies. The source's finite-type-over-Z clause follows by specialization; it is not an extra hypothesis on the result. The inherited blueprint.from.node is null, as confirmed by tools/blueprint_refs.py ancestor: the current imported ancestor det-thm-sf-ctf-stability-direct-images has no blueprint.is. I retained that provenance and the existing detailed place and via chain; each new node prepends this item to via and specifies the exact Ext/coherence source it serves. No unit or chapter route was changed.

The original item had no proof. Stacks 0D57 refers to 0D1K via the fully faithful inclusion of curves into proper spaces. I expanded the cotangent calculation rather than creating a node that restates proper-space tangent finiteness. Its two genuine inputs are deformation-to-Ext and proper coherent Ext finiteness, with the bounded-coherent hypothesis exposed separately. The naive cotangent complex needed an algebraic-space definition rather than a citation of the ring-only complex. I also used the existing curve infinitesimal pushout node to justify addition and linearity of the injection into ambient flat deformations. This avoids silently claiming that the full-inclusion functor alone proves linearity.

The new coherence node records the locally Noetherian consequence of locally finite presentation over a locally Noetherian base, plus the coherent degrees -1 and 0 needed by Ext finiteness. These are general algebraic-space facts, not clauses of the item. The final subspace argument, field Noetherianity, and the dual-number/fibre-product ring calculations remain elementary parts of the item's proof.

## Not duplicates

The whole DAG was searched by the tags 0D0V, 08TW, 08U0, 0D17, 0D0Y, 0D0Z, 04ZK, 0D0T and by cotangent, deformation, infinitesimal automorphism, coherent Ext, and locally Noetherian keywords; no existing node has these source tags. Whole-blueprint searches included cotangent, cotangent complex, deformation, naive, tangent, infinitesimal automorphism, locally Noetherian, and the four principal source tags. Relevant distinctions are:

- def-sfb-space-naive-cotangent-complex vs lem-trf-affine-cotangent-comparison: the latter constructs the full cotangent complex for sheaves on ordinary topological spaces and compares stalks; this node defines the two-term naive complex on the small etale topos of an arbitrary algebraic space.
- def-sfb-space-naive-cotangent-complex vs def-weil-pbc-smooth-ring-map: the latter's naive complex belongs to a single ring map, not to sheaves on an algebraic-space topos.
- lem-sfb-space-naive-cotangent-coherent vs pqf-lem-locnoeth-lft: the existing node only gives local Noetherianity of schemes; it does not give coherent naive cotangent cohomology on algebraic spaces.
- lem-sfb-proper-space-coherent-ext-finite vs lem-pc-coherent-hi: the existing node is a coherent higher-direct-image theorem for schemes and module sheaves, not global Ext of bounded-on-one-side coherent complexes on algebraic spaces.
- lem-sfb-flat-space-split-deformation-ext vs lem-sfb-curve-tangent-finiteness: the new node classifies arbitrary flat-space deformations by Ext with general square-zero coefficients and says nothing about finite dimensionality; it does not restate either finiteness conclusion.

## Review by Q70

I read quot.tex Tag 0D57 (lemma-curves-tangent-space), the inclusion 0D50, the entire proof of Tag 0D1K (lemma-spaces-tangent-space), and the curve pushout 0D56. The item does not restrict to nodal, smooth, geometrically reduced, connected, or projective curves. In particular the -1 cohomology of the naive cotangent complex cannot be dropped. I checked the chapter and unit records: this is a prerequisite below the fixed alteration/plurinodal moduli route, not the unit key statement, so there is no unit realization to edit.

For def-sfb-space-naive-cotangent-complex I read spaces-more-morphisms.tex 0D0V (definition-netherlander), sites-modules.tex 08TW and 08U0, including the actual canonical polynomial presentation and its conormal differential. The node constructs that presentation by sheafification, takes its kernel and square, and places the differential in degrees -1,0. It does not identify the full cotangent complex with its truncation. I read the existing algebraic-space definition to check that it supplies the small etale site and structure sheaf. Ring Kahler differentials, module sheaves, tensor, and the derived category are cited in the statement. The notation Ext for complexes is explicitly defined by derived Hom, because def-pc-ext itself only defines Ext of degree-zero objects.

For lem-sfb-flat-space-split-deformation-ext I read defos.tex 0D17 (lemma-deform-spaces) and its ringed-topos argument. Its thickening is Spec K inside Spec(K direct-sum M), whose conormal module is M. The trivial family supplies a solution and hence the origin in the Ext-one torsor; the coefficient is O_X tensor_K M. The same lemma gives Ext zero for automorphisms. I also read the construction of the torsor in lemma-choices-ringed-topoi, artin.tex 07Y6/07Y9 and 0D18: the scalar and addition operations are the split square-zero operations, and this applies over arbitrary fields. Naturality in the coefficient and Baer addition belong to this prerequisite's stated conclusion, not to an uncited claim in the item's proof. The new node introduces X, K, M, marking and all arrow conditions. Flatness is assumed and explicitly interpreted on charts. No properness or finite presentation is asserted in this general classification.

For lem-sfb-space-naive-cotangent-coherent I read 0D0Z (lemma-netherlander-fp), 0D0Y (lemma-netherlander-quasi-coherent), and spaces-morphisms.tex 04ZK. Local finite presentation implies local finite type, so the latter theorem makes X locally Noetherian. On Noetherian charts the two finite-type terms of the local cotangent model have finite kernels and cokernels; this gives precisely coherent cohomology in degrees -1 and 0. O_X is itself coherent on these charts. The node states this corollary, with local Noetherianity and coherence spelled out. During this review I corrected the inline description of an associated module: on the etale site its value on Spec B over Spec R is B tensor_R N, rather than only the Zariski D(g) description.

For lem-sfb-proper-space-coherent-ext-finite I read spaces-perfect.tex 0D0T (lemma-ext-finite). I checked the directions of both bounds: the first argument is bounded above, the second bounded below. A is Noetherian, properness is not replaced by projectivity, and n can be any integer. The node states finite generation as an A-module, not finiteness as a set. It defines the global derived Hom being used and describes coherence on etale affine charts. ModuleCat.finite_ext returned by Loogle is a finite-module theorem on an affine ring, so it is not a match to this global geometric statement.

Step 1 cites the complete deformation/Ext statement, including the trivial origin and operation compatibility. O_X tensor_K K equals O_X by b tensor c mapping to cb; the inverse is b mapping to b tensor 1. The field of definition is the same K throughout.

Step 2 is an elementary full-subgroupoid argument. It uses only the two arrow definitions already stated: an ambient marked isomorphism between two curve families is already a curve-family arrow. The infinitesimal automorphisms are those of the very same trivial family, so no restriction or quotient is lost.

Step 3 cites the existing lem-sfb-curve-infinitesimal-pushout statement, which I opened in full, and the new deformation/Ext compatibility statement. The existing lemma permits a thickening and an affine map; Spec K to the dual numbers satisfies both requirements. Two marked families therefore glue over the explicit ring fibre product. Pullback along the addition map and scalar maps is exactly the specified C base change. The deformation/Ext node says these operations map to Ext addition and scalar multiplication. Thus the map is linear and its image is a subspace; this is not inferred merely from full faithfulness. The explicit fibre-product computation uses two independent square-zero coordinates with every product zero, not K[epsilon_1,epsilon_2]/(epsilon_1^2,epsilon_2^2).

Step 4 cites exactly the coherent-cotangent statement and checks its local-finite-presentation and locally Noetherian hypotheses. A field has just the two ideals, so no finite-type-over-Z assumption is used. Step 5 cites exactly global Ext finiteness with A=K, E=NL, F=O_X[0], n=0,1; step 4 gives the required opposing bounds, and the item gives properness. Step 6 is finite-dimensional linear algebra written out via the injective map: no geometric lemma is hidden there. The citations file includes every step's uses and quotes their statements verbatim.

Small cases checked: X empty gives zero Ext and unique marked deformation; X=Spec K has naive complex quasi-isomorphic to zero and trivial deformations/infinitesimal automorphisms; P^1_K has tangent zero and its usual three-dimensional infinitesimal automorphism space. Nonreduced singular proper curves are permitted: coherence only uses finite presentation and Noetherianity, so neither local complete intersection nor H^{-1}=0 is assumed. For the classification node M=0 gives just X with its marking and identity automorphism; zero-dimensional fibres are allowed by the original curve definition. For the proper Ext statement the empty base/space has zero modules and causes no exception.

All five nodes have actual current wrapper searches in LeanFinder (two phrasings), Loogle, grep and LeanSearch. I read the returned hits, including ring cotangent finiteness requiring projective differentials, scheme local Noetherianity, and ModuleCat.finite_ext; none has the required algebraic-space/coherent-derived statement. No node is claimed as a Mathlib leaf. Each new node was left unsplit. No non-elementary step exceeds 2000 characters (the longest is step 3, 1272 characters), and none transfers a finiteness clause into a new node. All statement-only prerequisites are independently meaningful geometric results.

## Unfinished work

None within this one-level split. The four new unsplit nodes are the intended subsequent stage-1 items. There is no Lean delivery and no build.

## Dry-run repairs

The first full preflight rejected the phrase “the item's” in step 4 under its standalone-statement check. I replaced it by the explicit assertion that the structure morphism is finitely presented by hypothesis. No mathematical statement or dependency changed. The separate review_split server check had already passed.
