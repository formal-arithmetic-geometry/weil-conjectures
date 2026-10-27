# Worker report

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-adic-formal-open-gluing.json`: item, statement unchanged, split into eight steps.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-topological-ring-sheaf-open-descent.json`: one new statement-only node, unsplit; no exact Mathlib match.
- `citations.json`: every proof-step citation has a verbatim part of the cited statement.
- `searches.jsonl`: genuine msearch.py query log; inherited item searches are retained and the current search results appended.

## Attachments

None. Searches in `lean/WeilConjectures/` for the blueprint id, formal spectra, adic formal schemes and locally topologically ringed spaces found no declaration stating this item. Existing formal-completion modules concern different objects or module systems and do not attach all clauses.

## Literature wanted

No WANTED document: all sources used here are present. Read the current blueprint at `literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/lem-per-artin-gabber-affine-curve.{md,proof.md}`, together with the chapter and unit records. This helper belongs to the recorded formal-resolution descendants of the Step 3 duality branch; it does not replace the unit's perverse/Fourier route.

## Corrections and limitations

The item's statement is unchanged and is not disputed. Its proof was empty. I filled the actual quotient construction and the omitted mapping-property details from Schemes Tag 01JB, rather than treating ordinary scheme gluing as a theorem about formal spectra. The cited definition def-per-adic-formal-geometry gives a ringed-space construction; it is used here only for its finite formal-affine cover convention, not as a statement about continuity of arbitrary ringed-space maps. Topological structure and continuous maps are explicitly handled by the new node and the local hypotheses of the item.

There is one new node, no Mathlib leaves, and no unfinished step in the item's proof. As required, the new dependency remains unsplit with no proof or proof dependencies. Its future proof material follows below, outside its statement.

## Proof material for the new node

Read Formal Spaces Tag 0AHY, section-formal-schemes-EGA, from the opening warning through the discussion of equalizer section topologies, f-maps and locally topologically ringed spaces. Also read Sheaves Tags 00AL (lemma-glue-sheaves, first proof), 00AM (lemma-glue-sheaves-structures) and 00AN (lemma-mapping-property-glue). The topological adaptation is an argument by Q61, not a claim that 00AM includes topological rings: 0AHY expressly warns against that inference.

For the new node, take compatible tuples of local sections with their subspace topology in the product. Ring operations and restrictions are continuous coordinatewise. For an arbitrary cover of W, the sheaf equalizer for each local F_a(W intersect U_a) makes its topology initial for restriction to the smaller opens of that cover. Thus the tuple topology is initial for all the double-indexed local coordinates. The same initial topology is obtained by first forming matching tuples on each covering open and then taking their equalizer. These identifications are ring isomorphisms and homeomorphisms: in both directions continuity is tested on precisely those restriction coordinates. This verifies the categorical sheaf condition, not only unique gluing of underlying sets. For W contained in U_a, projection to the a coordinate has inverse sending s to (theta_ab(s restricted to W intersect U_b))_b; continuity holds coordinatewise in both directions. Morphisms are formed by applying the local morphisms and the sheaf gluing axiom; continuity follows from the target equalizer topology. Their uniqueness and naturality follow by restrictions. Gluing inverses gives uniqueness up to unique compatible isomorphism. This works on a fixed arbitrary space with no Noetherian, formal-spectrum, stalk-locality or ideal condition, so it is a strictly smaller sheaf-theoretic fact, not a restatement of the item.

## Search findings

Before creating the new node I searched the DAG by gluing/descent of sheaves and by topologically ringed spaces, 0AHY, 00AL, 00AM and 00AN; searched the entire imported blueprint using blueprint_refs.py search for gluing, glueing, sheaves of rings and topological rings; and read the project source candidates. The blueprint search found ordinary scheme descent, module/coefficient sheaves and algebraic ring objects, not topological-ring sheaf descent. Existing module-open-descent nodes need an already given structure sheaf and do not construct a topological structure sheaf.

All Mathlib queries added here were run through msearch.py and read. Both semantic phrasings find section gluing for an already specified sheaf or ordinary scheme glue data; they do not state object descent with continuous section maps. I read Mathlib/Topology/Sheaves/SheafCondition/UniqueGluing.lean (the general concrete-category assumptions, including reflecting isomorphisms), Topology/Sheaves/CommRingCat.lean (objSupIsoProdEqLocus at line 301), Topology/Category/TopCommRingCat.lean (the entire short file) and Geometry/RingedSpace/PresheafedSpace/Gluing.lean (generic GlueData and HasLimits assumptions, especially the SheafedSpace part around lines 553--646). The generic GlueData theorem assumes limits of its value category. The TopCommRingCat file has no limit construction or instance, and the global source search for its limit instances found only the category namespace. Moreover its forgetful functor to sets does not reflect isomorphisms (the source explicitly says so), so the concrete unique-gluing equivalence cannot simply be instantiated. Ordinary CommRingCat section equalizers carry no sheaf of section topologies. Hence this new node is not a one-line Mathlib specialization. The Loogle query TopCommRingCat, Sheaf returned an unknown-identifier message, which is recorded as such rather than treated as a theorem search excluding all matches; other Loogle and semantic queries and actual source inspection supply the search coverage. No service was unavailable in the retained new-node searches.

## Review by Q61

I checked B--E of delivery-errors.md with the node statements and the three Stacks source files open. The new node introduces its own space, cover, local sheaves, maps, section topology and cocycle. It contains a statement only, correctly escaped TeX, actual logged Mathlib queries, a precise nearest blueprint ancestor and via chain, and no dependencies on this item's conclusion. It is neither an elementary two-line consequence nor a formal-scheme gluing clause renamed: it proves effective descent of a different category on a fixed space. The geometric gluing and all ideal clauses remain arguments in the item. No SGA source is used.

For Step 1 I checked the actual quotient relation against the full triple-overlap domain hypothesis; transitivity uses that hypothesis before invoking the cocycle. Injectivity uses the diagonal identity. The inverse-image formula checks that every chart is an open embedding and that its precise overlap is the prescribed one. These are direct point-set verifications, with no cited theorem hidden.

Step 2 uses the new node's assertion of object descent and compatible local topological ring-sheaf isomorphisms. The phi maps are continuous isomorphisms by hypothesis, so their transported maps satisfy exactly its cocycle. Stalk locality follows by the germ identification on an open neighbourhood. The new node does not assert formal affineness; Step 3 checks that separately from def-per-adic-formal-geometry's exact sentence about a finite cover by formal affines. Finite union of finite chart covers uses finiteness of E. Empty pieces and the empty family are handled explicitly.

Step 4 uses exactly the new node's matching-tuples formula, not its proof or an unasserted topology comparison. It writes the map on every target open and verifies continuity into the subspace by its continuous coordinates. The local stalk-map hypothesis comes from the supplied f_i. It proves the omitted mapping properties of 01JB and then derives the inverse comparison maps; there is no unjustified use of ordinary scheme maps as formal maps.

Steps 5 and 6 construct the actual ideal subsheaf by a local membership condition and prove its sheaf condition, closure, restrictions and equality uniqueness. Coherence is the very local finite-ideal presentation stipulated in the item. The usual formal meanings of open ideals and ideals of definition are local predicates, and their witnesses on the original charts remain unchanged. No claim about a uniform exponent on every arbitrary open is smuggled in. In particular no affine-overlap hypothesis, ideal descent theorem or formal-functions theorem is being used without a node.

Step 7 uses lem-per-formal-affine-principal-refinement's exact principal-open formal-spectrum identification and Noetherian coordinate-ring conclusion; the complete rings are those in its explicit definition of R_{{s}}. I read its statement and its dependency lists: it does not depend on this item, so adding the citation makes no cycle. Its extra regularity/faithful-flatness clauses are not used. The finite subcover argument is written out using def-weil-pbc-noetherian-ring's statement that every ideal is finitely generated; it reduces the ideal generated by an arbitrary set of principal-open elements to finitely many of those same elements. This works for an arbitrary open subset and needs no separatedness. Step 8 uses only the explicit mapping and membership arguments already established in Steps 4--5, and verifies comparison coherence by equality on the refined cover.

Every step is under 2000 characters. The elementary markings are limited to explicit quotient, finite-cover, ideal membership and uniqueness arguments; the genuinely non-elementary topological-sheaf descent steps are marked non-elementary and cite the new node. I checked all five citation occurrences against the exact statement text and copied them into citations.json. The cited definition is not used as a theorem, and the new sheaf node is not used to assert anything about formal spectra or coherent ideals.

Edge cases: the zero ring/formal empty chart is harmless; an empty index set gives the empty locally topologically ringed space and its unique ideal; a singleton cover gives the original object; disjoint overlaps give disjoint union; identity overlaps give the original chart. The two copies of an ordinary affine plane with the punctured plane as overlap (with discrete adic topology) check the nonaffine-overlap situation: the construction never replaces that punctured overlap by an affine. For ideals, the unit ideal is open but is not an ideal of definition on a nonempty nondiscrete formal chart, whereas the zero ideal is an ideal of definition on a discrete chart; Step 6 retains these distinctions. Empty opens cause the unique zero-ring section and zero ideal, agreeing with the formulas.

## Not duplicates

lem-per-topological-ring-sheaf-open-descent vs lem-per-noetherian-formal-affine-coherent-modules: this concerns finite modules and coherent sheaves on a noetherian formal affine on formal charts; the new node has no formal spectrum or finite-module hypothesis and supplies fixed-space topological ring sheaf descent.

lem-per-topological-ring-sheaf-open-descent vs lem-per-adic-formal-open-gluing: the item constructs a varying underlying formal space and glues morphisms and coherent ideals; the new node only descends topological ring sheaves on an already fixed topological space.

lem-per-topological-ring-sheaf-open-descent vs def-per-adic-formal-geometry: this defines formal spectra and completion in ringed spaces; it does not assert descent of sheaves of topological rings.

lem-per-topological-ring-sheaf-open-descent vs lem-per-formal-affine-principal-refinement: this concerns principal refinements and local algebra of noetherian formal affine charts on formal charts; the new node has no formal spectrum or finite-module hypothesis and supplies fixed-space topological ring sheaf descent.

lem-per-topological-ring-sheaf-open-descent vs lem-per-completion-finite-type-base-change: this concerns completion of finite-type schemes and adic base change on formal charts; the new node has no formal spectrum or finite-module hypothesis and supplies fixed-space topological ring sheaf descent.

lem-per-topological-ring-sheaf-open-descent vs def-per-adic-principal-chart-data: this defines topologies and comparison data on principal formal opens, without constructing gluing of arbitrary topological ring sheaves.

lem-per-topological-ring-sheaf-open-descent vs lem-per-formal-completion-reduction-dictionary: this concerns infinitesimal quotients on arbitrary affine charts of a formal completion on formal charts; the new node has no formal spectrum or finite-module hypothesis and supplies fixed-space topological ring sheaf descent.

lem-per-topological-ring-sheaf-open-descent vs lem-weil-pbc-scheme-morphism-gluing: this glues morphisms of ordinary schemes, not objects and continuous morphisms in the category of topological ring sheaves.

lem-per-topological-ring-sheaf-open-descent vs lem-weil-pbc-module-compatible-family-small: this concerns coherent module families are small via a point-indexed subcover with an existing module/scalar sheaf; it does not descend the section topologies or construct a sheaf of topological rings.

lem-per-topological-ring-sheaf-open-descent vs lem-weil-pbc-module-object-open-descent: this concerns effectivity of open-cover descent for module sheaves with an existing module/scalar sheaf; it does not descend the section topologies or construct a sheaf of topological rings.

lem-per-topological-ring-sheaf-open-descent vs lem-weil-pbc-module-object-open-descent-diagonal: this concerns diagonal transition map identity from cocycle with an existing module/scalar sheaf; it does not descend the section topologies or construct a sheaf of topological rings.

lem-per-topological-ring-sheaf-open-descent vs new-stage3-torsion-controlled-overlap-cocycle: this concerns the fixed local sources and normalized quotient maps admit compatible overlap isomorphisms. with an existing module/scalar sheaf; it does not descend the section topologies or construct a sheaf of topological rings.

lem-per-topological-ring-sheaf-open-descent vs new-stage3-torsion-controlled-local-cocycle: this concerns local algebraizations give an algebraic cocycle preserving the arrows and quotient maps. with an existing module/scalar sheaf; it does not descend the section topologies or construct a sheaf of topological rings.

lem-per-topological-ring-sheaf-open-descent vs new-stage3-torsion-controlled-descended-source-comparisons: this concerns a descended source with compatible quotient maps yields the formal comparisons and arrow. with an existing module/scalar sheaf; it does not descend the section topologies or construct a sheaf of topological rings.

lem-per-topological-ring-sheaf-open-descent vs new-stage3-compatible-quotient-formal-comparisons: this concerns compatible local quotient maps identify a fixed coherent source's completion with n. with an existing module/scalar sheaf; it does not descend the section topologies or construct a sheaf of topological rings.

lem-per-topological-ring-sheaf-open-descent vs def-weil-pbc-module-compatible-family-presheaf: this concerns explicit coherent-family module presheaf and its shrinking with an existing module/scalar sheaf; it does not descend the section topologies or construct a sheaf of topological rings.

lem-per-topological-ring-sheaf-open-descent vs lem-weil-pbc-module-compatible-family-sheaf: this concerns compatible-family module sheaf and its sectionwise universal property with an existing module/scalar sheaf; it does not descend the section topologies or construct a sheaf of topological rings.

lem-per-topological-ring-sheaf-open-descent vs lem-weil-pbc-module-compatible-family-sheaf-condition: this concerns componentwise gluing for the coherent-family module presheaf with an existing module/scalar sheaf; it does not descend the section topologies or construct a sheaf of topological rings.

lem-per-topological-ring-sheaf-open-descent vs new-stage3-torsion-controlled-algebraization-local-descent: this concerns algebraic descent retaining compatible local formal comparisons with an existing module/scalar sheaf; it does not descend the section topologies or construct a sheaf of topological rings.

lem-per-topological-ring-sheaf-open-descent vs lem-weil-pbc-projective-space-twist-glued-identification: this concerns the glued twisting sheaf o(1) of p^n_z is the sheaf attached to s(1) with an existing module/scalar sheaf; it does not descend the section topologies or construct a sheaf of topological rings.

lem-per-topological-ring-sheaf-open-descent vs lem-weil-pbc-glue-sheaves-of-modules: this concerns glueing morphisms and sheaves of modules along an open covering with an existing module/scalar sheaf; it does not descend the section topologies or construct a sheaf of topological rings.

lem-per-topological-ring-sheaf-open-descent vs lem-weil-pbc-module-object-open-descent-aux-diagonal: this concerns diagonal identity for transition isomorphisms with an existing module/scalar sheaf; it does not descend the section topologies or construct a sheaf of topological rings.

lem-per-topological-ring-sheaf-open-descent vs lem-weil-pbc-torsion-controlled-algebraization-descent: this concerns descent from local torsion-controlled triples with an existing module/scalar sheaf; it does not descend the section topologies or construct a sheaf of topological rings.

lem-per-topological-ring-sheaf-open-descent vs def-sc-local-free-generator: this concerns local free generator of a module sheaf with an existing module/scalar sheaf; it does not descend the section topologies or construct a sheaf of topological rings.

lem-per-topological-ring-sheaf-open-descent vs lem-sc-glue-component-transition-cocycle: this concerns cech transition functions glue local trivial line bundles with an existing module/scalar sheaf; it does not descend the section topologies or construct a sheaf of topological rings.

## Dry-run repairs

The first server preflight required a definition-node citation in the new statement, despite its inline definitions. I read def-kun-subspace-topology in full: it defines exactly the induced topology on a subset as the coarsest topology making inclusion continuous. The new node now cites that existing Mathlib definition for its matching-tuple subspace topology, with the corresponding statement dependency. This adds no mathematical hypothesis and no new node. All tuple/topology citation quotes were refreshed verbatim.
