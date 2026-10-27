## Files written

dag/nodes/sec-six-functors-basics/lem-sfb-fppf-groupoid-restriction-quotient.json: existing statement split in five steps; no new nodes and no new Mathlib leaves. The statement and statement dependencies are unchanged.

citations.json: one exact quoted statement for every node cited by every proof step. searches.jsonl: actual msearch.py searches, retained as produced by the command.

## Attachments

None. Searches of lean/WeilConjectures for the blueprint tag, fppf/groupoid combinations, restriction and groupoid quotient terminology found no declaration stating this result. The etale torsor and contracted-product declarations address different objects, not a general internal scheme groupoid. No compiler was run.

## Wanted

None. The relevant Stacks sources are available locally.

## Findings and changes

The item was unsplit in live and there was no prior sandbox node, report or search log. No released repair note exists. I read the current item and copied it into the sandbox, preserving its inherited search records and blueprint ancestry. I searched the whole DAG for Tags 02VH and 02YK and the restriction/quotient notions, and ran blueprint_refs.py ancestor and searches for groupoid quotient, monomorphism and sheafification. The ancestor command prints None, agreeing with the item's existing blueprint.from.node = null. No new blueprint ancestor was invented.

I read the current latest blueprint unit and sk-thm-sf-ctf-stability-direct-images.proof.md, especially (3), as well as the recorded chapter/unit JSON. The historical inherited ancestry mentions an alteration reduction, whereas current (3) is the compactification/direct-image argument. This delivery proves the existing supporting groupoid lemma without changing either unit or chapter route; it makes no new claim about which current paragraph contains the historical alteration argument.

The Stacks source is groupoids.tex Tag 02VH, lemma-quotient-groupoid-restrict, with its preceding pre-equivalence restriction proof. The monicity clause follows the test-section argument in descent.tex Tag 02YK, lemma-descending-property-monomorphism. I spell out the two successive endpoint covers rather than require a separately proved product-cover lemma. The cover facts are topologies.tex Tag 021O, lemma-fppf, and Tag 022C, lemma-zariski-etale-smooth-syntomic-fppf-fpqc. Equality descent is descent.tex Tag 023Q, lemma-fpqc-universal-effective-epimorphisms. I checked the omitted restricted groupoid construction in Tag 02VB, lemma-restrict-groupoid, directly from the groupoid laws.

No new lemma is needed: the restricted triple construction and the sectionwise orbit injection are short consequences of the definitions, written in the proof. Reflection of monicity is proved rather than moved into a clause node. The sheaf quotient isomorphism is proved by injectivity and local lifting of the presheaf map, using the existing set-valued Mathlib criterion. The similarly named abelian-group-valued sheafification criterion was deliberately not used: the orbit presheaves are sets.

The Mathlib item searches were actually run with msearch.py: grep in AlgebraicGeometry for groupoid quotient/restriction returned no hits; Loogle "Sheaf", "Groupoid" returned manifold StructureGroupoid sheaves; LeanSearch returned cover-dense subsite comparison and generic sheafification isomorphisms. I read DenseSubsite/Basic.lean:350-389: those isomorphisms require an isomorphism after restriction to a cover-dense subsite and do not supply our orbit-presheaf comparison. Two LeanFinder phrasings returned generic scheme topologies, cover-density and topological open-cover equivalences, not this statement. The actual local-bijection ingredient was already a Mathlib leaf, lem-cbc-set-presheaf-sheafification-local-bijection; I read LocallyBijective.lean:100-161 and Localization.lean:70-82 to check its exact set-valued scope. No unavailable service has been recorded as absence.

## Not duplicates

No new nodes. Existing lem-trf-etale-relation-restriction-quotient requires an etale equivalence relation and etale restriction, whereas this item allows arbitrary groupoid arrows and an fppf covering. Existing lem-sfb-relation-restriction-quotient assumes relation monicity and gives a more general orbit-cover criterion; it cannot supply this item's groupoid case before monicity. Existing lem-trf-fppf-generator-sheafification-comparison assumes an etale generator map. Their hypotheses explain why none is used as a proof of the item.

## Review by NR

I checked B through E of delivery-errors.md against the node and the open Stacks sources. There are no new statement-only nodes, hidden proof sketches, unsupported new notions or duplicate nodes. The statement introduces its objects and defines monicity on test sections; all existing definition dependencies were retained. No statement correction or STATEMENT-DISPUTED flag is needed.

Step 1 cites def-pc-fibre-product for its universal property and def-a1-groupoid-scheme for precisely the pointwise identity, inverse, composition and associativity laws. I verified the composition orientation: an arrow (x,h,y) followed by (y,r,z) has middle coordinate c(r,h), not c(h,r). Both endpoints, the morphism domains and naturality are supplied explicitly, so this is a routine construction rather than an unproved restriction lemma.

Step 2 cites lem-trf-fppf-covering-base-change twice, first along a and then along b p. Its statement allows arbitrary scheme maps and requires exactly the given fppf cover q. Both resulting singleton covers lie in the chosen bound. lem-trf-fppf-covering-is-fpqc states that the same fppf family is fpqc, without a quasi-compactness assumption on q. lem-weil-pbc-fpqc-representable-descent states uniqueness for maps to any scheme, so it detects equality into R first on v and then on p; no algebraic-space or separatedness hypothesis is needed. The local triples have equal endpoints, so the assumed monicity of the restricted map applies. The groupoid definition supplies reflexivity, symmetry and transitivity once arrow uniqueness is obtained. This is the actual argument of 02YK, not a citation to an absent general monicity-descent node.

Step 3 uses only the fibre-product statement and groupoid definition. Arrow existence already gives an equivalence relation even with automorphisms; equality of isomorphism classes gives one arrow, and its two lifted endpoints make an R'-triple. Injectivity of P' -> P therefore does not require monicity of either relation.

Step 4 uses exactly the arbitrary-base-change assertion of lem-trf-fppf-covering-base-change. The universal property in def-pc-fibre-product gives q x = u p. Every orbit class has a representative by definition of the set quotient. The lift [x] works on the singleton cover, and its pullbacks work on every member of the generated covering sieve. No representability or epimorphism theorem is hidden here.

Step 5 uses lem-cbc-set-presheaf-sheafification-local-bijection, whose statement is for SET-valued presheaves on a small site in a containing universe, and gives both directions of exactly the criterion needed. def-weil-size-convention supplies a small skeleton and a containing universe; def-weil-pbc-sheafification gives the universal property identifying the sheafified morphism with the map named in the item. I checked every citation against its actual statement and copied those statements verbatim into citations.json. All external theorem inputs used by the proof are already Mathlib leaves; no off-route unsplit theorem is introduced.

Edge cases checked: q the identity; U empty (then U' and R empty, and the empty-test groupoid still has its unique sections as appropriate); U'=U disjoint union U with the fold cover; and the one-object groupoid attached to a nontrivial group scheme. In the last case the orbit presheaf is still terminal and step 3 remains valid despite nonunique arrows, while the conditional monicity clause does not falsely assert monicity. For a cover without a section, the two successive base changes provide the endpoint lifts; there is no assumed global lift. No step exceeds 2000 characters or conceals a separate comparison theorem. I corrected the initially mistyped source tag for the restriction construction to 02VB after checking the Stacks tag table.

## Unfinished work

None in this one-level stage-1 split. No Lean was written and no compiler, Lake, or build tool was run. Repository and launcher files were read only. The required server dry run and direct push are performed by deliver.py, and their result is reported in the final delivery line.
