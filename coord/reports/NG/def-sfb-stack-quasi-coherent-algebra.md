## Files written

dag/nodes/sec-six-functors-basics/def-sfb-stack-quasi-coherent-algebra.json — definition; split using existing notions only, no whole-item Mathlib match. No new nodes; no Mathlib leaves. citations.json is [] because a definition has no proof steps. searches.jsonl contains six new searches; the inherited search records were retained.

## Attachments

None. The project definitions AlgebraicGeometry.Scheme.CommAlgebraSheaf and AlgebraicGeometry.Scheme.IsQuasiCoherentAlgebra concern the open site of a scheme, not the big fppf site of a category fibred in groupoids; they do not state the entire item. The exact blueprint tag has no project hit.

## Wanted

None. All sources used are present locally.

## Findings and corrections

The definition was already mathematically explicit, but lacked direct dependencies for its universe convention, general site/sheaf terminology and underlying module. Added def-weil-size-convention, def-weil-pbc-sites-and-cohomology and def-weil-sheaf-of-modules-category, with explicit references in the statement. Expanded the underlying module action, the meaning of a ring sheaf and the discrete fibred category associated to the algebraic space Y. Specified regular-function sections and their restriction via the scheme structure-sheaf morphism. These are definitional clarifications; none changes the class of objects or morphisms. No STATEMENT-DISPUTED assertion was found.

Read the current latest chapter, unit and direct-image proof, and the recorded DAG chapter and unit. The inherited blueprint.from.node is null: blueprint_refs.py ancestor also prints None. Retained this provenance and its detailed from.place/via chain instead of inventing a blueprint ancestor. The current latest direct-image proof does not itself state the adequate-moduli prerequisite; this item is a definition below that inherited chain and does not replace a unit proof route. Whole-blueprint searches for quasi-coherent, structure sheaf and algebraic stack found no duplicate of this fibred-category definition. Same-tag DAG matches were the item and adequate-moduli-space (the latter uses these notions but does not define them). Existing scheme-algebra and algebraic-space nodes are different sites; reused the generic module quasi-coherence node. No new node is needed for a clause of this definition.

## Unfinished work

None within stage 1. No Lean was written or compiled.

## Not duplicates

No new nodes were created.

## Review by NG

I read stacks-sheaves.tex at Tags 06TP (definition-inherited-topologies), 06TV (definition-structure-sheaf), 06WG (definition-quasi-coherent), and 06W5/06W6 (section-pushforward/equation-pushforward). Each is formulated for a category fibred in groupoids, so the generality of the item needs no algebraic-stack, smooth-atlas, qcqs or representability hypothesis. The inherited site has the scheme fppf coverings. The structure sheaf is the explicit section functor on the scheme underneath an object, not an unspecified object chosen by existence. I also read descent.tex definition-structure-sheaf for this scheme section convention, sites.tex Tag 06UN for global sections as compatible families, and sites-modules.tex definition-site-local for presentations on slice sites.

There are no proof steps and hence no step-node citations to certify: citations.json is empty. I instead opened every statement dependency. def-pc-scheme gives schemes and their morphisms; def-pc-fppf-site gives the underlying scheme site and its coverings; def-sfb-stable-pointed-moduli-groupoids explicitly defines categories fibred in groupoids, their functors and 2-fibre products; def-sfb-algebraic-moduli-stack gives the illustrative stack predicate; def-trf-algebraic-space gives Y and its small etale site and structure sheaf. def-trf-space-quasi-coherent-module states the GENERAL ringed-site local-presentation condition, not merely its algebraic-space specialization. def-weil-size-convention gives the small skeleton bound needed for families over all site objects. def-weil-pbc-sites-and-cohomology gives sheaves and restriction morphisms. def-weil-sheaf-of-modules-category gives the semilinear module restrictions required by the explicitly displayed action. Thus each dependency states the notion actually taken from it; no definition is used as a descent theorem.

For the direct-image convention I checked the source triples (h:U→W,x,φ(x)→h*W): their projections give exactly A(x), with its original restrictions. The comma-category compatible-family formula is the source formula 06W6, now used as the definition of this direct-image convention restricted to Y_et. Pulling back a regular function on W gives its component at each such triple. No assertion that arbitrary direct images preserve quasi-coherence was added. Restriction to X_W is along a functor over Sch/S, so the structure-ring value stays Γ(T,O_T), not Γ(W,O_W). This verifies the hypotheses and the ring action without identifying different sites.

I tested the representable case X=h_T, φ=id and Y=T: the fibre over W has terminal object W, so the displayed family formula gives A(W). For the empty fibred category global sections are the unique empty family (the zero ring for ring sheaves), and the formulas still make sense. The zero algebra and infinite presentations are allowed; surjection is explicitly local lifting, not sectionwise surjectivity. Nontrivial automorphisms in a fibre impose compatibility on the global family and are not discarded by passing to isomorphism classes.

For delivery-errors B–E: there are no new unsplit nodes or hidden theorem nodes; all objects are introduced and TeX has ordinary single mathematical escapes; tags and labels were checked against the local tag table and source. The six new searches were run with msearch.py and their actual results read. LeanFinder/LeanSearch returned scheme structure sheaves and general QuasicoherentData, whose source I read, but not this fibred-category construction; Loogle and the algebraic-geometry grep returned no relevant name. A second semantic phrasing found only the same generic module predicate. No Mathlib hit is claimed as a whole-item leaf. C1/C4 are vacuous for proof steps here, and all statement dependencies were checked as above. D1/D2 are avoided by creating no clause-restatement nodes; D3–D5 and long-step checks have no proof to inspect. The small cases and direct-image types above address the E checks. The changes correct missing notion references, not mathematical hypotheses.
