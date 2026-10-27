# Stage-1 report: lem-sfb-galois-coefficient-path-coherence

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-galois-coefficient-path-coherence.json`: statement, split; unchanged statement and statement dependencies, seven proof steps, existing-node citations only. The item is not a Mathlib leaf.
- `citations.json`: one verbatim statement quotation for each of the 17 step/node citations.
- `searches.jsonl`: the search command's original records, retained without alteration.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the item tag, Galois coefficient coherence, and ringed paths. Finite-coefficient and module-object coherence infrastructure exists, but no declaration states the full internal-condensed, arbitrary-ring-map section comparison with its signed-shift and connecting-arrow clauses. An ordinary pushforward compositor is not an attachment.

## WANTED

WANTED: a human-written combined reference for the normalized condensed Galois coefficient-path comparison and its signed-shift normalization, for lem-sfb-galois-coefficient-path-coherence. The original node already requests this combined reference. The split is marked agent-written: Stacks Tag 0D6E, label lemma-derived-pushforward-composition in sites-cohomology.tex, supplies general composition, and the existing DAG nodes supply its coherence and the normalized section model. No claim is made that 0D6E itself states Galois descent or every compatibility.

## Audit and changes

The original item was unsplit and contained no proof. The sandbox contained only dispatcher marker files; there was no earlier split, report or search log to discard. No repair note existed. The statement is mathematically well-typed with scalar restrictions interpreted as their exact derived functors; it has not been changed. No STATEMENT-DISPUTED correction was needed.

The geometric/invariant scalar squares use the *actual* ringed maps; equality after forgetting scalar actions would not suffice. The new proof explicitly checks the scalar action and action-site restriction. The evaluation target is the singleton topos with ring Z, not the condensed topos with an arbitrary scalar-free coefficient. The coefficient maps need not preserve K-injectives: the proof uses a replacement j after restricting, and the direct-image composition theorem proves that its pushed-forward map is a quasi-isomorphism. The specified delta is identified on the exact K-injective section model before the cocycle is applied. The last steps give the integer-shift degree formula and the actual square for the connecting arrow.

The source `main-20261015/.../sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3), gives the proper/open direct-image route; this item is a supporting separable-closure comparison introduced below that route, not a verbatim theorem of the blueprint. Read the item's unit and chapter records, and checked the current main blueprint paragraph. The inherited unit record still records an older sec-six-functors placement; neither its route nor its realization fields are changed by this auxiliary item. `blueprint_refs.py ancestor` returned None, as the inherited ancestry records; the existing `from.place` and `via` are retained and `same_as` checked. Blueprint searches for derived composition, pushforward composition, Galois coefficient and composition cocycle produced no blueprint statement equivalent to this item.

Generic tools from other units are listed in `split_report.tool_uses`: they provide general ringed composition, exact coefficient restriction, global-sections comparison, K-injective shifts and triangulated functors. They do not replace any geometric step in the unit route. A dependency traversal found no path from the newly cited generic tools back to the item.

## New nodes

None. Reusing lem-pur-ringed-derived-composition-cocycle and lem-coef-derived-sections-scalar-coherence avoids duplicating the general coherence argument. No Mathlib leaves are created.

## Not duplicates

No new nodes, hence no new/existing node pairs requiring distinction. Ordinary pushforward composition and its associativity were found in Mathlib; they are infrastructure, not the condensed Galois theorem.

## Mathlib searches

Retained the five inherited search records and their results. Ran leanfinder twice, Loogle twice and grep twice, as well as LeanSearch, with the prescribed msearch.py command and the item's own id. The first Loogle query contained an unknown identifier; this is recorded as an unusable query, and a valid second query was run. LeanSearch returned unrelated scalar-restriction and field-theory declarations; no outage was recast as a negative result. The inherited LeanSearch rate-limit outage remains recorded as unavailable.

Read the fresh search hits. In the pinned local Mathlib, SheafOfModules.pushforwardComp and pushforward_assoc in Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean, lines 139 and 159, describe ordinary compositors. Read their definitions and the section-identity component formulas at lines 146 and 150. Also read the generic total-right-derived interface in CategoryTheory/Functor/Derived/RightDerived.lean. The service's second Loogle search listed additional generic shift and natural-transformation infrastructure; its RightDerivedCommShift module is not present in this pinned local checkout, so it is not asserted as a local match. None of these hits states the full item or specializes to it in one line.

## What could not be finished

No mathematical part of the requested one-level split remains. The existing nodes are used by their statements, including currently unsplit structural inputs; proving or splitting those inputs is subsequent work, not part of this item. No Lean was written, no compiler was run, and neither the shared repository nor launcher files were modified.

## Review by Q90

I checked B through E of delivery-errors.md against the sources and the final node. There are no new unsplit nodes, hidden proofs in statements, or moved clauses masquerading as lemmas. Each of the seven steps is below 2000 characters. The only elementary-marked step is the final componentwise calculation using the named section-model comparison and naturality; the structural ringed, derived and triangulated inputs are explicit citations.

For step 1 I read the complete statement of lem-sfb-geometric-sections-adjunction: it supplies normalized E_R, its natural identity-on-sections scalar comparison, the formula for F_R, and the identification of invariants with the actual p_G module direct image. The restriction-ringed-topos lemma supplies precisely identity-topos coefficient restriction. I checked the given qcqs X and the small-site universe hypotheses. Linearity of the action verifies the square on action-site arrows as well as on section groups.

For step 2 I read lem-coef-derived-sections-scalar-coherence, which explicitly constructs the map to (Set,Z) for any small ringed site and gives its structural map. Applying it to the profinite site makes global sections evaluation at the terminal singleton. The K-injective section-model statement explicitly supplies exact evaluation and the gluing isomorphism gamma. Restriction of scalars keeps kernels and cokernels; the exact-derived-functor lemma states that every complex computes the total derived functor. Thus no extra acyclicity or flatness hypothesis is inferred from a mere definition.

For step 3 I read the entire statement of lem-weil-pbc-ringed-topoi-derived-pushforward-composition and its source in Stacks 0D6E. Its normalization says exactly that g_*j is a quasi-isomorphism for a replacement of f_*I, which is the fact this step needs. Both edges in every factorization really are ringed-topos morphisms on small sites. The scalar-sections coherence statement gives sigma with the opposite direction to the requested c_Gamma; the proof correctly uses its inverse. The exact-derived-functor statement justifies using D(Res) at the exact edges.

For step 4 I checked the section-model statement's explicit claims: F_R and Gamma_G preserve K-injectives, and its C(gamma)_I is the canonical derived adjunction-composition comparison with the specified units and counits. Those are the claims used to identify d_R with the given delta. This identification does not use the proof of the node or assume that the scalar-restricted representative is K-injective.

For step 5 I read the cocycle lemma statement, including its last sentence allowing coefficient maps on identity underlying topoi. Expanding the two coefficient paths gives rebracketings of the same ringed composite; its triple law and two unit laws give exactly the claimed equalities. The ordinary comparisons agree because they are the specified identity maps on sections. This is a use of the named general cocycle, not an unproved appeal to coherence or an alternative definition of delta.

For step 6 I read the statements of both triangulated-functor lemmas and the source right-derived triangulated instances in WeilConjectures/CategoryTheory/DerivedCategory/RightDerivedFunctor/Triangulated.lean, lines 94-99. I read the K-injective shift node and Stacks derived.tex, definition-K-injective and its following shift observation, and lemma-enough-K-injectives-implies. A shifted replacement remains valid for every integer, including negative shifts. The component formula g_*(j^{r+n}) and differential (-1)^n H(d) verifies the comparison's compatibility rather than merely stating it.

For step 7 the C(gamma) formula is exactly the quoted section-model assertion. At odd n both differentials change sign, and the same gamma component is a chain map; no extra sign is inserted in the transformation. For the connecting map w I wrote the naturality equation and then substituted the shift-compatibility equation. This checks the actual last square of a morphism of triangles.

I tested the construction on identity and two successive coefficient maps (the unit laws and triple cocycle), on the zero ring and trivial G (the geometric input explicitly includes them), on a separably closed field, on nonflat constant Z to Z/2 coefficients, and on n=1 and n=-1. None requires scalar restriction to preserve K-injectives, finite cohomological dimension, constructibility, or an underived continuous-cochain replacement. I corrected no source statement; the substantive repair to the empty proof is exposing these normalizations and the signed final-square argument. Citations.json quotes each cited node's statement verbatim, so every use can be checked independently.
