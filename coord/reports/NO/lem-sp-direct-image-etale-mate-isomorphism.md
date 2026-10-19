# Stage-1 report: lem-sp-direct-image-etale-mate-isomorphism

## Files written

- dag/nodes/sec-smooth-purity/lem-sp-direct-image-etale-mate-isomorphism.json: statement node, four proof steps, no Mathlib match; original statement and hypotheses retained.
- citations.json: one verbatim statement quotation for every dependency used by each proof step.
- report.md: this report. searches.jsonl retains the actual completed searches.

## New nodes

None. There are zero new nodes and zero Mathlib leaves.

## Attachments

None. Searched the project WeilConjectures tree for the blueprint id and projection/mate notions. LowerStarProjectionComparison.lean has the general derived comparison compatibility and an invertibility-transfer theorem, but no declaration states all the present named-map transpose assertion with exactly the fixed normalized beta components. Its general category-theory projection/mate compatibility also requires tensor compatibility as an input. These are useful reference material, not an exact attachment claim.

## WANTED

None.

## What was wrong and what changed

The item was statement-only, with no proof. The statement is retained, including the separate assumptions K and H = K tensor^L B are bounded below. This is essential: with A = Z/ell^2, B = F_ell, K = F_ell, H need not be bounded below, so boundedness cannot be inferred merely from K. No unconditional invertibility of the etale projection is claimed.

The main-20261015 parent proof Step 1 defines the pro-etale projection by its counit transpose; it does not itself justify transport of that named map from the etale site. The existing general lem-weil-pbc-ringed-exchange-tensor-coherence supplies this omitted compatibility. Reusing it avoids creating either an elementary cancellation lemma or a second copy of the generic ringed-topos result. All tensor operations here are for ordinary constant-ring modules, with no completion or condensed-module replacement.

The final sentence about the transpose is read with the usual direction of the tensor identification: if c:L(D tensor B) -> LD tensor LB, the transpose is (epsilon tensor 1) c, or equivalently its precomposition by c^{-1} is epsilon tensor 1. Step 3 spells out these domains and directions explicitly; no mathematical statement was changed.

## Sources and searches

Read the current blueprint parent proof, its coefficient-comparison unit and the smooth-purity chapter record. Read Stacks sites-cohomology.tex, Tag 07A4 (lemma-pullback-tensor-product), Tag 0G7E (lemma-pullback-K-flat), the projection map construction equation-projection-formula-map, and Tag 0E48 (remark-compatible-with-diagram). Also read categories.tex, Tag 0B65 (lemma-transformation-between-functors-and-adjoints). Stacks omits the verification of 0E48; the existing coherence node supplies an explicitly reviewed proof of that exact square. Consequently this specialization is marked agent-written rather than attributing a full proof to the blueprint. No SGA source is used.

The inherited item searches are preserved. Completed new searches through the required msearch.py command are in searches.jsonl, with the inspected later queries appended to mathlib_searches. LeanSearch returned generic counit declarations; LeanFinder's second phrasing returned etale scheme/category declarations; Loogle's proposed Adjunction.mateEquiv identifier was unknown (the actual generic name is CategoryTheory.mateEquiv); grep found generic mates in Mathlib/CategoryTheory/Adjunction/Mates.lean, not a derived site projection comparison. Read mateEquiv_counit at lines 123-125. The interrupted early search command had finished its three searches according to the log; its tool session no longer existed. Those queries were not rerun. No service failure was misreported as mathematical absence.

DAG and blueprint searches included projection, projection mate, projection comparison, comparison monoidal and ringed exchange tensor; inspected the existing general ringed-topos coherence node, comparison-pullback node, canonical direct-image mate node, finite-ring compact-support transpose node, and etale scalar-mate node. The last two have different hypotheses/constructions and were not used. The existing general coherence theorem covers this use without creating a new node.

## Not duplicates

No new nodes. The existing lem-weil-pbc-ringed-exchange-tensor-coherence is reused directly, not duplicated.

## Review by NO

I checked the sources with each proof step's cited statements open. In Step 1 the comparison-site definition supplies a geometric morphism on finite constant-ring modules; comparison-pullback gives the canonical commutation isomorphism, and the constant-ring map node specifies the maps preserving constant sections. These assemble the actual ringed square. The direct-image canonical-mate node says precisely that its beta is the transpose of D(epsilon) a^{-1}; this verifies the orientation of the exchange and identifies both beta_K and beta_H, rather than identifying just their objects. Their bounded-below domains are explicitly available in the hypothesis. The isomorphisms are already named and assumed through that node in the item statement, so no new geometric comparison theorem is being asserted here.

In Step 2 I substituted f = p_et, f' = p_proet, g = nu_Y, g' = nu_Xbar, E = K, Q = B_Y into the full statement of the general ringed-exchange-tensor-coherence node. It explicitly permits noncartesian commutative squares and unbounded module derived categories. Its two displayed composites become beta_H C(pi_K) and Pi (beta_K tensor 1). The tensor-pullback node gives exactly the natural identifications stipulated by the item, and the etale projection definition gives the same counit-transpose projection on the upper right site. The coefficient object B is an A-module throughout. No flatness, perfectness, finite projective dimension or finite-field/algebraic-closure hypothesis is introduced.

Step 3 cancels the tensor of beta_K with the identity and then uses the definition of Pi explicitly contained in the coherence node's statement. Both the displayed transpose and c^{-1} are typed. This is only composition of the equality already obtained and evaluation of that definition, so it is elementary. Step 4 gives an actual two-sided inverse when pi_K is invertible, checking both composites by functor and tensor identities; its only nonformal input is the stated invertibility of both comparison components. I made the quotations substantive (including the relevant formulas), and checked every quotation is an exact substring of the cited statement. proof_deps is precisely the union of step uses. Generic off-unit statements are declared in split_report.tool_uses with their purposes; they implement the unit's existing projection-map route.

Small cases checked: p the identity makes the formula the tensor counit identity; K = 0 and the empty source give the unique maps of zero objects; B = A makes scalar tensor the tensor-unit case; B = 0 makes both sides zero; nonflat Z/ell^2 -> F_ell is allowed whenever the separately stated boundedness of H holds. The inverse argument does not assume that all etale projections are invertible. The statement uses p both in the field characteristic notation and as the map name; the context distinguishes them and no assumption changes. Every step has fewer than 2000 characters; no long step hides another lemma. No new node needs a small-case or duplicate audit. No Lean was written, no compiler/Lake/build tool was run, no sub-agent was started, and no write was made to the shared repository or the live launcher.

## What remains unfinished

Nothing in this one-level split. Its existing dependencies remain the responsibility of their respective items. Delivery is subject to the required server dry run and independent maintainer review.
