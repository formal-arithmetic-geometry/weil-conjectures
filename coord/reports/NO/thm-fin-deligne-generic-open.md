# Stage-1 report: thm-fin-deligne-generic-open

Files written:

- `dag/nodes/sec-smooth-purity/thm-fin-deligne-generic-open.json`: existing statement node marked `split`; no new nodes; Mathlib searches found no matching theorem.
- `citations.json`: verbatim statement quotes for every node cited by every proof step.
- `report.md`: this report.

Attachments: none. I searched both source checkouts for the item id, the expected declaration name, and the blueprint tag; no finished declaration exists.

WANTED: none.

No new node was created. I searched the DAG and both blueprint snapshots for each dependency and reused the existing nodes named by the imported split. The current blueprint statement is unchanged. The source metadata now points to the main-20261015 blueprint proof.

## Review by NO

I read the current item node, the chapter record `dag/chapters/sec-smooth-purity.json`, the unit record `dag/units/sk-prop-sf-cbc.json`, and the current blueprint statement and proof at `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-geo-generic-open/`. I also checked the archived/master source route retained in the node. The source statement has exactly the integral finite-type base, prime-to-characteristic coefficient, finite-type schemes, open immersion, constructible finite sheaf, generic nonempty open, bounded constructibility, and all-Noetherian-base-change clauses; I found no missing or extra hypothesis.

For step 1 I checked the cited statements for exact inverse-image, coefficient-forgetting, restriction of underived and derived direct image, constructibility, and Noetherian-component facts. These statements provide precisely the locality, coefficient comparison, and finite-range reductions used there. For step 2 I read the factorization of quasi-compact immersions, exact finite closed direct image, finite exchange, derived composition, exchange pasting, zero-dimensional Noetherian discreteness, and schematic-closure nodes. They supply the induction extension to immersions, closure reduction, and zero-dimensional base case; the affine killing argument is written out in the step.

For step 3 I checked the coordinate generic-dimension and projective-coordinate-boundary statements. They give the lower-dimensional coordinate reductions and finite complement used to form the common good locus. For step 4 I read the smooth generic direct-image, derived composition, finite-boundary reconstruction, projective-implies-proper, projective closed-model, and schematic-closure statements. They justify compactification, properness, boundedness, and reconstruction of `Rj_*F`.

For step 5 I checked bounded-below proper base change, exchange pasting, smooth generic direct image, coefficient-forgetting, proper stability, and finite-boundary comparison. Their hypotheses match the projective morphism, Noetherian base change, finite boundary, and bounded-below complexes used in the argument, and the step tracks the actual exchange morphism rather than only endpoint isomorphisms.

For step 6 I read the generic radicial smoothing, universal-homeomorphism invariance, base-change-map definition, derived long exact sequence, constructible Serre closure, open-closed recollement, surjective-closed-immersion universal-homeomorphism, and finite-closed-map statements. These support the reduction, triangle, constructibility, and identification of the complement term. For step 7 I checked exact pullback, truncation triangles, triangulated direct image, long exact sequences, Serre closure, triangulated exchange, coefficient-forgetting, composition, finite exchange, and pasting. They give the finite truncation devissage and the exchange isomorphism for the lower-dimensional complement and then for the original sheaf. For step 8 I checked finite radicial exchange descent and finite closed-map finiteness; together with the explicitly written homeomorphism and closed-image argument they give a nonempty open whose full preimage lies in the good locus.

I tested the edge cases described in the proof: empty generic source, zero-dimensional generic source, identity immersion after shrinking, and nonempty radicial descent open. Every proof dependency is an existing node and every citation quote in `citations.json` is copied verbatim from that node's statement. I made no Lean edits, ran no compiler or build, and created no hollow or duplicate node.

## Source error

None found.

## What remains

No unfinished split work remains for this item. The delivery dry run is the remaining required check.
