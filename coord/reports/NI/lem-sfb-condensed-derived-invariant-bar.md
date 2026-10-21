# Stage-1 report: lem-sfb-condensed-derived-invariant-bar

Group NI; direct delivery; 2026-10-21.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-condensed-derived-invariant-bar.json`: item, statement unchanged, split into nine proof steps; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-condensed-internal-bar-resolution.json`: one new statement-only, unsplit node; no Mathlib match. It states the exact augmented homogeneous internal bar resolution and its tensor exactness, with the continuous induced-coordinate description. It does not state the derived invariant comparison.
- `citations.json`: verbatim supporting statements for every cited node of every item proof step.
- `searches.jsonl`: actual msearch output records. Earlier item searches in the live node are retained. All additional queries were run and their hits read. One batch initially used the proposed new-node id in the msearch item argument; its genuine records were moved into this item's log and the accidental empty directory was removed. No search result or digest was invented or changed.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and for condensed/internal bar and invariant terminology. No project declaration states this theorem. The ordinary abstract-group bar result in Mathlib and the discrete continuous-cohomology nodes are not attachments to an internal condensed assertion.

## WANTED

WANTED: a reference for the augmented internal homogeneous bar resolution and ordinary derived invariants of internal modules with an internal profinite group action, for lem-sfb-condensed-internal-bar-resolution and lem-sfb-condensed-derived-invariant-bar. The source blueprint only motivates the tame-boundary calculation; it does not supply this internal categorical proof. The ordinary abstract-group bar resolution is an analogy, not evidence for replacing the coefficients by discrete modules. Accordingly the item's proof origin is agent, and the new lemma explicitly requests this reference.

## What needed repair

The item had no proof. The statement already carefully distinguishes derived internal functions from underived continuous functions and from topological-module cohomology. I kept those distinctions and every assertion of the item. No STATEMENT-DISPUTED was found.

The chapter/unit records were read, followed by the current main-20261015 unit text and the direct-image proof paragraph (3). This proof refines only the formal internal group-invariant input below the Kummer-boundary calculation. It replaces no geometric step of the unit. The unit JSON still records the older source/chapter location; I did not edit it. The blueprint ancestor command returns None for this inherited created.item chain, as it already does for neighboring created nodes; the item and new node retain null from.node and record the precise current blueprint place and via chain.

Self-review corrected a genuine C4 hazard: the bounded-below injective replacement node does not promise a degree-zero lower bound. Instead the scalar step uses a nonnegative injective resolution of the object Res N', and the strict lifting theorem 013P to compare Res J to it. The restricted A'-injectives are never asserted to be A-injective. I also made uniqueness of lifts a separate existing citation and wrote the (-1)^p total-homotopy sign explicitly.

## Not duplicates

lem-sfb-condensed-internal-bar-resolution vs lem-sfb-bar-resolution-cochains: the latter is the ordinary integral abstract-group projective resolution and its all-functions complex; the new node concerns arbitrary condensed-ring coefficients, an internal profinite action, and exactness after internal tensor. Projectivity is expressly not claimed.

lem-sfb-condensed-internal-bar-resolution vs lem-sfb-condensed-derived-invariant-bar: the new statement is only the augmented homogeneous algebraic resolution, before taking internal equivariant Hom or right derived invariants. The item's nine steps prove the derived-object comparison, its compatible model, and its naturality and scalar normalization; these conclusions are absent from the new node.

lem-sfb-condensed-internal-bar-resolution vs lem-sfb-condensed-product-action-inflation: the existing statement gives the abelian categories and inflation/invariant adjunctions, with no bar resolution or tensor-exact augmented complex.

Whole-DAG and blueprint searches were run for coinduction, homogeneous/augmented/internal bar resolutions, free internal modules, and their source terminology. Broad matches in scalar Hom, internal derived Hom, and Ind-module nodes do not state the new resolution. No Stacks tag is claimed as a source for the new internal resolution. The existing flat free sheaf node at Tag 03EV and generic scalar-Hom node were reused, rather than recreated.

## Review by NI

I read delivery-errors B through E, the stage-1 brief and stage document, the three blueprint levels in SETUP, GOAL, the chapter/unit records and the current direct-image proof. For the item I read its statement, all nine final steps, the exact statement of every cited node, and Stacks sites-modules.tex at lemma-extension-by-zero (03DI) and lemma-j-shriek-flat (03EV), homology.tex at lemma-first-quadrant-ss (0132) and lemma-double-complex-gives-resolution (0133), and derived.tex at lemma-morphisms-lift (013P), lemma-morphisms-equal-up-to-homotopy (013S), and section-right-derived-functor (0156). The derived scalar-Hom input is the existing node's evaluation-normalized statement, read as a generic ringed-site tool, rather than a claim extracted from its proof.

For the new node I read the current blueprint paragraph (3) and Mathlib's classifyingSpaceUniversalCover, barComplex, isoStandardComplex and barResolution in RepresentationTheory/Homological/Resolution.lean, and the scalar-coefficient limitations of Condensed.profiniteFree and LightCondensed.ihomPoints. These sources do not state the internal theorem, so the new node remains unsplit with an honest WANTED source. Its intended proof, recorded here rather than in its statement, is to insert the identity as the first homogeneous coordinate: h[g0,...,gn]=[1,g0,...,gn] and h_-1(a)=[1]a. Alternating deletion gives dh+hd=1 on the underlying augmented complex, and the same equality holds after tensor with any T. The contraction need not be equivariant: exactness is reflected by forgetting the action. Consecutive-coordinate differences give the stated induced-module identification. All maps are continuous polynomial group operations on profinite powers and therefore define internal maps after every parameter base change.

Step 1 uses exactly the Grothendieck-abelian and exact-inflation/invariants clauses of lem-sfb-condensed-product-action-inflation, then the enough-injectives statement. The recursive cokernel construction is the actual nonnegative resolution; it does not use an unjustified truncation.

Step 2 uses 03EV's exact tensor statement for the represented profinite parameter S. The identification of its module with A[S] is checked by its free universal property, with explicit basis restrictions. The elementary induced/forgetful adjunction is written by [g] tensor t maps to g f(t); the argument for underlying injectivity then uses precisely the extension property in def-sp-injective-resolutions. The closed tensor-Hom node supplies that adjunction for internal modules. No claim that A[S] is projective or internally projective is used.

Step 3 uses exactly the new node's tensor-exact augmented resolution with T=A[S], then the injective extension property. Factoring through kernels and quotients proves exactness after contravariant Hom. This establishes exactness on every profinite parameter, hence exactness as a sheaf. It never applies evaluation to an arbitrary sheaf-epimorphism and assumes it surjective.

Step 4 uses only the new node's induced-coordinate description and the existing closed structure. I checked the first, interior, and last faces by deleting homogeneous coordinates. For p=0 the differential really is gm-m and the augmentation is the invariant inclusion, so there is no action-convention inversion.

Step 5 uses the normalized injective-resolution computation theorem, applied to the common underlying injective resolution proved in step 2. This supplies entire derived objects, not just per-degree cohomology. The total-complex definition gives the sign and finite diagonals. All resolution degrees and cosimplicial degrees are nonnegative.

Step 6 applies the actual statement of the generic first-quadrant comparison to the row quasi-isomorphisms after switching indices. I checked the (-1)^(pq) change of total convention, and checked that K has only its p=0 column. Thus this is an isomorphism in the derived category with the correct augmentation; no convergence for an unbounded diagonal is assumed.

Step 7 uses the existing lifting statement for nonnegative object resolutions and the existing 013S uniqueness statement, which permits equality after augmentation as a special case. The total homotopy is (-1)^p times the vertical homotopy. This gives resolution independence and functoriality of the actual comparison, not unrelated choices of cohomology isomorphisms.

Step 8 uses 03EV for A[S] and the generic scalar-Hom adjunction with the variable condensed ring sheaves A and A', on the same small site. The latter explicitly asserts naturality in both variables and normalization by evaluation. The free universal property identifies derived scalar extension of A[S] with A'[S]. Hence the comparison commutes with parameter maps and the action face. It requires no flatness of A' over A and no perfection of the profinite free module.

Step 9 uses the strict 013P lifting node on the monic quasi-isomorphism from the single Res N' into Res J, targeting the nonnegative injective resolution K. These are precisely its hypotheses, including monicity in every degree and boundedness below. The two augmentations imply beta is a quasi-isomorphism. The first-quadrant comparison then compares columns; the row comparison compares the invariant augmentations. This identifies scalar restriction on the derived invariant map with exactly the termwise internal-Hom map asserted by the item. Exactness of restriction follows directly from retaining the underlying module-sheaf kernels and cokernels; injectivity after restriction is not assumed.

Small cases checked: G=1 gives the constant cosimplicial internal-Hom diagram with alternating 0/id differentials and normalized total N[0]; A=0 and N=0 give zero complexes and the same formulas; a finite nontrivial group gives the usual bar faces without introducing finiteness or invertibility of its order. The zero-degree check is invariants, including the first action face. The new augmented contraction works in degrees -1, 0 and 1 and with arbitrary tensor T, so it does not need flatness of T. For scalar restriction, A'=A is the identity, and quotient ring maps remain allowed: the proof never invokes flatness of restriction's left adjoint. Every final proof step has fewer than 2000 characters; the genuinely separate augmented-resolution lemma is the one new node. No SGA route, Lean write, compiler, Lake, repository edit, or direct git command was used.

## Unfinished work

The one new resolution node is deliberately statement-only, as required by a one-level split. Its proof is a future item. No part of the item's proof or its requested naturality clauses is intentionally left open. Required delivery dry run and push results follow below when completed.
