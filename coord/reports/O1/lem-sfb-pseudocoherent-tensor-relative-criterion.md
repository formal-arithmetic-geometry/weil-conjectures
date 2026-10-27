## Worker report

Files written, all under this item's sandbox:

- dag/nodes/sec-six-functors-basics/lem-sfb-pseudocoherent-tensor-relative-criterion.json: existing statement, split into six steps, statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-derived-chow-neighbourhood.json: statement-only prerequisite, Stacks 0CSJ, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-derived-chow-transform-restriction.json: statement-only prerequisite, Stacks 0CSK, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-flat-proper-pseudocoherent-direct-image.json: statement-only prerequisite, Stacks 0CSD, no Mathlib match.
- citations.json: verbatim statements for every use in every step.

Attachments: none. The project source was searched for the exact blueprint tag, pseudo-coherence, relative pseudo-coherence, tensor tests, derived Chow and Fourier--Mukai terminology. The relevant project declarations concern absolute affine/noetherian pseudo-coherence and do not prove this criterion with its hypotheses.

WANTED: none. All mathematical sources were present locally.

The imported item had no proof. Its statement agrees with Stacks 0CSL and is retained, including the absence of properness, flatness and Noetherian hypotheses on X/A. There is no repair order for this item. The inherited blueprint ancestor command returns None; I preserved its null from.node and long via list, rather than editing maintainer-owned provenance. The actual latest blueprint's six-functor unit and its direct-image proof were read; this is a generic algebraic-geometry tool inside the inherited pointed-curve/cohomology-and-base-change prerequisite chain, not a replacement of that unit's route.

Nothing remains mathematically unfinished in the item's assembly proof. The three new nodes are deliberately statement-only and remain future stage-1 items. No Lean was written or compiled.

## Source error

The final display in more-morphisms.tex, Tag 0CSL, writes the restriction of Rq_*(Lp^*K tensor E) to X times V. This object lives on P, so that restriction is ill-typed: X times V is an open of the source T, not the target P. The immediately preceding Tag 0CSK states the correct derived isomorphism after restriction to V. The split uses F|_V throughout. This repairs a typo in the source proof; the item's mathematical statement does not change, so there is no STATEMENT-DISPUTED target statement.

## Not duplicates

The entire DAG was searched by 0CSJ, 0CSK, 0CSD, derived-chow, Fourier--Mukai, pseudo-coherent direct image, and related concept phrases. Whole-blueprint searches used blueprint_refs.py for these tags and phrases. There is no existing node with any of the three new source statements. The one existing textual occurrence of 0CSD is a review note on lem-sc-proper-flat-right-adjoint-open-support, explicitly saying its former 0CSD child was dropped; that node states support preservation by a right adjoint, not pseudo-coherence under direct image.

lem-sfb-derived-chow-neighbourhood vs det-chow-projective-qcqs-chow: ordinary Chow modification gives geometric data, not a pseudo-coherent derived kernel with the prescribed structure-sheaf restriction over a neighbourhood. No substitution of geometric Chow for derived Chow is valid here.

lem-sfb-derived-chow-transform-restriction vs lem-pc-qcqs-derived-projection-iso-universes: projection formula supplies the tensor/direct-image isomorphism for a fixed morphism, not the integral-transform restriction identification for a closed graph with two projections and a specified open restriction. The new node is the derived isomorphism of Tag 0CSK, not a per-degree cohomology claim.

lem-sfb-flat-proper-pseudocoherent-direct-image vs lem-pc-proper-support-perfect-direct-image: the existing node concerns perfect direct images under relative finite-Tor hypotheses; 0CSD applies to arbitrary pseudo-coherent complexes, including complexes unbounded below. Neither perfectness nor finite Tor amplitude is assumed in the new node.

lem-sfb-flat-proper-pseudocoherent-direct-image vs lem-pc-noetherian-proper-bounded-coherent-image: the latter uses Noetherian schemes and bounded coherent complexes; 0CSD works over arbitrary bases and imposes no lower cohomological bound.

None of these three lemmas states a clause of the item: one constructs local kernels, one computes a derived transform, and one is a general preservation theorem. The item still performs the tensor-test argument and the local-to-global relative-coherence conclusion. The existing finite-twist test and flat-ambient criterion were reused instead of creating duplicates.

## Review by O1

I read the complete statement and proof of more-morphisms.tex Tag 0CSL, the complete statements and proofs of 0CSJ and 0CSK, the statement and proof of perfect.tex 0CSD, the equivalences in 0CSG, and the equivalences in more-morphisms.tex 09UU. All tags were checked against literature/stacks-project/tags/tags. The three new statements introduce every object, keep their source hypotheses, and have no proof sketch inside their statements. The 0CSK prerequisite is stated directly with its actual graph data, not by referring opaquely to data supplied by another node.

Step 1 takes all the neighbourhood and kernel data from the new 0CSJ node: it actually supplies the equality of inverse-image opens and the structure-sheaf restriction, not just a modification of X. Step 2 uses projective-space properness and its base-change stability, polynomial-projection flatness, the Proj chart definition, and separated finite-type base change. I checked their full statements. The chart calculation is written out: degree-zero localized monomials are polynomials in coordinate ratios, and coefficient base change gives the charts over any affine open of X. Thus p is flat proper and finitely presented, while q is qcqs. The open V is flat and locally finitely presented over A, with no claim that V is proper or quasi-compact. This distinction is necessary for the last step.

Step 3 uses pseudo-coherent implies quasi-coherent, the actual affine-component pullback and tensor lemmas, K-flat resolution existence, and qcqs pushforward preservation. I checked that the component lemmas are degreewise assertions on affine opens, so explicitly pass from an affine covering to the global quasi-coherence assertion. A K-flat representative is supplied for the tensor lemma; its hypothesis is not silently omitted.

Step 4 uses the invertible-twist definition and the local finite-free definition of pseudo-coherence. Pulling back a local trivialization makes the twist rank one; tensoring preserves the local finite-free model. This is an elementary calculation in the proof, not a new tensor-closure node. Only the non-elementary flat proper direct-image preservation is a new node. Its flatness, properness and finite-presentation hypotheses were checked in step 2. Importantly, X/A itself need not be flat or proper: it is p, the projective-space projection, to which 0CSD applies.

Step 5 cites the unrestricted qcqs projection isomorphism and composition of derived direct images, both read in full. They yield the two displayed derived global-section identifications with B_d and G_d in the correct order; the symmetric monoidal constraints reorder the tensor factors. Pseudo-coherence of G_d lets the item's hypothesis apply. The existing finite-twist criterion requires only d=0 through n and F in D_QCoh, both verified. No stronger all-twists theorem is hidden here, and no finite-Tor or bounded-below hypothesis is introduced.

Step 6 uses exactly the derived isomorphism from 0CSK, with all its graph and open hypotheses supplied in step 1. I corrected the source typo described above. The flat-ambient node actually states that relative pseudo-coherence of K|_U is equivalent to absolute pseudo-coherence of Rj_*(K|_U); it applies with ambient V, whose flatness and local finite presentation were checked. Restriction of a local finite-free model preserves pseudo-coherence. The affine-cover definition of relative pseudo-coherence supplies the final gluing: take together the witness charts on the U covering X for each m. I refreshed citations.json against the live definition, which had been refined while this work was in progress.

I tested the statement and new nodes for K=0, X empty, A the zero ring, and n=0. The empty scheme case is vacuous and has the zero complex; the neighbourhood node has no demanded data when there is no x. For n=0, P=Spec A and there is one twist, so the finite-twist test reduces to the affine case. The transform formula also reduces to the ordinary closed-immersion projection calculation. For an identity proper flat morphism the new direct-image assertion is tautological; the absence of a lower bound is consistent with a bounded-above finite-free complex extending indefinitely to the left. I did not replace the pseudo-coherent kernel with a structure sheaf globally: only the source-guaranteed restriction is used.

I read every search hit returned by the logged commands, including second semantic phrasings. They concern ordinary projective spectra, morphism properties, sheaf pushforward, finite presentation, and flat modules. None states any of the three derived assertions, nor specializes to it in one line. All recorded search queries actually ran with msearch.py and all currently succeeded. Search results and the per-node query plan remain in the sandbox. Every item use has a verbatim statement in citations.json; no quote is paraphrased. All six non-elementary steps are below 2000 characters, and no single step relocates the whole theorem into a child. I checked delivery-errors B--E in this substantive audit and corrected the missing K-flat witness and chart-interface citations before validation.
