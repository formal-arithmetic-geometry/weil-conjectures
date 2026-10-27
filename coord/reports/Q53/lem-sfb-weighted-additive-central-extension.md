## Worker report

Files written (all under dag/nodes/sec-six-functors-basics/):
- lem-sfb-weighted-additive-central-extension.json: item, split into eight steps; statement unchanged.
- lem-sfb-monic-principal-open-fppf.json: statement, unsplit; no complete Mathlib match.
- lem-sfb-unit-power-fppf-surjective.json: statement, unsplit; no complete Mathlib match.

No attachments. The searches of lean/WeilConjectures/ by the blueprint id and central-extension/equivariant-splitting concepts found no declaration stating this item or the new scheme-cover lemmas. Weights.lean concerns weights of representations, not fppf group-sheaf extensions. No Lean was written and nothing compiled.

WANTED: Brian Conrad, Reductive group schemes, https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, Proposition 4.3.1 and Lemma 4.3.2, printed pp.127–128, for lem-sfb-weighted-additive-central-extension. I read the online PDF; no archival copy was found under literature/. The proof_origin is agent, as required when the document is not archived locally. No SGA source was used.

The original node was statement-only, with no proof to retain and no local item copy. I retained its statement, source, original searches and blueprint chain. The latest blueprint unit and direct-images proof were read under literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/. The DAG unit record has an older chapter path; I changed neither it nor the inherited route. blueprint_refs.py ancestor returns None, as it does for the parent. The item continues its relative SL2 prerequisite in the recorded direct-image route; there is no route substitution.

The inherited separatedness assumption is retained. The explicit fppf argument in fact uses only the stated sheaf and centrality hypotheses for Z; it avoids extending equalities from geometric points or from a dense open over a nonreduced base. In Conrad the torus action is conjugation by a lift. Here the given action supplies it directly; the only property needed for equivariance of alpha_t minus identity is commutation of the torus actions, already part of a G_m action.

All work is finished to the stage-1 boundary: the two new nodes are statement-only and queued unsplit. There are zero Mathlib leaves. This is a split, not a proof in Lean.

## Searches and existing nodes

I searched the whole DAG by central extension, commutator pairing, monic polynomials, power maps, roots of units, fppf and the Stacks tags 00FB and 040N. I searched the whole imported blueprint with blueprint_refs.py for commutator, central extension, faithfully flat, monic, root of, power map, Kummer sequence, unit root and monic principal. No blueprint node states either new lemma. The generic finite-locally-free quotient descent node lem-a1-fppf-kernel-pair-quotient-descent assumes a specified quotient map and does not construct either cover; no need to cite it because the local-lift constructions and gluing are written out.

Every recorded Mathlib query ran through msearch.py and is present in searches.jsonl. I read the search results and the relevant sources: GroupExtension/Defs.lean has an abstract-group splitting as data (and objectwise surjectivity), not the current sheaf theorem. IsOpenComapC.lean:35,52 describes the image of a polynomial principal open, but does not supply the flat locally finitely presented scheme morphism theorem. AdjoinRoot.lean:593 and its surrounding monic quotient construction give a basis, not the fppf-sheaf power-surjectivity theorem. Semantic searches were repeated with ring-presentation and scheme-cover formulations before recording no match. One grep on a file path produced malformed file labels because of rg's single-file output; I reran the relevant grep on the RingTheory directory, obtaining the correct AdjoinRoot.lean:593 path. No leaf is claimed from those partial results.

## Not duplicates

lem-sfb-unit-power-fppf-surjective vs lem-amb-kummer-any-base: the latter requires n invertible and is etale; the new node is fppf, allows every positive n, and is needed for n=2 in characteristic 2.
lem-sfb-unit-power-fppf-surjective vs lem-sc-kummer-exact: the latter assumes a curve over an algebraically closed field and n prime to the characteristic; the new node has arbitrary base and no invertibility hypothesis.
lem-sfb-unit-power-fppf-surjective vs lem-sfb-pointed-cover-compatible-unit-roots: the latter normalizes tame roots on a particular pointed universal cover; it requires prime-to-characteristic orders and does not cover the inseparable square-root case here.
lem-sfb-monic-principal-open-fppf vs lem-sfb-additive-subgroup-polynomial-quotient: the latter constructs a finite additive-polynomial quotient over a field. The new node is the projection of a principal open of the affine line over any ring and need not be finite or a group map.
lem-sfb-weighted-additive-central-extension vs lem-sfb-relative-torus-bimultiplicative-vanishing: the latter is a pairing on two multiplicative groups. It cannot be used for the additive commutator pairing here.
No existing node with source tag 00FB or 040N was found. Neither new lemma restates a clause of the item: both concern covers, and neither assumes an extension or concludes a splitting or commutativity.

## Proof plans for new nodes

For lem-sfb-monic-principal-open-fppf, use the explicit algebra A[T,Y]/(YP-1). Polynomial rings are flat over A and localization is flat over A[T], hence the composite is flat. Its displayed two-generator, one-relation presentation proves finite presentation. The image computation in Stacks 00FB (algebra.tex, lemma-affineline-open, proof) says the image of D(P) is the union of the principal opens of its coefficients. A monic coefficient is 1, so the image is all Spec A. Equivalently each fibre is k[T,1/Pbar], nonzero since Pbar is monic. I also read algebra.tex, lemma-flat-localization, Tag 00HT, for the flatness input. This is a general scheme-cover lemma, not merely a unit-choice clause copied from the item.

For lem-sfb-unit-power-fppf-surjective, use Stacks 040N (etale-cohomology.tex, lemma-kummer-sequence-syntomic), proof read in full. On an affine T=Spec A and a unit a, A[X]/(X^n-a) is free of rank n with basis 1,...,X^(n-1), so faithfully flat for n>0 and finitely presented. Its universal root b is a unit with inverse a^(-1)b^(n-1). These covers on affine opens give the claimed cover for every T. No derivative or etaleness is asserted or needed.

## Source error

The local Stacks text of Tag 040N says n in N without excluding n=0. At n=0 the power map is constant 1, so is not locally surjective: take S=Spec Q and a=2; the root algebra A[X]/(1-2) is zero and cannot cover the nonempty base. Its own rank-n faithful-flatness proof requires n>0. The new node explicitly states n>=1, which is the intended positive-order Kummer assertion and includes the only order used here (2). The item itself is unchanged and has no statement dispute.

## Review by Q53

I read Conrad Proposition 4.3.1's additive commutator paragraph on printed p.127 and all of Lemma 4.3.2 on p.128. I matched the given action with its conjugation action and checked that the commutator descends without assuming representability or smoothness of F. I also opened the complete statements of both new nodes and their cited definition nodes (scheme, spectrum, polynomial ring, flat morphism and local finite presentation). The new statements introduce their own rings, schemes, integer and unit; their dependencies define exactly the notions used. They contain no proof steps or hidden proof sketches.

Step 1 uses only central exactness and the sheaf gluing given in the item's statement. Lifts exist locally, their commutator is in the kernel, and changing lifts by central sections does not change it. Step 2 is the explicit class-two group identity; no general cohomology or central-extension theorem is being silently cited. These are elementary computations and local gluing, not independent mathematical prerequisites.

Step 3 cites lem-sfb-unit-power-fppf-surjective precisely for a square root of a unit. Its hypotheses hold over each test scheme, including characteristic 2. For the negative weight I take a square root of a^(-1), not of a. The node's quoted sentence really asserts local existence of the root, with no n-invertibility assumption. I use only this local surjectivity, not a property buried in its proof.

Step 4 cites lem-sfb-monic-principal-open-fppf with P=t(t+1)(t^2+t+1), a monic polynomial over every commutative ring. The cited statement really supplies a flat, locally finitely presented, surjective cover, not just an open map. I recomputed delta=-(t^2+t+1)/(t(t+1)); all its factors are inverted on the cover. I checked each of the three biadditivity factors and the substitution v↦delta^(-1)v. This makes the commutator vanish over all test schemes, with sheaf descent replacing a density argument. No claim that two geometric points determine a morphism is made.

Step 5 uses the same cover lemma for monic t(t^2-1), including its surjectivity. I checked t^(-2)-1=-(t^2-1)t^(-2), so the scalar is a unit for both signs. The invariant-homomorphism conclusion follows from the displayed homomorphism identity and substitution. This is the argument for that clause, not a new node restating it.

Step 6 again uses exactly the cover statement for t(t^2-1), now over an affine base open. Central exactness supplies local lifts over arbitrary test schemes; triviality of the action on the kernel proves lift-independence. Commutativity has already been proved in step 4 before additivity of alpha_t-id is used. The map d is constructed on sections with unique gluing; it is not an object chosen from a mere existence assertion. qd=a id and the inverse scalar give the section.

Step 7 writes the full commutation calculation for alpha_s and alpha_t; it does not assume any lift of s to F or any linear structure on F. Step 8 uses the previously proved vanishing clause for the difference of two group sections; this difference is a homomorphism because F is commutative and takes values in Z because both sections lie over the identity. This holds after every base change and therefore proves agreement on overlaps. I wrote out the resulting sectionwise gluing rather than assuming descent of a representable F. All node citations in steps 3–6 have exact verbatim quotes in citations.json; all other steps have no external fact beyond their written elementary arguments.

Small cases checked: S empty and A the zero ring (all covers and section identities are vacuous); P=1 gives affine-line projection; n=1 gives the identity power map; n=2 over F_2 or a nonreduced F_2-algebra gives a finite free, possibly inseparable root cover. Over F_2 the avoidance covers have geometric points even though F_2 itself has no t outside {0,1}; t^2+t+1 and t(t^2-1) remain nonzero monic polynomials in every residue field. The trivial kernel gives F=G_a and the constructed section is the inverse of q. The product extension Z×G_a yields d(z,u)=(0,au) and j(u)=(0,u). Neither separatedness nor reducedness was used to infer an equality from pointwise data. No hypotheses were added to the item, no conclusion removed, and no SGA route introduced.

I checked delivery-errors B–E against these files: no duplicated or elementary node, no new copy of the item, no non-elementary uncited premise in the assembly, no use of another node's proof, and no dependency back to the item from either new node. All eight proof steps are below 2000 characters. Corrections during self-review were the explicit inverse scalar for k=-2, use of fppf rather than etale root covers in characteristic 2, the positive n restriction at Stacks 040N, and rerunning the file-path grep with a directory so its recorded hit paths are accurate.
