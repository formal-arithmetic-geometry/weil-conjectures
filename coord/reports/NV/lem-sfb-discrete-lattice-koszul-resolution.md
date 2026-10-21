# Worker report: lem-sfb-discrete-lattice-koszul-resolution

1. Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-discrete-lattice-koszul-resolution.json: item, statement unchanged, split into ten steps; no exact Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-integral-lattice-cubical-contraction.json: one new statement-only algebraic node; unsplit, no Mathlib match.
- citations.json: exact statement excerpts for every step/node pair.
- report.md: this report. searches.jsonl retains every actual search result. Local write_split.py and finalize.py are sandbox helper scripts, not delivery files.

2. Attachments

None. The project source has no exact declaration for the item or the new integral contraction. I searched WeilConjectures for the item id, cubical/lattice/Koszul/invariant notions. The discrete-integer infrastructure and continuous-cohomology comparison declarations in RepresentationTheory concern discrete representations and per-degree cohomology, not internal modules over arbitrary condensed rings or this derived-object comparison. The Koszul braiding and geometric Koszul/Čech files concern different constructions.

3. WANTED: a literature proof of the internal condensed-module lattice derived-invariants comparison with coefficient restriction, for lem-sfb-discrete-lattice-koszul-resolution. WANTED: an explicit integral cubical lattice contracting homotopy reference, for lem-sfb-integral-lattice-cubical-contraction. Existing Stacks Tags 0623 and 062F supply algebraic Koszul context, not either complete statement. The blueprint paragraph (3) does not contain this algebraic argument. Accordingly proof_origin.by is agent; no reference is claimed to prove more than it states.

4. Problems and corrections

The imported statement is mathematically valid and unchanged; no STATEMENT-DISPUTED is needed. Its proof was empty. The inherited blueprint ancestor chain has no imported ancestor: blueprint_refs.py ancestor prints None, so the inherited null from.node is retained and the exact paragraph/place and via chain are filled. The unit record uses the old sec-six-functors sketch whereas this item is filed under sec-six-functors-basics; I read both the recorded unit and the current source paragraph and changed neither. This is a lower algebraic input to the open direct-image calculation and does not replace its geometric route.

I avoided using the profinite-group internal-bar and product-action nodes for the infinite discrete lattice: their hypotheses require profinite groups. I also avoided assuming a free condensed module is categorically projective or that scalar restriction preserves injectives. The proof instead tests an exact augmented cubical complex against equivariant injectives and explicitly handles restricted resolutions.

5. Unfinished work

Only the new statement-only integral contraction is queued for its own later stage-1 split. All arguments needed above that child are supplied in the item's steps, including the scalar and degree-zero clauses. No Lean was written, and no compiler, Lake or local DAG validation script was run.

## Review by NV

I read the current chapter and the recorded unit, the paragraph (3) of the main-20261015 direct-images proof, Stacks more-algebra.tex at definition-koszul-complex (0623) and lemma-regular-koszul-regular (062F), homology.tex at lemma-double-complex-gives-resolution (0133), and derived.tex at lemma-morphisms-lift (013P), lemma-injective-acyclic (05TH), and section-right-derived-functor (0156). The first two describe ordinary Koszul algebra and do not themselves justify internal sheaf coefficients. My proof is explicitly an agent argument using the other cited categorical nodes. For every cited id I opened and read the actual statement, including the equivalence/tensor comparison added during this review. The full statements copied to citations.json can be compared directly with each step.

Step 1 uses the internal/section-ring equivalence and the sheaf tensor structure on the profinite site, then the small-module-diagram Grothendieck theorem with J=BD. D is a small set in the chosen universe, so BD is small; no profiniteness of D is used. The enough-injectives theorem applies to that Grothendieck category, and the resolution definition is exactly the nonnegative augmented exact complex chosen. Invariants' trivial-action adjunction is written out. I corrected an initial implicit identification between internal modules and ringed-site modules by citing the general equivalence, not the scheme-specific derived comparison.

Step 2 uses precisely the new child's integral differential, finite-column homotopies and augmentation. Integer matrices give morphisms between coproducts by the universal property; their contraction identities remain identities for any replacement module Q. The action-site-presentation node permits an arbitrary small sheaf of groups, including the constant condensed discrete group D, and states that forgetting creates kernels/cokernels. Hence an underlying split exact complex is equivariantly exact. The child's contraction is not asserted equivariant. This is an elementary application of the child, not another lemma to queue.

Step 3 reads the explicit j_{S!}R_S construction from the flat-free-sheaf node; it uses its description as a sheafified representable free module, not its flatness conclusion. The tensor-Hom node supplies the closed adjunction, and the internal/section tensor comparison identifies the relative tensors exactly. Adjunction gives tensor preservation of coproducts. Injectivity gives surjectivity on maps from each image subobject, so the augmented section Hom complex is exact. Exactness at every S suffices for sheaf exactness; this direction needs no enough-points theorem. The step proves the needed injective-Hom fact rather than citing a definition of flatness for it.

Step 4 evaluates equivariant maps on [0,I]; translation forces the explicit inverse x_I -> ([v,I] -> T^v x_I). The finite number of subsets makes product and coproduct coincide. Precomposition with the child's signed differential gives the displayed T_i-1 formula, including its sign. In degree zero the augmentation is exactly the invariant inclusion. No separate identification theorem is silently assumed. The cancellation proof of d squared is stated.

Steps 5 and 6 use the first-quadrant total comparison only on first-quadrant double complexes. There are at most r+1 terms on every diagonal, even though the resolution is infinite. For columns, exact finite sums of the underlying-module resolution give the hypotheses. For rows, step 4 applied to each equivariant injective term gives the hypotheses. I verified d_h+(-1)^a d_v and the transpose (-1)^(ab) sign on both directions, and it is 1 on the two axes. The derived-resolution-naturality node states the normalized derived-object comparison itself, not merely a cohomology comparison. These steps build the derived isomorphism, and the commuting augmentation square gives the required map from invariants.

Step 7 uses lift-exists only between two genuine injective resolutions, zero in negative degrees. The uniqueness node applies because the target is bounded below and termwise injective and the source augmentation is a quasi-isomorphism. The total homotopy has sign (-1)^a, making the horizontal cross terms cancel. Thus resolution independence and functoriality are shown on derived objects.

Step 8 uses scalar restriction's actual same-underlying-sheaf definition and the module-sheaf kernel/cokernel statement to prove exactness. The extension is supplied by lift-along-injective-quasi-iso, whose source need not have injective terms: UP'[0] -> UJ is monic and a quasi-isomorphism, the target I is bounded-below injective, and its augmentation extends UP'. This distinction is essential. The equality of the R and restricted R' Koszul double complexes is termwise (same finite sums, action, integer coefficients); row exactness comes from R'-injectivity, while column comparison comes from exact finite sums and beta being a quasi-isomorphism. These two comparisons prove Gamma(beta) is a quasi-isomorphism without assuming UJ injective over R.

Step 9 uses the right-derived-functor definition's unit and its computation equation, and the normalized injective-resolution comparison, to identify the inverse of Gamma(beta) as the canonical coefficient map. The uniqueness-of-lifts node makes this independent of the extension. The b and c squares commute on complexes; their inverses therefore give the requested derived square. I corrected the draft's displayed equation to remove a complex accidentally written as if it were a morphism. Composing this square with the map-functoriality square gives arbitrary f:P -> Res P', not only the identity comparison case.

Step 10 checks r=0: only the a=0 column remains, and normalized derived identity gives the identity of P[0]. The zero ring and zero module give zero complexes. Rank one gives P --(T-1)--> P, not its negative. With all T_i=1 and r=2 the differential is zero and the displayed degrees are P, P^2, P, as expected; no vanishing of positive group cohomology was wrongly imposed.

For the new node I checked r=0 directly and r=1 by writing h_0([n]) as the sum of edges from 0 to n: sum_{k=0}^{n-1}[k,{1}] for n>0, zero for n=0, and -sum_{k=n}^{-1}[k,{1}] for n<0. Its boundary is [n]-[0] and h_0([n+1]-[n])=[n,{1}], including n=-1. For general r the complex is the ordered tensor product over Z of these two-term line complexes. Each line retracts onto Z[0]; the tensor homotopy is the sum of e^{tensor(i-1)} tensor h tensor id on successive factors, with the usual graded sign. Its boundary telescopes to id-e^{tensor r}, giving exactly the child's finite-column contraction. This is a real algebraic lemma below the item: it has no condensed modules, no derived invariants, and none of the item's compatibility conclusions. The statement has no proof sketch inside it and no proof dependencies. The argument here records why I judge it true and hands the next worker its route.

I searched the whole DAG and imported blueprint with Koszul, lattice, Laurent, cubical, contracting homotopy and the source tags; no blueprint node states the new contraction. I inspected the Mathlib hits: simplicial extra-degeneracy homotopy equivalence (ExtraDegeneracy.lean:415) needs a simplicial object with an extra degeneracy; alternatingConstHomotopyEquiv (AlternatingConst.lean:232) contracts a different complex; standardComplex in RepresentationTheory/Homological/Resolution.lean contracts the unbounded bar/standard resolution, not this finite cubical complex; FiniteCyclic.lean requires a finite group and gives a periodic complex. None is an exact or one-line specialization. Both semantic phrasings, Loogle and the Mathlib greps were run using msearch.py and are recorded verbatim from searches.jsonl. No unavailable service was reported as a negative hit.

B-to-E audit: the new node is self-contained with an explicit basis, boundary, augmentation and contraction identities, one level below the item; it has no proof. The item statement is unchanged, all statement notions retain their definition dependencies, every step has source/uses/elementary, and proof_deps is the exact union. Every C1 non-elementary external input is named; C4 quotes are exact node statements. The profinite/discrete hypothesis distinction and restricted-injective issue were explicitly repaired. No proof step exceeds 2000 characters. Off-unit statements are only generic tools declared in split_report.tool_uses, never worker-written tool_uses. No SGA source is used.

## Not duplicates

lem-sfb-integral-lattice-cubical-contraction vs def-weil-pbc-koszul-complex: the existing node defines Koszul complex of a finite sequence of ring elements; it does not assert a contraction of the integral cubical lattice complex.

lem-sfb-integral-lattice-cubical-contraction vs lem-sfb-discrete-lattice-koszul-resolution: the item identifies a derived invariant object and its coefficient maps for internal condensed modules; the child only contracts an explicit integral augmented chain complex.

lem-sfb-integral-lattice-cubical-contraction vs lem-weil-pbc-conormal-intersection-regular-quotient: the existing statement concerns Conormal intersection identity for an ideal quotient generated by a regular sequence; it neither gives the child's integral translation-boundary complex nor its nonequivariant contraction identities.

lem-sfb-integral-lattice-cubical-contraction vs lem-weil-pbc-jacobi-zariski-regular-sequence-left-injective: the existing statement concerns Jacobi-Zariski sequence is exact on the left when the last map is a regular-sequence quotient; it neither gives the child's integral translation-boundary complex nor its nonequivariant contraction identities.

lem-sfb-integral-lattice-cubical-contraction vs lem-weil-pbc-koszul-tensor-cone-coordinates: the existing statement concerns Tensor Koszul coordinates for adjoining the final generator; it neither gives the child's integral translation-boundary complex nor its nonequivariant contraction identities.

lem-sfb-integral-lattice-cubical-contraction vs lem-weil-pbc-koszul-tensor-zeroth-boundary-saturation: the existing statement concerns Degree-zero Koszul boundaries are saturated under a quotient-regular scalar; it neither gives the child's integral translation-boundary complex nor its nonequivariant contraction identities.

lem-sfb-integral-lattice-cubical-contraction vs lem-weil-pbc-regular-quotient-ideal-intersection: the existing statement concerns Intersection with an ideal generated by a regular sequence modulo another ideal; it neither gives the child's integral translation-boundary complex nor its nonequivariant contraction identities.

lem-sfb-integral-lattice-cubical-contraction vs lem-weil-pbc-regular-sequence-koszul-regular: regular sequences give homology vanishing; this does not state an integral nonequivariant contracting homotopy with finite-column maps, which the child needs for arbitrary module replacement.

lem-sfb-integral-lattice-cubical-contraction vs new-d3-koszul-normalized-projective-resolution: the existing statement concerns The Koszul projective resolution with its quotient augmentation; it neither gives the child's integral translation-boundary complex nor its nonequivariant contraction identities.

lem-sfb-integral-lattice-cubical-contraction vs new-d3-koszul-quotient-tensor-homology-basis: the existing statement concerns Exterior basis of quotient-coefficient Koszul homology; it neither gives the child's integral translation-boundary complex nor its nonequivariant contraction identities.

lem-sfb-integral-lattice-cubical-contraction vs new-e1-koszul-conormal-cycle-presentation: the existing statement concerns Koszul wedge cycles present the exterior conormal; it neither gives the child's integral translation-boundary complex nor its nonequivariant contraction identities.

lem-sfb-integral-lattice-cubical-contraction vs new-j3-koszul-projective-resolution: the existing statement concerns The Koszul chain complex is a projective resolution of its quotient; it neither gives the child's integral translation-boundary complex nor its nonequivariant contraction identities.

## Validation

Required server-side dry run and direct delivery are run after this report; their results are recorded below when available.

First dry run stopped at citation validation because the shared action-site node was updated while I worked. Its final kernel/cokernel clause is unchanged; I reread the updated statement and replaced the two whole-statement quotations by that exact clause used by steps 2 and 5. No proof inference changed.

Second dry run requested explicit definition citations in the new node. I read def-weil-pbc-free-module and def-weil-pbc-module-chain-complex-homology and added them as statement dependencies and inline citations: abelian groups are Z-modules, the displayed basis is free, and the displayed differential satisfies the cited chain-complex convention. No mathematical statement changed.
