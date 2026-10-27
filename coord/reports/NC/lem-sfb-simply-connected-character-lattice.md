# Stage-1 delivery: lem-sfb-simply-connected-character-lattice

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-simply-connected-character-lattice.json: item split into the root-system reduction, explicit lattice calculation, central-isogeny contradiction, and character interpretation.
- dag/nodes/sec-six-functors-basics/lem-sfb-semisimple-roots-span.json: statement; no Mathlib match. This is the algebraic-group semisimplicity criterion, not abstract spanning under an IsRootSystem hypothesis.
- dag/nodes/sec-six-functors-basics/lem-sfb-central-lattice-enlargement.json: statement; no Mathlib match. Realizes an arbitrary finite integral enlargement, without a simple-connectedness hypothesis or a weight-lattice conclusion.
- dag/nodes/sec-six-functors-basics/lem-sfb-root-base-rational-integral-spans.json: statement; Mathlib leaf. Base.mk', the two rational basis constructions, and the two integer-span equalities, with source locations in mathlib_match.how.
- citations.json: one verbatim statement excerpt for every citation of each item step.
- searches.jsonl: actual msearch.py searches, including two semantic phrasings for each proposed new node, LeanSearch, Loogle, and source grep.

## Attachments

None. Searched the actual upstream library lean/WeilConjectures both for the blueprint tag and for simply connected, character lattice, fundamental weight, isogeny and semisimple-group terminology. The available group-scheme files concern general definitions, abelian isogenies and rational representations, not this assertion. The item has no finished project declaration.

## WANTED

None. The complete Milne book is present and was read with pdftotext. No SGA source is used.

## Corrections and route

The item was unsplit, with previously recorded Mathlib searches and no proof. Those searches were read and retained; new searches concern the three narrower prerequisites. Fixed doubled TeX backslashes in the item's statement; mathematical content and hypotheses are unchanged. There is no STATEMENT-DISPUTED mathematical change.

Read GOAL.md, the stage-1 brief and contract, the three levels of SETUP.md, worker role, chapter and unit records, and delivery-errors B--E. Read the newest literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, especially (3). This item is a supporting representation-theoretic input far below that direct-image alteration branch, not a unit's key statement. The inherited blueprint ancestor command returns None, and the sandbox preserves that null from.node and the complete inherited place/via chain; new nodes prepend the item to that via chain as prescribed. Blueprint searches for weight lattice, coroot, root datum, root system, semisimple and isogeny found no blueprint duplicate of the proposed prerequisites. The full DAG was also searched by those concepts and Milne source places, restricting the final audit to statements/sources so unrelated numerical search hits do not count as duplicates. No off-unit tool citation is needed.

## Not duplicates

lem-sfb-semisimple-roots-span vs lem-sfb-reductive-borel-pair-structure: the existing statement supplies a possibly nonsemisimple root datum, positive base and semisimple implies reductive; it does not assert that roots span the entire rational character space or give the converse semisimplicity criterion.

lem-sfb-central-lattice-enlargement vs lem-sfb-semisimple-multiplicative-universal-cover: the existing statement gives an unspecified simply connected covering; it gives neither prescribed character lattice L nor the map X -> L. The new statement realizes every finite integral enlargement and does not assert that its source is simply connected.

lem-sfb-central-lattice-enlargement vs lem-sfb-semisimple-central-isogeny-multiplicative: the existing statement proves faithful flatness/diagonalizability of an already given central isogeny. The new statement constructs a central isogeny realizing prescribed lattice data.

lem-sfb-central-lattice-enlargement vs lem-sfb-simply-connected-character-lattice: the item identifies the lattice of a simply connected group; the new prerequisite applies to arbitrary semisimple groups and arbitrary finite integral enlargements. The item itself proves both the weight-lattice calculation and the simple-connectedness contradiction.

lem-sfb-root-base-rational-integral-spans vs lem-sfb-reductive-borel-pair-structure: the existing result introduces algebraic-group roots and a simple-root base. The new leaf is a general rational root-pairing theorem giving simple-coroot bases and integral generation, with no algebraic groups or character-lattice identification.

## Review by NC

I read Milne's printed pp.464--465 (22.8--22.11), p.502 (23.59), the existence theorem and corollary on p.501 (23.55--23.56), the isogeny theorem on p.487 (23.9), its centrality/isomorphism criterion on pp.485--486 (23.5), the semisimplicity criterion on p.439 (21.48), and Appendix C.21--C.26 and C.34--C.35 on pp.612--615. The main proof follows 23.59: if the character lattice were smaller than the weight lattice, realizing the inclusion would contradict simple connectedness. It does not use an unproved claim that fundamental weights already are characters.

For the semisimplicity prerequisite, 21.48 says exactly that group semisimplicity is equivalent to semisimplicity of its root datum; C.34 defines this by rational root spanning. C.35 and 22.9 give the resulting full rational root system. For the lattice-realization prerequisite, C.35 allows the integral lattice between root and weight lattices; 23.55 realizes the root datum, 23.9 realizes the inclusion, and 23.5 gives centrality (all root multipliers one) and the isomorphism criterion. The source does not impose separability: the scheme-theoretic finite kernel can be nonreduced. These are statement-only inputs whose later workers can split the construction; neither repeats the item.

For the Mathlib leaf, I read BaseExists.lean:311--320. Its Base.mk' requires a finite reduced crystallographic root system over a characteristic-zero field, a linearly independent simple-root family, and the signed nonnegative spanning property. The field here is Q, independently of char(F), and all other hypotheses are written in the leaf. Base.lean:298--323 gives the two bases, :131--140 the two integral-span equalities. The support conversion from a finite subset to a finset changes no mathematical datum. The earlier semantic hits called toWeightBasis a weight basis, but the source shows it is the basis of SIMPLE ROOTS; I did not mistake it for the fundamental-weight basis. Fundamental weights are constructed in the item's dual-coordinate calculation instead.

Step 1 cites the Borel-pair node for the actual lattices, perfect integer pairing and simple-root conventions, the semisimplicity prerequisite for full rational spanning, and the Mathlib leaf for the simple-coroot basis and integral generation. I opened each cited statement, and citations.json quotes precisely these conclusions. The group is semisimple, hence reductive as the existing statement explicitly says, so all group hypotheses hold; the abstract field is Q and the root system is finite, reduced and crystallographic.

Step 2 is an elementary calculation using the bases obtained in step 1: integral simple-coroot coordinates characterize P because every coroot is an integer sum. The same coordinates give X contained in P. Simple roots give a full integral sublattice Q contained in X; clearing the finitely many denominators of an inverse rational matrix gives nP contained in Q, so P/X is finite. This writes out the finite-index argument rather than treating it as an uncited theorem. The rank-zero case uses X tensor Q = 0 and freeness of the character lattice, so X = 0.

Step 3 uses the exact statement of the generic enlargement node, not its future proof. At this point P is free of the right rank, contains X with finite quotient, and all its coroot pairings are integral. Its source is semisimple and kernel finite and central as group schemes, exactly the hypothesis quantified over by the item's definition of simple connectedness. The theorem's isomorphism criterion then yields X = P. Step 4 uses the Borel-pair statement's actual definition X = Hom(T,G_m), not a differential or only a character of the Lie algebra. Its remaining content is direct substitution from preceding steps.

I tested the trivial group (empty root system and zero lattices), type A1 with SL2 (root 2omega, weight omega), and PGL2 (proper root/weight inclusion, so the contradiction step correctly does not apply to it). In characteristic 2 the SL2 -> PGL2 kernel may be nonreduced mu_2: the enlargement statement still permits it and never substitutes geometric points for scheme-theoretic kernels. Products of root systems give direct sums of lattices as expected. In the enlargement lemma L = X gives an isomorphism, and rank zero gives the trivial case; no new statement claims a nontrivial rank-zero root system. Every item step is shorter than 2000 characters. I checked B--E against the node files: no proof sketches in unsplit statements, no unintroduced group or coefficient field, all non-elementary inputs cited, no source-only citations replacing nodes, and no target restatement moved into a new node.

## Unfinished work

No unfinished work in this one-level split. The two new unsplit prerequisites are intentional next-stage-1 queue items; the abstract base input is a Mathlib leaf. Delivery awaits the required server dry run and push.

## Dry-run repair

The first server preflight requested a definition citation in the abstract Mathlib leaf and a numeric mathlib_match.line. Added the existing vector-space/dimension definition, whose statement I read, and the verified primary line 298. The root-pairing notions remain fully specified inline, and all clause-specific file/line references remain in how.
