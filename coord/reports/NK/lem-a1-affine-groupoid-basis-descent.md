# Stage-1 repair: lem-a1-affine-groupoid-basis-descent

## Files written

- dag/nodes/sec-purity-real-sheaves/lem-a1-affine-groupoid-basis-descent.json: unchanged statement; short assembly of three independent statement-only tasks.
- lem-a1-affine-groupoid-coordinate-identities: statement, unsplit; no exact Mathlib match. Groupoid geometry and coordinate-ring bookkeeping, formerly steps 1-2.
- lem-a1-twisted-tensor-invariant-coefficients: statement, unsplit; no exact Mathlib match. Base change of the basis and the coefficient comparison, formerly steps 3-4.
- lem-a1-invariant-coefficients-reconstruction: statement, unsplit; no exact Mathlib match. Retraction, descended basis and specified tensor-ring isomorphism, formerly steps 5-6.
- citations.json: one verbatim statement quotation for each of the three assembly citations.

## Attachments

None. I searched WeilConjectures for the blueprint tag, affineGroupoid_basis_descent and groupoid/basis/invariant/retraction terminology. There is no matching completed project declaration. The existing Sheaf.AlgebraicGeometry.AffineGroupoidBasisDescent declaration has sorry and is not an attachment. No Lean was written or compiled.

## WANTED

None. All mathematical sources used are present locally.

## What was wrong and what changed

The released repair note dated 2026-10-22 overrides the earlier passing review: the 3556-character proof must be distributed among workers. At session start this sandbox contained only brief markers, no earlier node, report or search log. The mandatory initial dry run exited with FAILED: no node files under the sandbox dag/nodes directory. I copied the current shared-repository node, preserving its statement, existing searches, blueprint ancestry, Lean metadata and historical reviews. No git command was run in the read repository. The supplied return entry and coord/repair-notes/lem-a1-affine-groupoid-basis-descent.json agree; the current node carries exactly the six returned proof steps and the same 3556 characters. There was therefore no distinct retained node or report to rebase. The full returned proof is preserved below, verbatim.

Three new statements of comparable sizes replace that work: 1123, 909 and 961 characters. The parent assembly has 1248 characters, and no step exceeds 2000. Each new node has proof [], proof_deps [], proof_origin null and status unsplit. The first isolates the geometry without any basis hypothesis or descent conclusion; the second isolates coefficient invariance without a groupoid or retraction; the third assumes coefficient invariance explicitly and isolates the reconstruction. In particular the third cannot replace the original theorem: its additional hypothesis is precisely the substantive result supplied by the second node, which in turn needs the first node's identities. No one new node carries the original argument. Every original argument is allocated to one of these three tasks, not omitted or compressed out of the work queue.

The chapter and unit records were read and not changed. The blueprint ancestor remains lem-a1-affine-hc0 through the finite-flat affine-relation quotient chain. This remains the supporting Stacks 03C8 route, with the original tensor orientation and ring map. No SGA source is used. No mathematical statement dispute was found.

## Searches and Mathlib verdicts

I searched the whole DAG by 03C8, 02YE, lemma-diagram, twisted tensor, invariant coefficients, common retraction and groupoid coordinate terminology. tools/blueprint_refs.py ancestor returned lem-a1-affine-hc0; its searches for 03C8, groupoid basis, invariant coefficients, common retraction, twisted tensor and groupoid coordinate found no matching imported statement. The broader groupoid search found seven unrelated blueprint statements. The broad tensor-comparison search likewise found no equalizer/retraction result here. Searches are retained in searches.jsonl and each new node records the actual queries and returned names, including the unsuccessful Loogle identifier attempt, rather than inventing results.

All Mathlib searches used msearch.py. Each new node has LeanFinder, LeanSearch, Loogle and grep records, with a second wording. I read the returned hits. Coalgebra/Bialgebra results use one algebra structure and do not encode this affine groupoid's two maps A to B. FreeGroupoid.lift_spec concerns categorical free groupoids. IsBaseChange.basis (Mathlib/RingTheory/TensorProduct/IsBaseChangeFree.lean, lines 31-60) assumes an already supplied base-change witness; it does not prove our invariant coefficients or reconstruct the descended basis. The existing DAG base-change leaf already covers its usable basis fact. Algebra.IsEffective.eqLocus_includeLeft_includeRight (IncludeLeftSubRight.lean, lines 86-103) identifies a particular tensor equalizer given effectivity, not these two arbitrary ring maps. The tensorEqualizer results require linear/algebra maps over a common base and flatness; they do not state the coefficient comparison for the twisted tensor. Subalgebra.LinearDisjoint.basisOfBasisRight/Left (LinearDisjoint.lean, lines 264-307) require linear disjointness and an existing subalgebra basis, which are not the data of our statements. They are not one-line specializations. Accordingly all three tasks remain unsplit, with no new Mathlib leaf. Searches for the parent are retained from its prior delivery because its statement and search question have not changed.

## Review by NK

I read coord/delivery-errors.md B-E in full, the stage-1 brief, stages/1-dag.md, the three blueprint levels in SETUP.md, GOAL.md, the worker role, chapter and unit, and the released repair note. I read Stacks groupoids.tex lemma-basis (Tag 03C8), both diagrams and the final conclusion, together with lemma-diagram (02YE), lemma-diagram-pull (03C6), and the surrounding finite-flat quotient proof (03BM). I verified those tags against tags/tags. These are the sources for the item and all three new nodes; the new nodes specify their exact portion of 03C8 rather than citing a moving section number.

For assembly step 1 I opened the new coordinate-identities node and checked that its statement supplies precisely the counit identities, tensor identification, balancing and composition identities used. Its schemes and maps are exactly those in the parent. In particular the first tensor factor is B through sigma and the second B through tau, so p0 sigma = p1 tau, Delta sigma = p1 sigma and Delta tau = p0 tau. The proof task includes evaluating the functorial groupoid laws at U and at the composable-pair scheme; it does not assume composition is cartesian. I also read def-a1-groupoid-scheme, def-weil-affine-spectrum, def-pc-fibre-product, the affine fibre-product node and the tensor-ring universal-property node. The definition gives the required groupoid laws, affine functoriality reverses composition, the affine fibre-product lemma identifies both projection maps, and the tensor-ring node really provides the needed multiplication and inclusions. No definition is being cited as a substitute for an existence theorem.

For assembly step 2 I opened the new twisted-tensor node. It requires only the two displayed Delta identities and the original basis assumption, which are now available. Its statement explicitly supplies both the basis over the second B and invariance of every coefficient in tau(a). I rechecked the allocation of the old proof: base change along tau uses the RIGHT tensor version of lem-weil-pbc-free-module-base-change-free (whose statement I opened), not the basis over the wrong B. Applying Delta to the expansion gives coefficients sigma(a_j); applying p0 gives tau(a_j) by balancing. The vectors in both expansions are p0(tau(x_j)), so uniqueness compares coefficients in B itself. This is a substantive algebraic lemma, not the parent's geometric hypothesis or either final clause. No faithful-flatness, reducedness, finiteness of the rings, or equivalence-relation assumption has been added.

For assembly step 3 I opened the reconstruction node and checked every hypothesis: epsilon retracts BOTH maps by step 1, the B-basis is the parent's given basis, and invariant coefficients come from step 2. Its statement supplies the actual x_j as basis, not merely existence of some free module structure, and specifies the tensor-ring map on every pure tensor. I reread def-weil-pbc-free-module and the tensor-pushout universal-property statement: the latter supplies a ring map for two C-algebra maps which agree on C, not just a linear map. The remaining assigned proof is epsilon applied to the expansion for spanning, tau applied to a C-relation for independence, then base change of the C-basis and a basis-to-basis map for bijectivity. All of this remains a future task, stated without proof steps; its full old proof is below. The tensor orientation gives 1 tensor x_j on the source and tau(x_j) on the target as required.

The three parent uses lists have exactly these three nodes, and citations.json quotes their statements verbatim. Prior-step conclusions in steps 2 and 3 are explicit, so no hidden appeal to another node's proof is made. Non-elementary argument is assigned to the new nodes; the parent merely instantiates their statements. All objects are introduced afresh in each new statement, and tensor rings and bases cite the nodes defining/providing them. I checked that no new dependency refers back to the parent, so the decomposition is acyclic by construction.

Small cases: for the identity groupoid A=B, sigma=tau=id, epsilon=id, rank one x=1, all identities, invariance and reconstruction hold with C=A and A tensor_A A=A. For A=k x k and B=A tensor_k A (the pair groupoid), C is the diagonal k, the two standard idempotents form the descended basis and the specified tensor map is the identity after the standard identification. For the nonreduced example A=k[epsilon]/(epsilon^2), B=A tensor_k A, the basis (1,epsilon) gives the same coefficient comparison; no cancellation or domain assumption enters. If A=0, a common retraction forces B=0 and all coefficient modules are singleton sets; finite nonempty indexed zero bases are valid over the zero ring. For the coefficient lemma even without a retraction, if B=0 its basis hypothesis with r>=1 forces A=0 by uniqueness, so this edge case is consistent. The original r>=1 restriction is preserved. I did not add any nontrivial-ring assumption.

I corrected the former undivided work allocation only. The statements remain faithful to 03C8's finite nonempty case; no original mathematical claim was weakened. The discussion above checks B1-B10, C1-C8, D1-D5 and E1-E7 in substance: statement-only tasks, self-contained objects, actual sources and searches, no duplicate, exact citations, no route change or circularity, and explicit orientation and edge cases.

## Not duplicates

lem-a1-affine-groupoid-coordinate-identities vs def-a1-groupoid-scheme: defines groupoids but states no affine coordinate-ring consequence or basis descent theorem.

lem-a1-affine-groupoid-coordinate-identities vs lem-a1-affine-groupoid-basis-descent: is the unchanged geometric theorem; the three extracted tasks respectively give coordinate identities without a basis, coefficient invariance without a groupoid/retraction, and reconstruction assuming invariant coefficients.

lem-a1-affine-groupoid-coordinate-identities vs lem-a1-finite-flat-affine-relation-quotient: asserts representability and finite locally free quotient properties for a finite locally free equivalence relation, not this algebraic subargument.

lem-a1-affine-groupoid-coordinate-identities vs lem-a1-affine-groupoid-invariant-rank-strata: asserts invariant rank decompositions under finite local freeness, not coordinate identities or coefficient/basis descent.

lem-a1-twisted-tensor-invariant-coefficients vs def-a1-groupoid-scheme: defines groupoids but states no affine coordinate-ring consequence or basis descent theorem.

lem-a1-twisted-tensor-invariant-coefficients vs lem-a1-affine-groupoid-basis-descent: is the unchanged geometric theorem; the three extracted tasks respectively give coordinate identities without a basis, coefficient invariance without a groupoid/retraction, and reconstruction assuming invariant coefficients.

lem-a1-twisted-tensor-invariant-coefficients vs lem-a1-finite-flat-affine-relation-quotient: asserts representability and finite locally free quotient properties for a finite locally free equivalence relation, not this algebraic subargument.

lem-a1-twisted-tensor-invariant-coefficients vs lem-a1-affine-groupoid-invariant-rank-strata: asserts invariant rank decompositions under finite local freeness, not coordinate identities or coefficient/basis descent.

lem-a1-invariant-coefficients-reconstruction vs def-a1-groupoid-scheme: defines groupoids but states no affine coordinate-ring consequence or basis descent theorem.

lem-a1-invariant-coefficients-reconstruction vs lem-a1-affine-groupoid-basis-descent: is the unchanged geometric theorem; the three extracted tasks respectively give coordinate identities without a basis, coefficient invariance without a groupoid/retraction, and reconstruction assuming invariant coefficients.

lem-a1-invariant-coefficients-reconstruction vs lem-a1-finite-flat-affine-relation-quotient: asserts representability and finite locally free quotient properties for a finite locally free equivalence relation, not this algebraic subargument.

lem-a1-invariant-coefficients-reconstruction vs lem-a1-affine-groupoid-invariant-rank-strata: asserts invariant rank decompositions under finite local freeness, not coordinate identities or coefficient/basis descent.

lem-a1-affine-groupoid-coordinate-identities vs lem-a1-twisted-tensor-invariant-coefficients: the coordinate task has groupoid data and no basis; the coefficient task has a Delta map and gives invariance; the reconstruction task has a common retraction and assumes invariance, and gives the basis and tensor comparison. These are distinct interfaces and arguments.

lem-a1-affine-groupoid-coordinate-identities vs lem-a1-invariant-coefficients-reconstruction: the coordinate task has groupoid data and no basis; the coefficient task has a Delta map and gives invariance; the reconstruction task has a common retraction and assumes invariance, and gives the basis and tensor comparison. These are distinct interfaces and arguments.

lem-a1-twisted-tensor-invariant-coefficients vs lem-a1-invariant-coefficients-reconstruction: the coordinate task has groupoid data and no basis; the coefficient task has a Delta map and gives invariance; the reconstruction task has a common retraction and assumes invariance, and gives the basis and tensor comparison. These are distinct interfaces and arguments.

## What remains

Nothing in this stage-1 repair is left unassigned. The three new tasks intentionally have no proofs, for other workers to split. Delivery checks are run through the required remote delivery command only.

## Retained returned proof, verbatim, and allocation

### Former step 1, assigned to lem-a1-affine-groupoid-coordinate-identities

Put $\varepsilon=e^\sharp:B\to A$. The identity-arrow laws give $s\circ e=t\circ e=\mathrm{id}_U$: evaluate the assumed groupoid laws on the test scheme $U$ and its identity morphism. Contravariant functoriality on affine spectra gives $\varepsilon\sigma=\varepsilon\tau=\mathrm{id}_A$, so both $\sigma$ and $\tau$ are injective. Also $C$ is a unital subring of $A$: the equality $\sigma(a)=\tau(a)$ is preserved by addition, negation and multiplication, and holds for $1$. Equip $A$ with its inclusion $C\to A$ and $B$ with the common restriction $\sigma|_C=\tau|_C$.

### Former step 2, assigned to lem-a1-affine-groupoid-coordinate-identities

Let $P=R\times_{s,U,t}R$. The affine fibre-product formula identifies its coordinate ring with $D=B\otimes_{\sigma,A,\tau}B$, where $A$ acts on the first copy of $B$ through $\sigma$ and on the second through $\tau$. Write $p_0(b)=b\otimes1$, $p_1(b)=1\otimes b$, and $\Delta=c^\sharp:B\to D$. Tensor balancing gives $p_0\sigma=p_1\tau$. The source and target laws for composition give $\Delta\sigma=p_1\sigma$ and $\Delta\tau=p_0\tau$: for a composable pair of arrows $(\alpha,\beta)$ with $s(\alpha)=t(\beta)$, the composite $\alpha\circ\beta$ has source $s(\beta)$ and target $t(\alpha)$. These are equalities of scheme maps because the asserted pointwise laws apply to the test scheme $P$ and its pair of projections; take their pullbacks on global sections. Thus no cartesian assertion about the composition map is being assumed.

### Former step 3, assigned to lem-a1-twisted-tensor-invariant-coefficients

Apply the free-module base-change statement to the first copy of $B$, free over $A$ through $\sigma$ with the given basis $(\tau(x_j))_{j=1}^r$, along $\tau:A\to B$ into the second copy. Its right-tensor version says exactly that $y_j=\tau(x_j)\otimes1=p_0(\tau(x_j))$ form a basis of $D$ as a module over the second copy of $B$, acting through $p_1$. In particular, if $\sum_jp_1(b_j)y_j=\sum_jp_1(b'_j)y_j$, then $b_j=b'_j$ for every $j$. The two copies of $B$ have different $A$-structures here, and the coefficient ring of this basis is the second copy itself.

### Former step 4, assigned to lem-a1-twisted-tensor-invariant-coefficients

Fix $a\in A$, and use the assumed basis to write $\tau(a)=\sum_j\sigma(a_j)\tau(x_j)$ uniquely with $a_j\in A$. Apply $\Delta$ and use step 2 to obtain $p_0\tau(a)=\sum_jp_1\sigma(a_j)y_j$. Applying $p_0$ to the very same expansion and using $p_0\sigma=p_1\tau$ instead gives $p_0\tau(a)=\sum_jp_1\tau(a_j)y_j$. Uniqueness of coefficients in the basis of step 3 yields $\sigma(a_j)=\tau(a_j)$ for each $j$. Hence every coefficient $a_j$ belongs to $C$.

### Former step 5, assigned to lem-a1-invariant-coefficients-reconstruction

Apply $\varepsilon$ to the expansion in step 4. Step 1 gives $a=\sum_j a_jx_j$ with $a_j\in C$, proving spanning over $C$. If $\sum_j c_jx_j=0$ with $c_j\in C$, apply $\tau$ to get $\sum_j\sigma(c_j)\tau(x_j)=0$, since $\tau(c_j)=\sigma(c_j)$. The assumed $A$-basis of $B$ says that each $c_j=0$ in $A$, hence in its subring $C$. Thus the $x_j$ are a $C$-basis of $A$.

### Former step 6, assigned to lem-a1-invariant-coefficients-reconstruction

The maps $\sigma,\tau:A\to B$ agree on $C$, so the tensor-product ring universal property gives a ring map $\phi:A\otimes_C A\to B$ with $\phi(a\otimes a_2)=\sigma(a)\tau(a_2)$. It is $A$-linear when the source uses the first tensor factor and the target uses $\sigma$. Base change of the $C$-basis in step 5 gives the $A$-basis $(1\otimes x_j)$ of $A\otimes_C A$. The map $\phi$ sends this basis to the assumed $A$-basis $(\tau(x_j))$ of $B$. Explicitly, every $b=\sum_j\sigma(b_j)\tau(x_j)$ is the image of $\sum_j b_j\otimes x_j$; and if $z=\sum_jb_j\otimes x_j$ maps to zero, uniqueness for the target basis gives all $b_j=0$, hence $z=0$. Therefore $\phi$ is bijective, and is an isomorphism of rings. This proves both conclusions with the specified comparison map.
