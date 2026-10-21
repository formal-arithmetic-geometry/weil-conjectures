## Worker report

Item: lem-sfb-bounded-finite-evaluation-rectangle-replacement. Group O2. Stage 1 only, 2026-10-22. Direct delivery with self-review as authorized by the brief.

### Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-bounded-finite-evaluation-rectangle-replacement.json: statement, split; fourteen explicit steps, no new nodes and no new Mathlib leaves. The statement and its statement dependencies are unchanged.
- citations.json: seven step/dependency entries, each quoting the cited statement verbatim.
- report.md: this report and signed review.

Sandbox-only supporting files: searches.jsonl (the search command's unmodified log), write_split.py (writes the item and citations), check_chains.py (finite formal-chain checks; no Lean or compiler).

### Attachments

None. The project search for the exact blueprint tag and for rectangle/cocycle, homogeneous-cochain and finite-index terms did not find a declaration proving the item. The project file RepresentationTheory/HomogeneousInhomogeneousContinuousCohomology.lean treats discrete coefficients and coordinate conversion, not these normed coefficient spaces or these operators. Transfer for discrete modules likewise does not assert rectangle residual operators. No sorry declaration is treated as finished.

### WANTED

WANTED: an exact human-written reference for bounded, coefficient-independent finite-evaluation rectangle replacement for continuous cochains with possibly incomplete nonarchimedean vector-space coefficients. The item's original source already asks for it. Its existing blueprint source, main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3), gives the open-direct-image route, not this auxiliary lemma. Accordingly the proof is explicitly agent-written. Stacks etale-cohomology.tex, Tag 0DVG, section-continuous-group-cohomology, was read for the actual continuous differential, and simplicial.tex, Tag 019S, lemma-homotopy-s-N, was read for the alternating-chain homotopy context; neither is claimed to state the rectangle theorem. No forbidden SGA source is used. Literature and repository coordination files are read-only under this brief, so this request is recorded here for the maintainer.

### What changed and what was wrong

The item had an empty proof and mentioned a finite-chain join comparison and transfer without giving either construction. The full construction is now in the item: the existing integral ordered-join filling operator gives a partial chain map from tuples in G to the ordered coset join; a recursively defined prefix homotopy compares its erased map to the identity. Averaging the resulting H-invariant functions over H\G restores G-invariance. Every coefficient is an integer divided by the prime-to-ell index, hence has norm at most one.

The existing rectangular-detection node concludes existence of a primitive on H; it does not state the fixed coefficient-independent evaluation formulas or their bounds. The existing continuous transfer node states a continuous homotopy but does not assert the integral-coefficient/norm bound. Neither statement is used for stronger conclusions. Instead their relevant finite constructions are written and checked here, using only the explicitly stated ordered-join lemma. This avoids C3/C4 without creating a new node restating the item.

The imported blueprint unit record has older sec-six-functors text; I also read the actual current source paragraph in sec-six-functors-basics. This is a subsidiary arithmetic obligation for paragraph (3), and changes no unit or chapter route. The ancestor command returns None because created.item at lem-sfb-admissible-direct-image is a Lean module name. The inherited from.node null and via list are retained; from.place and split_report.blueprint identify the exact current blueprint paragraph, whose node is det-thm-sf-ctf-stability-direct-images. Searches of the whole imported blueprint for ordered join, homogeneous cochain and finite evaluation found no statement identifying this item; same_as remains empty.

### Searches and reuse

Read the current DAG statements of lem-sfb-ordered-join-partial-contraction, lem-sfb-homogeneous-cocycle-rectangle-detection, lem-sfb-topological-homogeneous-cochain-coordinates, lem-sfb-continuous-cochain-finite-index-transfer, and the parent finite-quotient descent node. Whole-DAG keyword searches found the ordered-join lemma, which is reused rather than recreated. No new nodes or tags are introduced, so there are no same-tag new/existing pairs.

The five additional Mathlib queries were run only through the required msearch command and appended with their exact tool, query and result object, retaining the item's earlier search history. Both LeanFinder phrasings returned low-degree cohomology or standard/bar resolution and Dold-Kan declarations; LeanSearch returned cocycle definitions and the inhomogeneous differential; Loogle and the RepresentationTheory grep returned no hits. I read Mathlib/RepresentationTheory/Homological/Resolution.lean and GroupCohomology/Basic.lean to check the relevant hits. They do not state the rectangle comparison with finite continuous evaluation substitutions and norm-one averaged coefficients. No failed service was recorded as an absence result.

## Not duplicates

No new nodes. In particular, no duplicate of lem-sfb-ordered-join-partial-contraction or lem-sfb-homogeneous-cocycle-rectangle-detection was created. The former supplies the needed general filling identity; the latter lacks the quantitative operator conclusion of this item.

## Review by O2

I read the item, the current blueprint paragraph (3), its chapter record, the unit record, and all four statements actually cited in the fourteen steps, with delivery-errors B through E open. The item quantifies over all n >= 1, nonnormal open H of prime-to-ell index, arbitrary coset anchors, and incomplete coefficient spaces. None of these hypotheses has been strengthened. No new statement-only nodes need a separate source or small-case review.

Step 1 uses lem-sfb-topological-homogeneous-cochain-coordinates exactly for its actual cochain isomorphisms Phi and Psi and their differential identities, including degree zero. Its statement explicitly allows arbitrary topological vector spaces and requires no completeness or discreteness. The trivial action is jointly continuous, and the given norm axioms supply the required continuity of vector operations. Step 2 proves the continuous H-equivariant retraction rho on the clopen right cosets; the side of the coset and the formula rho(hx)=h rho(x) were checked. No normality assumption is used.

Step 3 uses def-weil-pbc-free-module only for the specified formal basis convention. The deletion differential and its square-zero identity are proved directly, and F's additive extension concerns finite sums. Step 4 applies the statement of lem-sfb-ordered-join-partial-contraction to r=n+1 and X_i=Ha_i. Its identity is available through degree r-2=n-1, which is exactly the range used in step 5. Its naturality and finite expansion without equality tests are actual clauses of its statement, used in step 6. The top chain has increasing colors 0,...,n, so rectangle vanishing does not require vanishing on any permutation of the rectangle.

Step 5's induction has an explicit augmentation base and proves that the input to S is a cycle before applying the cited identity. Step 6 uses the cited naturality with the changed anchor h rho(x_0); it does not incorrectly assert that a fixed-anchor contraction is equivariant. The finite expression is uniform because color lists are fixed and repeated terms need not be combined. Both statements taken from the ordered-join node were checked against its statement, not its proof.

Steps 7 and 8 give the prefix identity and the full base/induction calculation of the concrete Q used here. They invoke no unstated comparison theorem. In particular Q_n is constructed as well as Q_(n-1), since its boundary is needed when a cocycle is evaluated. Step 9 proves equivariance and finite continuous substitutions by the same recursion; its only inserted vertices are original x_j or rho(x_j)a_i. This is a finite algebraic construction, not a topology on the chain groups or an existence argument for continuous choices.

Step 10 evaluates the displayed chain identity, using F boundary = 0 for a cocycle. This gives the residual identity on all G-tuples, before averaging. Its residual vanishes on the ordered rectangle by the range of A_n, and its cocycle identity follows by applying the displayed differential and square-zero identity. Step 11 checks the averaging permutation explicitly from sg=hu; it works for nonnormal H. The normalization is 1/m exactly once, and the average is the identity on already G-invariant F. Deletion commutes with each simultaneous translation, so there is no missing differential compatibility.

Step 12 cites the same coordinate node for the cochain identities, and writes the actual composition of tuple substitutions giving the required finite evaluation maps in the inhomogeneous coordinates. It defines the operators on every cochain, even though the decomposition is required only on cocycles. Step 13 uses def-weil-l-adic-numbers for the valuation of integers and of the prime-to-ell integer m; the bound then follows termwise from the norm axioms, without a theorem about integration. Compactness gives bounded suprema. No coefficient subspace is required to be closed. Step 14 fixes the parameter in each explicit continuous substitution and checks the n=1 bottom degree rather than dropping it. All continuity arguments use finite sums only.

For the mathematical small-case checks I ran check_chains.py, a finite integer-chain calculation, for n=1,2,3 on the trivial group, on C3 with H=1, and on S3 with H the subgroup generated by a transposition. The latter H is nonnormal, of index 3 (prime to ell=2). It checked the P chain identities, the full 1-A = boundary Q + Q boundary identity, H-equivariance, and the color order/coset membership of every top output term. It exhausts all tuples through degree 2 in these groups and checks additional degree-3 tuples. All nine cases passed (769 basis tuples, each with the relevant subgroup translates). Separately, n=1 has Q_0[x]=[x,x]-[x,rho(x)a_0], so averaging gives an invariant degree-zero homogeneous cochain, whose differential is zero as required. H=G needs no averaging, zero V gives zero maps, and an empty parameter space gives the unique family. Coincident anchors do not affect colors or the formulas.

Against B1-B10: there are no new nodes; the item is self-contained and unchanged, with TeX formulas, retained source/search records and actual project attachment searches. Against C1-C8: each non-elementary external fact is one of the cited coordinate/contraction statements, and the other calculations are written out; citations.json quotes every cited statement verbatim. The free-module and l-adic-number definition nodes are used only for definitions and valuations. All nondefinition proof dependencies have the same unit. Against D1-D5: no clause was moved into a fresh lemma; both finite chain inductions and the averaging argument are carried by the item, with no unspecified standard comparison step. Against E1-E7: all degree ranges, right-coset conventions, nonnormal subgroup actions, and incomplete coefficients were checked above; there is no statement correction or source-error claim. No step exceeds 2000 characters, and none hides a separately invoked comparison or identification lemma.

The self-review corrected a potential insufficient citation before writing: instead of citing the existential rectangle-detection or qualitative transfer statements for quantitative norm bounds, the explicit integral constructions were retained. The signed review is O2's own reading, as required by the direct-delivery brief; no second worker or agent was started.

### Unfinished work

No part of the item's split remains unfinished. The exact literature reference remains WANTED as in the imported item; the proof is marked agent-written. The dependency lem-sfb-ordered-join-partial-contraction remains an existing unsplit node for its own future item. Its statement, rather than any proof internals, is the cited input here.

### Validation

Finite-chain checks passed as described above. The required server dry run exited 0 and printed: OK (not pushed) deliver/O2/lem-sfb-bounded-finite-evaluation-rectangle-replacement at 0ee676ebfb4: preflight passed. This includes the server preflight, check_dag and review_split gates. Final push follows this successful dry run; its resulting commit is printed by deliver.py.
