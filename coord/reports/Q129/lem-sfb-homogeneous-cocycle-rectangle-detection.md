# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-homogeneous-cocycle-rectangle-detection.json`: retained the statement verbatim and replaced the nine-step proof by five assembly steps, totaling 2063 characters. All existing attachment, provenance, search and review fields are retained.
- `dag/nodes/sec-six-functors-basics/lem-sfb-ordered-join-coset-comparison.json`: statement, status unsplit; no Mathlib match. Extracts the augmented comparison P, its chain identity, equivariance, uniform integral coordinate formula, and color-erasing map A=eP.
- `dag/nodes/sec-six-functors-basics/lem-sfb-homogeneous-tuple-prefix-homotopy.json`: statement, status unsplit; no Mathlib match. Extracts the prefix contraction and recursion Q for an arbitrary supplied finite-formula equivariant augmented map A, its homotopy identity, equivariance, and uniform formula.
- `citations.json`: one verbatim quotation for every cited node in every assembly step.

The sandbox initially contained only dispatcher marker files, with no node, report or searches.jsonl. I copied the current read-only item, whose nine steps and lengths match the returned entry, and preserved it as original-node.json. No prior completed sandbox work was discarded. The live item's existing Mathlib searches were read and retained unchanged; only the two genuinely new arguments were searched anew. No repository git command, Lean writing, compiler, Lake or local preflight/check_dag/review_split was used.

## Attachments

None. Searching WeilConjectures by blueprint tag and homogeneous-cocycle/rectangle concepts found no exact proved declaration. The recorded Sheaf theorem Representation.homogeneous_cocycle_rectangle_detection in HomogeneousCocycleRectangleDetection.lean has `sorry`; its statement agrees with the unchanged item and its docstring records the same nine arguments. It is not a completed attachment.

## WANTED

WANTED: a reference for a continuous-coefficient partial-resolution comparison with uniform finite integral coordinate formulas, for the item and both new nodes. The current main-20261015 blueprint, sk-thm-sf-ctf-stability-direct-images.proof.md paragraph (3), motivates the surrounding direct-image argument but does not contain the arithmetic cocycle calculation. These are honestly agent-written extractions, not attributed to a nonexistent Stacks tag. The report below supplies the complete inherited argument for future workers. No SGA source was used.

## Repair of the return

The human asked for work to be distributed, at least two comparable new statement-only nodes, and an assembly of at most 3000 characters without blurring the old argument. The new statements are 2172 and 2146 characters. Each has an empty proof and proof_deps, null proof_origin, status unsplit, complete hypotheses, blueprint provenance and seven real logged searches. Neither mentions a cocycle or a primitive: the first constructs a map into a truncated colored join, while the second takes any supplied augmented finite-formula map and constructs a homotopy in the full tuple complex. They can be assigned as separate work. The old item still proves its coefficient, topology and rectangle clauses in its own short assembly.

Old steps 2–4 are carried by the comparison node: the exact P recursion remains in its statement, as do naturality-based equivariance and the full uniform expansion. Old steps 5–7 are carried by the prefix-homotopy node: the exact C, Z and Q formulas, the homotopy and equivariance conclusions and the full uniform expansion remain in its statement. Old step 1 is assembly step 1; rectangle vanishing from old step 2 is assembly step 2; old steps 8 and 9 are assembly steps 4 and 5. The original proof is reproduced below, without shortening, so no argument was lost when the new nodes were delivered statement-only. There was no statement dispute and no change to a target or unit route.

## Searches

Before creation I searched all DAG node statements/titles for ordered join, prefix homotopy, homogeneous cocycle, bar resolution and projective resolution homotopy; I read the closest statements, rather than using their proofs as interfaces. tools/blueprint_refs.py search was run for ordered join, chain homotopy, bar resolution, homogeneous cocycle, prefix and rectangle. No blueprint statement supplies either new conclusion. Its ancestor command returns None for this existing created.item chain; I retained the inherited null ancestor and prefixed the item to each via list, with precise paragraph and old-step locations.

For each new node I ran leanfinder, loogle, leansearch and grep through the required msearch.py, plus a second natural-language phrasing and focused source greps. Every query/result/digest recorded on the nodes is taken verbatim from searches.jsonl; all services answered. The hits Rep.standardComplex, Rep.barComplex and their differentials describe the ordinary resolutions; neither constructs the ordered-color comparison. I read Mathlib/RepresentationTheory/Homological/Resolution.lean, including the extra degeneracy based on the identity vertex and the alternating differential. For the second node, Homotopy.mkInductive at Algebra/Homology/Homotopy.lean:528 asks for component constructions and their homotopy identities; I read its parameters and docstring. It does not establish the input-dependent prefix recursion or uniform coordinate lists. ExtraDegeneracy.homotopyEquiv and Dold–Kan homotopies concern other supplied simplicial data, not the claimed equivariant formula for arbitrary A. These are partial implementation tools, not one-line specializations proving either entire new statement. Hence zero Mathlib leaves.

## Not duplicates

lem-sfb-ordered-join-coset-comparison vs lem-sfb-ordered-join-partial-contraction: the existing node gives a chosen-anchor contraction on the colored join itself; the new node constructs P from homogeneous H-tuples using a different first-coordinate anchor at each input, with equivariance and uniform formulas.
lem-sfb-ordered-join-coset-comparison vs lem-sfb-bar-resolution-cochains: the existing node gives the inhomogeneous group-ring resolution and its cochains; it has no finite colored join, P, or rectangle image condition.
lem-sfb-ordered-join-coset-comparison vs def-coef-ordered-join: the existing node defines the join of simplicial sets; it does not assert an integral comparison map from H-tuple chains to ordered coset chains.
lem-sfb-ordered-join-coset-comparison vs lem-sfb-homogeneous-cocycle-rectangle-detection: the new statement has no coefficient space, topology, f or primitive; its output is a partial chain map rather than the parent conclusion.
lem-sfb-homogeneous-tuple-prefix-homotopy vs lem-sfb-projective-resolution-homotopy-equivalence: the existing node assumes two exact projective resolutions and gives unspecified comparison maps and homotopies; the new node fixes a truncated A and proves a specific equivariant recursion and its uniform coordinate formula without those assumptions.
lem-sfb-homogeneous-tuple-prefix-homotopy vs new-t4-augmented-resolution-lift-homotopy: the existing node is an abstract projective-resolution lifting and uniqueness theorem in an abelian category; no fixed coordinate formula or first-coordinate prefix recursion is supplied.
lem-sfb-homogeneous-tuple-prefix-homotopy vs new-h2-quotient-tensor-resolution-lift-homotopy: the existing node concerns lifts along a ring map between projective quotient resolutions, with no homogeneous tuple construction or uniform coordinate templates.
lem-sfb-homogeneous-tuple-prefix-homotopy vs lem-sfb-finite-index-rectangle-primitive-operator: the existing node gives an operator on rational l-adic cochains with finite-index transfer and bounds; the new node is an integral homotopy for any supplied A and requires no cocycle, topology, finite index or coefficient module.
lem-sfb-homogeneous-tuple-prefix-homotopy vs lem-sfb-bounded-finite-evaluation-rectangle-replacement: the existing node gives bounded rational l-adic cochain replacement with a prime-to-l index condition; the new integral chain statement contains none of those conclusions or hypotheses.
lem-sfb-homogeneous-tuple-prefix-homotopy vs lem-sfb-homogeneous-cocycle-rectangle-detection: the new node neither detects vanishing nor produces a continuous coboundary; A is arbitrary supplied data and its conclusion is the algebraic finite-formula homotopy.

## Review by Q129

I read the item, the chapter record sec-six-functors-basics, unit sk-thm-sf-ctf-stability, the current main-20261015 direct-images proof paragraph (3), and the recorded Lean theorem and full proof docstring. This confirms that the arithmetic chain argument is an existing agent expansion below the route, not a theorem contained in the blueprint. The initial return was a granularity repair; the subsequent landing return at head 41065a83f01 asks for rebasing onto the current DAG and rereading changed citations, as recorded below. I compared the copied statement literally with the live JSON and did not change any hypothesis or conclusion.

For the comparison node I read the statement of lem-sfb-ordered-join-partial-contraction: it provides the exact S operator, its identity through degree r-2 including degree -1, naturality for maps preserving the chosen vertices, and equality-independent finite formulas. Setting r=n+1 permits the recursion to apply S in degree q-1 up to n-1, never in the unsupported top degree n. Each Ha_i is nonempty and left H-stable even if H is not normal. Labeling them separately handles coincident cosets. In degree zero P[h]=[(0,ha_0)] has augmentation one. At q>=1 the old induction computes d(P(dx))=0; the contraction then gives dP=P d. Left translation changes anchors ha_i to gha_i, exactly the naturality hypothesis. Insertions/replacements use only h_j a_i and deletion only chooses subtuples, proving the uniform formula without input-dependent cancellation. Erasing labels commutes with deletion, and a top symbol has every color once. I corrected an intermediate wording that appeared to give an arbitrary set Y an H-action: the final statement specifies the actions only on B(H), B(G) and the coset join. It also explicitly types P_q:B_q(H) to J_q.

For the prefix node I checked its own A hypotheses independently of the first new node. The first node supplies A=eP with augmentation identity, chain identity and equivariance; its coordinate templates are a special case of the second node's permitted h_j and h_j a_i templates. The prefix boundary is d[b,y]=[y]-C_b(d[y]), including C_b(1)=[b]. Its equivariance is gC_b=C_gb g, not equivariance for a single fixed b. The augmentation of Z_0 is zero, and for q>=1 dZ_q=0 follows by substituting the preceding homotopy identity and d squared zero. Prefixing with h_0 gives the correct sign I-A=dQ+Qd. Equivariance follows because the first coordinate changes to gh_0, and all finite templates are stable under subtraction, deletion and prefixing. The node deliberately allows n=0, where Q_0[h]=C_h([h]-A_0[h]) still has the asserted boundary; the item itself still requires n>=1.

For each assembly citation I checked the statement used. Step 1 cites def-weil-pbc-free-module only for specified finite basis expansions, and explicitly gives the boundary sign cancellation, the additive extension F, and Fd=0. Step 2 cites the comparison statement for A's chain identity, augmentation, H-equivariance, fixed formulas and top rectangle span. Applying F to each spanning tuple uses the parent's actual rectangle hypothesis. Step 3 cites the prefix statement for the homotopy and both formula and equivariance conclusions; all A hypotheses were checked in step 2. Step 4 cites the same statement for the uniform formula and equivariance of Q, and def-kun-subspace-topology for continuity of H into G. Product projections, coordinatewise continuous maps, composition, and finite sums/negations are elementary consequences of the stated topologies and continuity hypotheses; this step makes each map explicit. No topology on formal chains is introduced. Step 5 cites the displayed I-A identity in the prefix statement, then evaluates it using the already proved FA=0 and Fd=0. Its equality is of actual cochains, not a class in a separated quotient. citations.json uses literal snippets from these statements, with a separate entry for each use.

I checked B1–B10, C1–C8, D1–D5 and E1–E7 against the final files: both new nodes have only statements and honest search records, introduce every object, cite the exact construction they use, retain single-escaped TeX and precise source provenance, are genuinely separate arguments, and introduce no backward dependency on the parent. They are neither elementary one-line facts nor rewordings of the parent's conclusion. No non-elementary parent step exceeds 2000 characters. Both new proofs are left empty as required, rather than hidden in proof_deps or proof_origin. No external-unit theorem is introduced into the parent proof.

Small-case checks: by hand n=1 gives Q_0[h]=[h,h]-[h,ha_0], and the repeated-entry cocycle relation gives f(h,h)=0, so t(h)=-f(h,ha_0), agreeing with the inherited sign. The partial contraction is only needed below top degree, so nonzero top join homology is harmless. The Python formal-integer-chain experiment in check_small_cases.py checked 325 tuples in degrees 0 through n for n=1,2, with H trivial, H a nonnormal order-two subgroup of S3, and H=S3. It verified dP=P d, the top ordered-color condition, I-A=dQ+Qd, dZ=0, and P/Q equivariance. These include repeated vertices, coincident cosets and noncommuting translations. The exact construction uses integer coefficients only, so reduction to characteristic two or any other characteristic does not divide by a forbidden integer. Zero coefficients and the zero coefficient space are harmless. Openness, completeness and Hausdorffness are not used by either algebraic new node; continuity in the parent needs only the given induced topology and continuous operations. The experiment supports the edge-case audit and is not a replacement for the future formal proofs.

## Complete inherited arguments for the new workers

The following is the original nine-step proof, verbatim. Steps 2–4 belong to the new ordered-join comparison task, steps 5–7 to the new prefix-homotopy task; the rest records their original assembly and topology use. This preserves every calculation and qualification from the returned proof while leaving both new node files statement-only.

### Original step 1

Use integral formal chains: for a set $Y$, let $B_q(Y)$ be finite integer sums of ordered $(q+1)$-tuples from $Y$, with repeated entries allowed, using the specified tuple basis [def-weil-pbc-free-module], and let $B_{-1}(Y)=\mathbf Z$ generated by the empty tuple. The boundary $d$ is alternating deletion, with $d[y]=1$. Deleting positions $i<j$ in the two possible orders gives signs $(-1)^{i+j-1}$ and $(-1)^{i+j}$, so $d^2=0$, including augmentation. Extend $f$ additively to $F:B_n(G)\to M$. The stated cocycle identity says exactly $Fd=0$ on $B_{n+1}(G)$. Equivariance of $f$ and additivity of the action imply $F(gz)=gF(z)$.

Cited nodes: def-weil-pbc-free-module.

### Original step 2

Apply [lem-sfb-ordered-join-partial-contraction] with $r=n+1$ and $X_i=Ha_i$ as separately labeled sets. Write $J$ for its augmented chains. Erasing color labels gives $e:J_q\to B_q(G)$; it commutes with $d$ because both boundaries delete the same ordered positions. Every degree-$n$ basis symbol has colors exactly $0,\ldots,n$ in that order, so the rectangle hypothesis gives $Fe=0$ on $J_n$. For each $h\in H$ choose the anchors $v_i(h)=ha_i$. The cited operator $S^h$ satisfies $dS^h+S^h d=1$ through degree $n-1$, including degree $-1$.

Cited nodes: lem-sfb-ordered-join-partial-contraction.

### Original step 3

Construct augmented homomorphisms $P_q:B_q(H)\to J_q$ for $-1\leq q\leq n$. Set $P_{-1}=1$ and $P_0[h_0]=[(0,h_0a_0)]$, so $dP_0=P_{-1}d$. Suppose $P$ has been constructed through $q-1$, with $1\leq q\leq n$. For a basis tuple $x=[h_0,\ldots,h_q]$ put $z=P_{q-1}(dx)$ and define $P_q(x)=S^{h_0}_{q-1}(z)$, then extend additively. The induction hypothesis gives $dz=P_{q-2}d^2x=0$ (for $q=1$ use the already checked augmentation identity). Since $q-1\leq n-1$, the cited contraction gives $dP_q(x)=z$. Thus $dP_q=P_{q-1}d$ in every required degree. The anchor is selected separately on each input basis tuple; no claim of a single fixed-anchor chain contraction being $H$-equivariant is made.

Cited nodes: lem-sfb-ordered-join-partial-contraction.

### Original step 4

For $g\in H$, left translation maps $X_i$ to $X_i$ and takes $v_i(h)$ to $v_i(gh)$. Naturality in [lem-sfb-ordered-join-partial-contraction] therefore gives $gS^h(z)=S^{gh}(gz)$. Induction in the formula for $P_q$ now gives $P_q(gx)=gP_q(x)$, the base $q=0$ being $(gh_0)a_0=g(h_0a_0)$. Its finite-formula clause also gives, inductively, an expansion of each $P_q[h_0,\ldots,h_q]$ as a fixed finite integer sum of symbols whose vertices are $h_j a_i$. Indeed the boundary selects coordinate subtuples and the operator only inserts or replaces vertices by $h_0a_i$. All coefficients, color lists and coordinate choices are independent of the values of the $h_j$; coincident vertices are retained as uncancelled formal terms if necessary.

Cited nodes: lem-sfb-ordered-join-partial-contraction.

### Original step 5

Let $I_q:B_q(H)\to B_q(G)$ be coordinatewise inclusion and set $A_q=eP_q$. Both are augmented chain maps through degree $n$, both are $H$-equivariant, and $I_{-1}=A_{-1}=1$. For $b\in G$ define $C_b:B_q(G)\to B_{q+1}(G)$ by prefixing $b$, also $C_b(1)=[b]$ in degree $-1$. Direct deletion gives $d[b,y_0,\ldots,y_q]=[y_0,\ldots,y_q]-C_b(d[y_0,\ldots,y_q])$; in degree $-1$ it gives $d[b]=1$. Thus $dC_b+C_b d=1$ in all augmented degrees. Moreover $gC_bz=C_{gb}(gz)$.

Cited nodes: none.

### Original step 6

Define $Q_{-1}=0$. Inductively, for $0\leq q\leq n$ and $x=[h_0,\ldots,h_q]$, put
$$Z_q(x)=I_qx-A_qx-Q_{q-1}(dx),\qquad Q_q(x)=C_{h_0}(Z_q(x)),$$
and extend $Q_q$ additively. For $q=0$ the augmentation of $Z_0$ is $1-1=0$. For $q\geq1$, the previous identity $dQ_{q-1}=I_{q-1}-A_{q-1}-Q_{q-2}d$ and the chain-map identities give
$$dZ_q=(I_{q-1}-A_{q-1})dx-(I_{q-1}-A_{q-1}-Q_{q-2}d)dx=0.$$
The prefix identity of the previous step therefore gives $dQ_q(x)=Z_q(x)$, hence
$$I_q-A_q=dQ_q+Q_{q-1}d.$$
This establishes the induction, including its base, without a resolution-comparison existence theorem.

Cited nodes: none.

### Original step 7

The recursion for $Q$ is equivariant: assuming it for $Q_{q-1}$, equivariance of $I,A,d$ gives $Z_q(gx)=gZ_q(x)$, and the identity for prefixing gives $Q_q(gx)=C_{gh_0}(gZ_q(x))=gQ_q(x)$. The base $Q_{-1}=0$ is equivariant. Likewise the finite-formula property for $A$, followed by subtraction, deletion and prefixing, proves by induction that every $Q_q[h_0,\ldots,h_q]$ has a fixed finite integer expansion in tuples whose coordinates are either some $h_j$ or some $h_ja_i$. This uses the explicit expansion proved in step 4; it introduces no choices or equality tests depending on the input.

Cited nodes: none.

### Original step 8

Define $t(h_0,\ldots,h_{n-1})=F(Q_{n-1}[h_0,\ldots,h_{n-1}])$. This is defined because $n\geq1$. The preceding expansion writes $t$ as a fixed finite sum of integer multiples of values $f(b_0(h),\ldots,b_n(h))$, where each $b_k(h)$ is a coordinate inclusion $h_j\in G$ or its right translate $h_ja_i$. The inclusion $H\to G$ is continuous by [def-kun-subspace-topology]; finite product projections are continuous by definition of the product topology, and right translation is continuous by the given multiplication. Hence every substituted tuple map is continuous, and so is its composite with $f$. Finite sums, negation and repeated addition are continuous by the hypotheses on $M$. Therefore $t$ is continuous. No topology on the formal chain groups is needed.

Cited nodes: def-kun-subspace-topology.

### Original step 9

For $g\in H$, equivariance of $Q_{n-1}$ and of $F$ gives $t(gh_0,\ldots,gh_{n-1})=g\,t(h_0,\ldots,h_{n-1})$. In degree $n$ the homotopy identity gives
$$FI_n-FA_n=FdQ_n+FQ_{n-1}d.$$
Here $FA_n=FeP_n=0$ by the ordered rectangle hypothesis (step 2), and $FdQ_n=0$ by the homogeneous cocycle identity (step 1). Consequently $f(h_0,\ldots,h_n)=FQ_{n-1}d[h_0,\ldots,h_n]=\sum_{i=0}^n(-1)^i t(h_0,\ldots,\widehat{h_i},\ldots,h_n)$, as required. This is an equality of actual cochains; the construction uses only finite integer sums, so it applies in every characteristic and imposes no completeness or closure hypothesis.

Cited nodes: none.

## Unfinished work and validation

Both new statements intentionally remain unsplit for separate future workers. Nothing else is left unfinished in this stage-1 repair. The server review_split check passed before report preparation. The required deliver.py --no-push run exited successfully: OK (not pushed), preflight passed, temporary commit d4c2d2ec12b. The two new statement-only nodes were included. The subsequent delivery command performs its own final preflight before pushing.


## Landing-return repair, 2026-10-22

The supplied return names head 41065a83f01 and says the independent reader approved it, but landing refused side completion that had not been promoted into the live queue DAG. I retained the delivered sandbox split, both new nodes, the full inherited proof, report and all search records. This section supersedes the earlier validation paragraph's temporary commit. I first ran the required dry run without changing the retained work: it exited successfully at efee0960f71 against the delivery tool's freshly fetched current origin/sheaf-dag. No separate git operation was run. The delivery tool builds a fresh commit on that base and preserves the maintainer-owned fields rather than copying stale completion or attachment metadata from the sandbox.

I compared original-node.json with the current read-only item: they are equal as JSON. Comparing the retained item to the current item shows only proof, proof_deps and split_report differences. Thus the old nine-step proof remains the current source material, and the retained five-step assembly is still the required mathematical change; the current item statement, statement dependencies, source, blueprint fields, Lean attachment and review records do not need replacement. Both extracted node ids are still absent from the current read-only DAG, so the delivery still adds two nodes rather than overwriting another worker's node.

I reread all current cited statements, including the new-node statement dependencies, instead of relying on the old approval. def-weil-pbc-free-module explicitly gives unique finite basis expansions; I replaced the short free-module quotation in citations.json by this stronger verbatim clause that step 1 actually uses. def-kun-subspace-topology explicitly makes the inclusion continuous. The currently split lem-sfb-ordered-join-partial-contraction still provides the explicit S formula, its identity only through degree r-2, naturality for maps sending chosen anchors to the chosen anchors, and uniform coefficients independent of vertex equalities. These are exactly the inputs to the comparison statement at r=n+1; its recursion never uses the unsupported top-degree contraction. The two retained new statements supply exactly the augmented chain map and the equivariant finite-formula homotopy used by assembly steps 2–5. Their statements and logged search questions did not change, so the seven recorded searches per new node were reused after reading their results. There is no new Mathlib-leaf claim.

I also reread the main-20261015 paragraph (3), the current chapter/unit route, and the current Sheaf theorem. The latter is still sorry, and the source-library keyword/tag search found no completed attachment. The arithmetic expansion is still explicitly agent-written and WANTED remains recorded; no SGA route is introduced. I reran check_small_cases.py successfully on all 325 tuple cases, and checked all six citation entries as literal substrings of the current or supplied statements. The total assembly remains 2063 characters, both extracted files remain statement-only, and every argument in the nine old steps remains in the inherited report. No mathematical correction was required by the current cited statements. The item split_report now explicitly records this landing-return repair, so this is not an unchanged re-push. The live-DAG promotion mentioned in the return is reserved to L; this delivery supplies the rebased split for that review and promotion.

Validation for the changed repair files is the subsequent required deliver.py --no-push run, followed only after its successful exit by deliver.py. Both run the server preflight. No Lean source was written and no compiler, Lake or library build was invoked.
