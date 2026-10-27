# Q94 stage-1 repair report

1. Files written:
   - `dag/nodes/sec-six-functors-basics/lem-sfb-normed-scalar-profinite-cech-exact.json`: unchanged statement; four assembly steps, 2733 text characters.
   - `dag/nodes/sec-six-functors-basics/lem-sfb-finite-coefficient-cech-primitive-lift.json`: statement, unsplit, no Mathlib match. Finite-coefficient primitives with prescribed quotient reduction; includes the zero-quotient base case.
   - `dag/nodes/sec-six-functors-basics/lem-sfb-inverse-limit-cech-primitive.json`: statement, unsplit, no Mathlib match. Sequential inverse-limit primitive extending a prescribed first reduction.
   - `citations.json`: one literal statement excerpt for each parent step/cited-node pair.
2. Attachments: none. The live `Sheaf/Topology/NormedScalarProfiniteCechExact.lean` theorem `Profinite.normedScalarProfiniteCech_exact` ends in `sorry`; its eight-step docstring confirms the returned proof. The searched WeilConjectures source supplied no closed declaration for the item or the extracted statements.
3. WANTED: none newly required. This repair uses the obtained Bhatt–Scholze paper and already available arithmetic/tower nodes; it does not purport to obtain Serre's Local Fields, previously wanted by the arithmetic nodes.
4. What was wrong: the returned parent concentrated the finite contraction, finite-kernel correction and continuous inverse-limit reconstruction into one 5386-character proof. The sole return point asks for work to be spread across at least two new statement-only nodes, with parent proof at most 3000 characters. This repair changes the split, not the statement. No mathematical or blueprint statement dispute was found.
5. Unfinished: exactly the proofs of the two new unsplit nodes, intentionally queued for other stage-1 workers. Both have empty proof and proof_deps and null proof_origin. No Lean was written, compiled or run. All writes are inside the Q94 sandbox.

## Repair of the return

The sandbox initially contained only dispatcher marker files, no delivered JSON, report or search log. I copied the current read-only node, whose eight steps and lengths match the returned version, and retained every old step verbatim below and in `original-proof.json`. There was no earlier sandbox work to overwrite or earlier search result to rerun. The existing finite-cocycle-descent node is reused and not delivered again.

The parent retains original steps 1 and 3 verbatim and step 8 with only its reference to the integral result updated. Original step 2 and the full kernel-correction argument of original steps 5–6 become the finite-coefficient primitive-lifting node's work. Original step 4, the induction conclusion of step 6 and the full reconstruction argument of step 7 become the inverse-limit primitive node's work. Its prescribed first reduction makes initialization an explicit use of the first new node in parent step 3. These are two distinct arguments of similar scale: finite quotient descent/contraction plus one kernel correction, and recursive compatible choice plus continuous inverse-limit reconstruction. Neither states the field-coefficient result; neither deals with local-field arithmetic or the denominator argument. The new statements contain no proof sketch, and the full arguments are retained here for their future workers.

For the first new node: establish finite-M exactness using the existing cocycle-descent lemma exactly as old step 2 does. For p:B→A and prescribed u, choose any set section s of p, put t=s∘u and r=d t−c. Additivity of p gives p r=0, and d²=0 gives d r=0. Regard r as a continuous cochain into the finite discrete kernel K. Solve d w=r by the finite-M assertion and put v=t−ιw. Then p v=u and d v=c. No additivity of s, no continuous section of q, and no negative degree is used. This preserves both full equations of old steps 5–6 with B=A_(m+1), A=A_m.

For the second new node: reduce f to f_m=ρ_m f. Starting at the specified u_1, use the first new lemma recursively to get u_(m+1) with p_m u_(m+1)=u_m and d u_(m+1)=f_(m+1). The recursive invariant is precisely those two equations, with base d u_1=f_1. At x, the family (u_m(x)) belongs to L. Its map into the product is continuous coordinatewise, and corestriction to the compatibility subspace is continuous. This gives u. Applying ρ_m to d u yields d u_m=f_m for every m; coordinatewise equality in the product proves d u=f, and ρ_1 u=u_1. This is the full old reconstruction argument with a general finite abelian tower replacing the local-field quotients. The parent transports along the separately cited topological ring isomorphism O≅L.

## Not duplicates

lem-sfb-finite-coefficient-cech-primitive-lift vs lem-sfb-finite-valued-cech-cocycle-descent: the existing node produces a finite quotient surjection and a descended cocycle, with its equation; it asserts neither a primitive nor a primitive lifting a prescribed cochain across B→A. It supplies the contraction argument's input, rather than the new conclusion.

lem-sfb-finite-coefficient-cech-primitive-lift vs lem-sfb-normed-scalar-profinite-cech-exact: finite discrete abelian groups, an arbitrary coefficient epimorphism, and a prescribed reduction; the parent has complete local-field coefficients and no coefficient lifting condition. The new node alone does not give integral-limit reconstruction or localization.

lem-sfb-inverse-limit-cech-primitive vs lem-sfb-integers-profinite-tower: the existing node is the topological ring presentation of O_E and its finite-factorization property. It asserts no equation for cochains or primitives; the new node concerns arbitrary finite abelian towers and a prescribed initial primitive.

lem-sfb-inverse-limit-cech-primitive vs lem-sfb-finite-coefficient-cech-primitive-lift: one finite coefficient transition versus an entire inverse limit with its product/subspace topology and actual continuous primitive. The latter requires recursive compatible choices and continuous reconstruction, not merely one application of the former.

lem-sfb-inverse-limit-cech-primitive vs lem-sfb-normed-scalar-profinite-cech-exact: the new node has an explicit surjective finite abelian tower, inverse-limit topology and prescribed first reduction. It supplies neither the local-field integral presentation nor a bound on a field-valued cocycle, both still needed by the parent.

Whole-DAG statement searches for Cech with profinite/finite discrete/inverse limit found the existing descent lemma, the item, field/separable-coordinate and site-comparison nodes. None states these prescribed-reduction results. Whole-blueprint searches for Cech, primitive and inverse limit likewise found no equivalent. `blueprint_refs.py ancestor` returns None: the inherited detached null ancestor is retained, with the precise finite-E paragraph (3) place and an extended via chain. No unit or chapter record changes. Searching 4.3.9 finds the item/descent lemma and unrelated enriched-category nodes whose sources use the same number in a different document, all distinguished above or by subject.

## Review by Q94

I read the item's statement and all eight old proof steps, the source's Bhatt–Scholze Lemma 4.3.9(2)–(4) and proof on printed page 33, the main-20261015 direct-images proof paragraph (3), the unit and chapter records, and the full statement of each node cited in the parent. Bhatt–Scholze's text gives discrete coefficients, sequential closed colimits and sequential limits along profinitely split maps; it does not literally state these pointwise Cech assertions. The source fields of the new nodes explicitly say that they are agent-formulated expansions. The two paragraphs of argument above are what is extracted, not claims of verbatim theorems in that paper. I also read the existing finite-descent statement, including its essential guarantee of the cocycle equation on the entire finite fibre power and its explicit lack of surjectivity for the induced tuple maps. The contraction uses that guarantee, never the missing surjectivity.

Parent step 1 uses the actual statement of lem-sfb-finite-quotient-fiber-product: its P is compact Hausdorff totally disconnected. Iterating on P_(r+1)=P_r×_S T applies under the given continuous maps to the Hausdorff base. Coordinate identification and deletions are explicit maps. The two deletion orders cancel with signs (-1)^(i+j-1) and (-1)^(i+j); no vanishing theorem is hidden there. The empty case gives zero function groups.

Parent step 2 uses the coefficient definition only to fix O, its norm and the chosen uniformizer. I checked that the DVR statement supplies a nonzero uniformizer, finite residue field and 0<|π|<1; the finite-quotient node supplies finiteness and surjective additive/ring transitions, and integers-profinite-tower clause (1) supplies exactly a ring isomorphism AND homeomorphism for the discrete quotient topology. Thus the finiteness, topology and surjectivity hypotheses of BOTH new nodes are satisfied. These three generic arithmetic/topological inputs retain the accepted tool-use declarations; no unit route is replaced.

Parent step 3 first applies the finite-lifting node with A=0 and B=A_1. The zero cochain satisfies its required equation and the homomorphism to the zero group is surjective. Its actual conclusion is p∘v=u AND d v=c, so the primitive u_1 is obtained, not borrowed from the proof. The second node explicitly gives a continuous L-valued primitive for the same positive degree and same q, with the first reduction prescribed; every transition is surjective by step 2. The actual ring/homeomorphism statement of integers-profinite-tower allows composition with ι and its inverse; additivity commutes with the displayed finite sums. Inverse-limit reconstruction is inside the second node's task, not hidden in this assembly step.

Parent step 4 retains the old argument: the increasing open sets U_k cover because 0<|π|<1, the compact domain supplied by the cited fibre-product statement has a finite subcover, and the largest k gives |π^k f|<1 everywhere. Multiplication and corestriction to O's subspace topology are continuous. Step 3 provides an integral primitive; multiplication by π^(-k) is continuous, and the displayed scalar cancellation proves exactly d g=f. No local constancy of integral or field-valued maps is introduced.

For B1–B10, each new statement introduces q, both spaces, the positive degree, tuple domains, coefficients, topology, differential and prescribed primitive. Tuple/size notions cite their actual definition nodes and everything else is defined inline. Both nodes are statement-only, not Mathlib leaves or alleged closed Lean attachments; neither has a proof dependency or proof sketch. I checked both new names against the DAG before writing and searched the entire blueprint, not just this chapter. Mathlib searches were run only by the required msearch command; searches.jsonl is the actual log, and mathlib_searches copies its query/result records. Each new node has LeanSearch, two LeanFinder phrasings, Loogle and grep. I read candidate source at Profinite/CofilteredLimit.lean:124, Nobeling/Successor.lean:240, HomComplexSingle.lean:251, MappingCone.lean:485, and ProfiniteGrp/Limits.lean:120–147. Factorization of locally constant functions, Nobeling's special exact sequence, abstract Hom cocycles and the presentation of a profinite group do not assert finite coefficient Cech exactness or primitive lifting. No candidate is a one-line specialization. A first inverse-limit grep used the overly narrow Profinite path; the subsequent ProfiniteGrp grep located and checked the actual presentation lemmas, so the absence verdict does not rest on that empty grep.

For C1–C8, I checked every uses entry against the statement file and generated literal quotations in citations.json. The item cites only facts actually asserted, not data from an existing proof or a definition as a theorem. proof_deps is exactly the union of uses. Both new nodes share the parent's unit; the three retained off-unit tool uses have their existing reasons preserved. There is no edge back from either new node to the parent: their only statement dependencies are size and profinite tuple definitions.

For D1–D5, the repair does not merely shorten the parent: it adds two new independently statable problems and assigns every moved argument to them explicitly above. The finite-lifting node requires finite quotient descent and kernel correction; the limit node requires the recursive invariant and topological reconstruction. Neither is a relabelling of the field-valued assertion. No argument has disappeared: the complete old text is retained below. No new parent step exceeds 2000 characters; the total is 2733.

For E1–E7, I tested n=1 (degree-zero primitives, no negative degree), q=id, a singleton base, both spaces empty, B=A=0, p=id, p:B→0, a constant identity-transition tower, and towers containing zero groups. With q=id, d_0=0 and d_1=id, so a degree-one cocycle is zero, as required. For p=id the hypotheses already force v=u and d v=c. For p:B→0 the result is ordinary finite-coefficient exactness. In the limit node with a constant identity tower, the prescribed primitive already solves the lifted cocycle; the reconstructed primitive is that same cochain. Empty spaces require no chosen points or section of q. For non-split coefficient extensions, only a set section is used in the future proof; its failure to be additive is precisely the finite-kernel obstruction corrected by the cocycle primitive. Completeness is supplied solely by O≅lim A_m, not imposed on an algebraic closure. These checks found no statement dispute and no changed hypothesis.

The correction made in this repair is the requested redistribution of work and an explicit prescribed-reduction interface between the two new tasks. The original scalar statement, Lean metadata, imported fields and accepted tool_uses are preserved. I started no agents and ran no compiler or local DAG/review/preflight command. Final validation is performed by deliver.py on the server.

## Original argument preserved in full

### Original step 1

Put $P_r=T_S^r$. Repeatedly apply [lem-sfb-finite-quotient-fiber-product] to $P_{r+1}=P_r\times_S T$, starting with $P_1=T$. It gives the compact Hausdorff totally disconnected topology on every $P_r$; the tuple identification and its inverse are the coordinate maps. Deleting a coordinate is continuous. Thus every displayed differential is continuous. In $d_{k+1}d_k$, deleting positions $i<j$ in the two possible orders gives the same function with opposite signs $(-1)^{i+j-1}$ and $(-1)^{i+j}$, so $d_{k+1}d_k=0$. If $T=S=\varnothing$, every cochain group is zero and $g=0$ proves the claim. We may henceforth work with nonempty $S$ (surjectivity makes $T$ nonempty).

Cited nodes: lem-sfb-finite-quotient-fiber-product

### Original step 2

First let $M$ be any finite discrete abelian group and let $c\in C(P_{n+1},M)$ be a cocycle, with $n\geq1$. Apply [lem-sfb-finite-valued-cech-cocycle-descent] to obtain $q_0:T_0\twoheadrightarrow S_0$, $a,b$ and $c_0$ with $d_nc_0=0$. Choose a set section $\sigma:S_0\to T_0$; it is continuous since both sets are finite discrete. Put
$$v_0(x_0,\ldots,x_{n-1})=c_0(\sigma(q_0(x_0)),x_0,\ldots,x_{n-1}).$$
For an equal-image tuple $(x_0,\ldots,x_n)$, the equation $d_nc_0=0$ on $(\sigma(q_0(x_0)),x_0,\ldots,x_n)$ reads
$$c_0(x_0,\ldots,x_n)=\sum_{j=0}^n(-1)^j c_0(\sigma(q_0(x_0)),x_0,\ldots,\widehat{x_j},\ldots,x_n).$$
All base images are equal, so the sum is $d_{n-1}v_0$. Precompose $v_0$ with $a$ in every coordinate. The resulting continuous $v:P_n\to M$ satisfies $d_{n-1}v=c$, since coordinate deletion commutes with $a$. This proves the finite-coefficient assertion used below, including $n=1$.

Cited nodes: lem-sfb-finite-valued-cech-cocycle-descent

### Original step 3

Use the coefficient datum [def-weil-l-adic-coefficient-extension], and put $O=\mathcal O_E$. By [lem-weil-l-adic-extension-integers-dvr] choose a nonzero uniformizer $\pi$ with $0<|\pi|_E<1$ and $\pi O=\mathfrak m_E$; $O$ is a DVR with finite residue field. By [lem-weil-valued-dvr-finite-quotients], $A_m=O/\pi^mO$ is finite for every $m\geq1$ and $p_m:A_{m+1}\to A_m$ is surjective. By [lem-sfb-integers-profinite-tower], the reduction map
$$O\xrightarrow{\sim}\varprojlim_{m\geq1}A_m$$
is a topological ring isomorphism for the discrete quotient topologies. In particular each reduction $O\to A_m$ is continuous and the reductions jointly distinguish elements of $O$.

Cited nodes: def-weil-l-adic-coefficient-extension, lem-weil-l-adic-extension-integers-dvr, lem-weil-valued-dvr-finite-quotients, lem-sfb-integers-profinite-tower

### Original step 4

Temporarily suppose $f:P_{n+1}\to O$ is a continuous cocycle. Write $f_m$ for its reduction in $A_m$; then $d_nf_m=0$ because reduction is additive. Step 2 with $M=(A_1,+)$ gives a continuous $g_1:P_n\to A_1$ with $d_{n-1}g_1=f_1$. We construct by induction continuous $g_m:P_n\to A_m$ with
$$d_{n-1}g_m=f_m,\qquad p_mg_{m+1}=g_m.$$
The first equation at $m=1$ is the base case just obtained. The next two steps give the induction step for every $m\geq1$.

Cited nodes: 

### Original step 5

Assume $g_m$ is constructed. Choose a set section $s_m:A_m\to A_{m+1}$ of the surjection $p_m$ from [lem-weil-valued-dvr-finite-quotients]; it is continuous between finite discrete spaces. Thus $\widetilde g=s_m\circ g_m$ is a continuous lift; no additivity of $s_m$ is assumed. Set
$$r=d_{n-1}\widetilde g-f_{m+1}.$$
The additive map $p_m$ sends $r$ to $d_{n-1}g_m-f_m=0$. Hence $r$ is a continuous cochain with values in the finite discrete abelian group $K_m=\ker(p_m)$: it is continuous as a map to the subset $K_m\subseteq A_{m+1}$. Further,
$$d_nr=d_nd_{n-1}\widetilde g-d_nf_{m+1}=0$$
by step 1 and the cocycle equation for $f$. The same equation holds in $K_m$ because its inclusion is injective.

Cited nodes: lem-weil-valued-dvr-finite-quotients

### Original step 6

Apply the finite-coefficient result of step 2 to $M=K_m$ and this degree-$n$ cocycle $r$. It gives continuous $v:P_n\to K_m$ with $d_{n-1}v=r$. Let $\iota_m:K_m\hookrightarrow A_{m+1}$ be the inclusion and define
$$g_{m+1}=\widetilde g-\iota_m v.$$
Then $p_mg_{m+1}=g_m$, since $p_m\iota_m=0$, and
$$d_{n-1}g_{m+1}=d_{n-1}\widetilde g-\iota_mr=f_{m+1}.$$
This completes the stated induction. It works in degree $n=1$: it solves a $K_m$-valued degree-one cocycle by a degree-zero cochain, and uses no negative degree or degree-zero vanishing claim.

Cited nodes: 

### Original step 7

For each $x\in P_n$, the compatible tuple $(g_m(x))_{m\geq1}$ lies in $\varprojlim_mA_m$. The map to the product is continuous because each coordinate $g_m$ is continuous; corestricting to the compatibility subspace preserves continuity. Compose with the inverse homeomorphism in [lem-sfb-integers-profinite-tower] to obtain a continuous $g_O:P_n\to O$. For every $m$, the reduction of $d_{n-1}g_O$ is $d_{n-1}g_m=f_m$, since the reduction maps preserve finite signed sums. The ring-isomorphism part of that node makes the reductions jointly injective, so $d_{n-1}g_O=f$ as actual $O$-valued functions. This proves the integral assertion without any exchange of cohomology and inverse limits.

Cited nodes: lem-sfb-integers-profinite-tower

### Original step 8

Return to the given $E$-valued cocycle $f$. The open sets
$$U_k=\{x\in P_{n+1}:|f(x)|_E<|\pi|_E^{-k}\}\qquad(k\geq0)$$
cover $P_{n+1}$ because $0<|\pi|_E<1$. Compactness of $P_{n+1}$ from [lem-sfb-finite-quotient-fiber-product] gives a finite subcover. The $U_k$ are increasing; take its largest index $k$. Then $|\pi^kf(x)|_E<1$ for every $x$, so $h=\pi^kf$ is a continuous $O$-valued cocycle, with $O$ carrying its subspace topology. The integral result of steps 4–7 gives continuous $u:P_n\to O$ with $d_{n-1}u=h$. Set $g=\pi^{-k}u:P_n\to E$. Multiplication by this fixed field element is continuous, and linearity of the finite signed sum gives
$$d_{n-1}g=\pi^{-k}d_{n-1}u=\pi^{-k}\pi^kf=f.$$
No local constancy is imposed on $f,u$ or $g$.

Cited nodes: lem-sfb-finite-quotient-fiber-product


## Validation repairs

The first retained dry-run diagnostic rejected two literal citation excerpts solely because they were shorter than 40 characters. I replaced them with the full valuation-ring definition and the entire finite-lifting conclusion sentence and formula, respectively; no mathematical statement or proof step changed.


## Current-DAG landing repair (2026-10-22)

The new return is a landing-state refusal, not a rejection of the two-lemma split: “completed in this project's DAG but not in the live DAG the queue reads (side completion never promoted; L promotes it)”. I continued the retained returned sandbox, including the two new statements, complete original argument, citations, and all 13 search-log entries. I ran its required dry run first; it exited successfully at fa1820a8674. No push was active or repeated. The delivery tool fetches origin/sheaf-dag and constructs the payload on its current tip; no worker git command or repository write was used. Promotion and the independent landing review remain L's duties, as the return says.

The current read-only item still has the eight-step proof, whereas this payload supplies four assembly steps and the two unsplit lemmas required by the released stage-1 repair note. Its statement, stmt_deps, source, blueprint provenance, Lean record, reviewed Lean record, and existing tool_uses agree with the retained version. The two new ids are absent from the current DAG. The only item fields differing from the current DAG are proof, proof_deps and split_report. rebase-audit.json records the statements reread and their hashes; it is sandbox evidence, not an extra delivered DAG file.

I reread the complete current statements of every cited node and the two definition dependencies of the new nodes. The current finite-quotient node is a Mathlib leaf; its clauses 2 and 3 still provide finite groups and surjective transitions. The DVR node is now itself split through core and factorization nodes, but its statement still supplies exactly the uniformizer and residue-field data the parent uses. The fibre-product node still asserts compact Hausdorff totally disconnectedness, and integers-profinite-tower clause 1 still asserts both the ring isomorphism and homeomorphism. Thus none of those changes in proof or completion status changes the assembly's hypotheses or conclusion. I also reread the current finite-valued cocycle-descent statement used by the preserved future argument: it still guarantees the cocycle equation on every finite equal-image tuple, without claiming that the tuple map is surjective. No application depends on a cited proof's internal construction.

I reread Bhatt–Scholze Lemma 4.3.9(2)–(4) and its proof on printed page 33, the current blueprint direct-images proof paragraph (3), the chapter and unit records, and the released keep_plan repair note. The source still motivates the finite, limit and localization route; it does not state the auxiliary pointwise lemmas verbatim. The two new statements therefore keep their explicit agent-formulated source qualification. Their statements have not changed, so I reused the recorded Mathlib searches after reading the hits rather than inventing or repeating queries.

The concrete edits in this retry make the assembly's reduced-cocycle compatibility explicit in step 3, remove inherited doubled TeX escapes from the four current proof steps (B4), and expand the two arithmetic citation excerpts to include the actual uniformizer and surjectivity clauses. Each excerpt is copied literally from the current statement. The original eight-step text and its searches remain preserved above. The correction does not add a hypothesis, assume a continuous section, replace continuous cochains by locally constant ones, or alter the target statement.

### Review by Q94 of the landing repair

For step 1 I checked that the fibre-product compactness statement applies successively to P_r and T over S, and verified the opposite deletion signs. For step 2 I checked all local-field hypotheses of the quotient and tower nodes and included the full transition clause in citations.json. For step 3 the first new node is applied to A=0 and B=A_1; surjectivity to zero and its prescribed zero primitive satisfy its hypotheses. The second node uses the same q, positive degree, finite groups and surjective transitions; the newly displayed compatibility equation verifies the reductions of f_L. Composing with the inverse topological ring isomorphism preserves the finite signed differential. For step 4 compactness provides a single largest denominator exponent, and the displayed scalar cancellation yields precisely the original field-valued cocycle. Neither new lemma states the entire parent assertion; the parent still performs arithmetic specialization and localization.

I rechecked the empty surjection, n=1, zero coefficient groups, p=id, p:B→0 and identity-transition towers against both statements. All are included and satisfy the prescribed-reduction equations. The proof still has no long hidden step; the total proof text is below 3000 characters. The uses union equals proof_deps and all nine step/citation pairs have literal current statement excerpts. Existing approved tool_uses are preserved, not enlarged. The report and proof changes above discharge this retry's rebase/reread/adjust instructions while retaining all prior work. The next dry run and push use the mandated unmodified delivery tool, with only one invocation active at a time.
