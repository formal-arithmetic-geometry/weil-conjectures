## Worker report

Files written for this stage-1 repair:

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-graded-module-section-tail.json`: same statement and statement dependencies; four assembly steps, 1428 characters in total.
- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-graded-proj-section-comparison.json`: new statement-only, unsplit. Coherence and the canonical graded section map's local isomorphisms. Mathlib: no match after two semantic phrasings, LeanSearch, valid Loogle and source searches.
- `dag/nodes/sec-six-functors-basics/lem-sfb-graded-local-isomorphism-tail.json`: new statement-only, unsplit. The abstract graded-map criterion, including truncated finite kernel/cokernel and an explicit degree bound. Mathlib: no match after two semantic phrasings, LeanSearch, valid Loogle and source searches.
- `citations.json`: literal statement witnesses for every cited node in each assembly step.
- `report.md`: this report and signed review. The old report, original nine-step proof and raw search log remain in `prior-report.md`, `original-proof.json` and `searches.jsonl` in the sandbox. Those are retained evidence, not replacements for the submitted report.

Attachments: none. `AlgebraicGeometry.Proj.finite_graded_module_section_tail` is at `lean/Sheaf/AlgebraicGeometry/FiniteGradedModuleSectionTail.lean:86`, but ends with `sorry`. It is not a finished proof and is not under the required `WeilConjectures/` attachment root. The searches by node tag and section-tail terminology in `lean/WeilConjectures/` found no exact finished declaration. No new Lean file is written, no existing declaration is rebound, and no compiler, Lake or build tool is run.

WANTED: none. The sources are already present.

What was wrong: the returned O2 version did no stage-1 work and instead replaced N9's owned Lean binding by an existing-declaration record. That change is withdrawn. The item was copied from current live with N9's complete `lean` and `reviewed_lean` records unchanged, including `by: N9`, `branch: sheaf-dag`, `existing: false` and the module file. The previous report's proposed rebind is obsolete and is explicitly superseded here. Its unrelated paragraph about OpenImmersionLocalizing was stale material, not a constraint or a mathematical finding about this item.

The current released repair note `coord/repair-notes/lem-sfb-finite-graded-module-section-tail.json` explicitly requests at least two comparable new statement-only nodes, a proof of at most 3000 characters, and preservation of all the original arguments. This is why the reviewed Q10 split is now refined. It is not a repeat of the superseded attachment delivery. The statements, sources, old proofs, accepted ownership and inherited blueprint fields were compared with live. The mathematical statement is unchanged, and there is no statement dispute. All requested stage-1 work is present; nothing mathematical is left unfinished beyond the intentionally unsplit new nodes.

## Review by O2

I read the complete return and checked each named problem. A7 is addressed by following the later, released human re-split request: the delivery now changes the proof and adds two genuine prerequisites. A2 is addressed by this exact review section. H1/H2 are addressed by delivering only stage-1 DAG work and its report; comparison against live confirms that every Lean ownership and binding field is byte-for-byte equivalent as JSON. In particular, the reviewed file is still owned by N9. The first mandatory dry run, before any repair, failed for the missing review heading; that process exited before subsequent validation was started.

Sources read for the item and both new nodes: `literature/stacks-project/coherent.tex`, Tag 0AG7, `lemma-recover-tail-graded-module`, lines 3862--3929, including the whole kernel/cokernel proof. For the geometric comparison I also read `constructions.tex`, Tag 01MT, `lemma-apply-modules`, the integer twist/shift isomorphism and section maps; `properties.tex`, Tag 0AG5, `lemma-proj-quasi-coherent`, and `constructions.tex`, Tag 0B5I, `lemma-comparison-proj-quasi-coherent`, with its displayed inverse chart formula. For the section-finiteness assembly step I read `coherent.tex`, Tag 0AG6, `lemma-coherent-on-proj`, opening assertion and (4). The permitted route remains precisely 0AG7, not a different theorem or a source from SGA.

I opened the statements of every node cited in the new proof. Step 1 uses the new finite-graded-proj-section-comparison statement: it explicitly supplies Noetherian S, coherent F, the very same graded N and canonical phi, and isomorphism of every degree-zero localization at f_i. Its hypotheses are the item's hypotheses with the finite degree-one generating family chosen. The inverse is explicitly the reconstruction map on t/f_i^a, so this is not an arbitrary local isomorphism. Step 2 uses standard-proj-coherent-section-finiteness: its statement explicitly asserts finiteness of the nonnegative section module, with exactly the multiplication action defined in step 1. It needs S_0 Noetherian and finite degree-one generation, which the item assumes, and coherence of F, supplied by step 1. Step 3 uses the new graded-local-isomorphism-tail statement: S is Noetherian by step 1, M is finite by the item, N+ is finite by step 2, and the localized phi maps are those supplied by step 1. Its conclusion says that every phi_n for one common nonnegative bound is an S_0-linear isomorphism. Step 4 uses standard-proj-twist-tensor: its statement gives the actual canonical multiplication isomorphism alpha_(M,n), not merely an unrelated isomorphism. The degree-one opens cover because the f_i generate the irrelevant ideal. By the definition of phi, composing with Gamma(alpha) is the canonical x/1 section map on every standard chart. This last composition is elementary; the three preceding steps apply substantive cited statements and are not marked elementary. The literal quotations are in citations.json.

For C1 and C4, I also read the existing statements underlying the transferred geometric argument: finite-type-algebra-noetherian says that a finite type algebra over a Noetherian base is Noetherian; proj-graded-module-sheaf-exists supplies quasi-coherence, standard chart sections and the canonical section maps; quasi-coherent-finite-type-affine(c) supplies the finite-type inference from a chart cover; coherent-ft-locnoeth supplies coherence once X is locally Noetherian; proj-section-module-reconstruction supplies the inverse t/f^a formula, not just an existence isomorphism; proj-tilde-functorial supplies the chart formula for the map induced by phi. I read graded-localization-exact (both ordinary and degree-zero exactness), module-localization-away (the iff for a zero fraction), and noetherian-submodule-finitely-presented (finite submodules of finite modules) for the algebraic transfer. These arguments are now work assigned by the two new statements, rather than hidden facts in the short assembly. They are retained in full below for the workers who split those nodes. Neither new node carries proof steps, proof dependencies, or a proof sketch in its statement.

B1--B10: both new nodes introduce their ring, modules, gradings, maps and all hypotheses; gradings, truncations and homogeneous fractions are explicitly specified, and every other mathematical notion has its defining node. Their source is the actual 0AG7 label, with the extra geometric source tags identified precisely. Their inherited blueprint ancestor is null (as `blueprint_refs.py ancestor` reported); their `via` chains prepend this item to its preserved chain, and `from.place` locates respectively the original first and second halves. Whole-blueprint searches for `graded module`, `0AG7`, `section module`, `graded`, `local isomorphism` and `coherent associated`, together with whole-DAG tag/keyword searches, found no equivalent statement. The apparent graded matches in unrelated filtered-complex nodes are not graded-ring module theorems. The item is not a unit's key statement, so no unit realization record is changed.

D1--D5: the geometric node does not assert any eventual global-section isomorphism; it asserts coherence and a unit/counit calculation only after localization. The algebraic node has no scheme, sheaf or cohomology, and assumes a map with local isomorphisms and a finite target truncation. Its kernel/cokernel and degree-bound argument are independent of the geometric comparison. Each represents four of the old steps (2841 versus 2552 characters), so neither is the whole item under another name. The existing 0AG6 section-finiteness node is reused instead of duplicated. The two new statements depend only on definitions and existing interfaces, not on the item or one another; no circular use of the item is introduced. No new assembly step exceeds 2000 characters.

E1--E7: I checked zero S and M, empty generating families, empty Proj and nilpotent f_i. If r=0, all positive-degree ring pieces vanish; a finite graded module has finitely many generator degrees, and both truncation bounds give eventual zero. In the algebraic node no local-isomorphism hypothesis is then needed; finite N+ also has a finite range of generator degrees. For S=k[t], M=S/(t), the associated sheaf is zero while M_0 need not be zero: only eventual bijectivity is asserted. Negative homogeneous generator degrees are allowed in the geometric node and are interpreted using inverse powers in the localization; in K and Q all homogeneous generators have nonnegative degree by truncation. The zero localized fraction t_j/f_i^{e_j} gives t_j/1=0 even on an empty chart, then some positive b_ij kills t_j. The bound uses integer e_j and finite sums b_ij, and the strict inequality n>B_T makes the pigeonhole argument valid. The algebraic node assumes no finiteness of N in negative degrees and uses none. The source's final x_i/d_i index slip is not copied: generators are consistently t_j/e_j. There is no changed source statement or coefficient convention.

The Mathlib searches are the actual msearch calls recorded in searches.jsonl and copied exactly into mathlib_searches. Both original Loogle patterns had unknown identifiers; I recorded that fact rather than treating them as evidence of absence, and ran valid replacement patterns. Geometric searches return structure-sheaf/chart maps, not arbitrary associated module coherence or the section-unit map. Algebraic searches return ordinary localization comparison, homogeneous ring fractions, a trace identity, finite-type graded rings, and a Hilbert-polynomial TODO. I read Away.eventually_smul_mem (HomogeneousLocalization.lean:629), the monomial spanning and finiteType statements there, GradedAlgebra/FiniteType.lean, and the HilbertPoly.lean TODO. These are tools or different statements, not a one-line specialization giving either new lemma. There are no new Mathlib leaves.

## Transferred arguments retained in full

This is the original live proof text, with its old step numbers. Steps 1--4 belong to the new finite-graded-proj-section-comparison work item; steps 5--8 belong to the abstract graded-local-isomorphism-tail work item, with its arbitrary map psi replacing phi. Step 5's invocation of section finiteness is an explicit hypothesis of that algebraic node, discharged by assembly step 2. Step 9 remains the final assembly. Thus no old argument was erased to shorten the item.

### Original step 1

Choose degree-one algebra generators $f_1,\ldots,f_r$. Since $S_+=(f_1,\ldots,f_r)$, a relevant homogeneous prime omits some $f_i$, so the affine opens $U_i=D_+(f_i)$ cover $X$ by [def-pc-proj]. The ring $S$ is Noetherian by [lem-weil-pbc-finite-type-algebra-noetherian], applied to the finite type $S_0$-algebra $S$. Also $X$ is Noetherian by the opening assertion of [lem-sfb-standard-proj-coherent-section-finiteness]. Choose finite homogeneous generators $x_j\in M_{d_j}$: replace any finite generating set by its finitely many homogeneous components; their span contains the original generators and is contained in $M$. Empty generating families are allowed.

Cited statements: def-pc-proj, lem-weil-pbc-finite-type-algebra-noetherian, lem-sfb-standard-proj-coherent-section-finiteness

### Original step 2

Put $\mathcal F=\widetilde M$. It is quasi-coherent by [lem-weil-pbc-proj-graded-module-sheaf-exists](c). On $U_i$ its module of sections is $M_{(f_i)}$, generated over $S_{(f_i)}$ by $f_i^{-d_j}x_j$: in a homogeneous expression $y=\sum_j a_jx_j$ with $y\in M_a$, take $a_j\in S_{a-d_j}$, and write $y/f_i^a=\sum_j(a_j/f_i^{a-d_j})(x_j/f_i^{d_j})$. Negative powers denote multiplication by positive powers in the localization, so this also applies to $d_j<0$. The chart identifications and [lem-weil-pbc-quasi-coherent-finite-type-affine](c) imply that $\mathcal F$ is of finite type. Since $X$ is locally Noetherian, [pqf-lem-coherent-ft-locnoeth] implies that $\mathcal F$ is coherent.

Cited statements: lem-weil-pbc-proj-graded-module-sheaf-exists, lem-weil-pbc-quasi-coherent-finite-type-affine, pqf-lem-coherent-ft-locnoeth

### Original step 3

By [lem-sfb-standard-proj-twist-tensor], use the canonical isomorphisms $\alpha_{M,n}:\mathcal F\otimes\mathcal O_X(n)\xrightarrow{\sim}\widetilde{M(n)}$. Put $N_n=\Gamma(X,\mathcal F\otimes\mathcal O_X(n))$ and $N=\bigoplus_{n\in\mathbf Z}N_n$ with the homogeneous multiplication action in [lem-sfb-proj-section-module-reconstruction]. The canonical maps of [lem-weil-pbc-proj-graded-module-sheaf-exists](d), applied to $M(n)$ and composed with $\Gamma(\alpha_{M,n}^{-1})$, give $\phi_n:M_n\to N_n$. These assemble to a degree-preserving $S$-linear map $\phi:M\to N$: for $s\in S_e$ and $x\in M_n$, both $\phi_{n+e}(sx)$ and $s\phi_n(x)$ restrict to $sx/1$ in $(M_{f_i})_{n+e}$ on every $U_i$, so they agree by the sheaf axiom. The multiplication maps are associative and unital by the twist node, so this is precisely the canonical graded action.

Cited statements: lem-sfb-standard-proj-twist-tensor, lem-sfb-proj-section-module-reconstruction, lem-weil-pbc-proj-graded-module-sheaf-exists

### Original step 4

Apply [lem-sfb-proj-section-module-reconstruction] to the quasi-coherent sheaf $\mathcal F$: its chart formula gives isomorphisms $\varepsilon_i:N_{(f_i)}\to M_{(f_i)}$. By [lem-sc-p1-proj-tilde-functorial], the map on chart sections induced by $\phi$ is $\phi_{(f_i)}$, sending $x/f_i^a$ to $\phi_a(x)/f_i^a$ for $x\in M_a$. Its composite with $\varepsilon_i$ sends this fraction to $\phi_a(x)|_{U_i}\otimes f_i^{-a}=x/f_i^a$, by the fraction formula for the twist comparison. Thus $\varepsilon_i\phi_{(f_i)}=\mathrm{id}_{M_{(f_i)}}$. Since $\varepsilon_i$ is an isomorphism, $\phi_{(f_i)}=\varepsilon_i^{-1}$ is an isomorphism for every $i$.

Cited statements: lem-sfb-proj-section-module-reconstruction, lem-sc-p1-proj-tilde-functorial, lem-sfb-standard-proj-twist-tensor

### Original step 5

Let $M^+=\bigoplus_{n\ge0}M_n\subseteq M$ and $N^+=\bigoplus_{n\ge0}N_n\subseteq N$, both graded $S$-submodules because $S$ has no negative degrees. The first is finite by [lem-trf-noetherian-submodule-finitely-presented], using that $S$ is Noetherian and $M$ is finite. The second is finite by [lem-sfb-standard-proj-coherent-section-finiteness], applied to the coherent $\mathcal F$ of step 2. Restrict $\phi$ to $\phi^+:M^+\to N^+$, and put $K=\ker\phi^+$ and $Q=\operatorname{coker}\phi^+$. The kernel $K\subseteq M$ is finite by the same submodule theorem. The images of a finite generating family of $N^+$ generate $Q$, so $Q$ is finite too. Both are graded, vanish in negative degrees, and for $n\ge0$ have $K_n=\ker\phi_n$ and $Q_n=\operatorname{coker}\phi_n$, since all maps preserve degree.

Cited statements: lem-trf-noetherian-submodule-finitely-presented, lem-sfb-standard-proj-coherent-section-finiteness

### Original step 6

For $f_i$ of degree one, taking the nonnegative truncation does not change degree-zero localization: every fraction in $M_{(f_i)}$ is $x/f_i^a$ with $a\ge0$ and $x\in M_a$, hence already comes from $M^+$. The fraction equivalence relation is identical in the submodule $M^+$; if a power of $f_i$ kills an element there in $M$, it kills the same element in $M^+$. This proves $(M^+)_{(f_i)}=M_{(f_i)}$, and the same argument applies to $N$. Consequently $(\phi^+)_{(f_i)}$ is the isomorphism of step 4. Apply [lem-sc-graded-localization-exact] to $0\to K\to M^+\to N^+\to Q\to0$. It gives $K_{(f_i)}=0$ and $Q_{(f_i)}=0$ for every $i$.

Cited statements: lem-sc-graded-localization-exact, def-weil-pbc-module-localization-away

### Original step 7

Apply the following calculation to each of $T=K,Q$. Choose finite homogeneous generators $t_j\in T_{e_j}$, necessarily with $e_j\ge0$, by replacing finite generators by their homogeneous components as in step 1. Since $T_{(f_i)}=0$, the fraction $t_j/f_i^{e_j}$ is zero in $T_{f_i}$. Multiplying by $f_i^{e_j}$ gives $t_j/1=0$. By the fraction relation in [def-weil-pbc-module-localization-away], choose $b_{ij}\ge1$ with $f_i^{b_{ij}}t_j=0$. This treats nilpotent $f_i$ and empty charts as well, since the same fraction relation applies to the zero localized module.

Cited statements: def-weil-pbc-module-localization-away

### Original step 8

For this $T$ let $B_T=\max(\{0\}\cup\{e_j+\sum_i b_{ij}:j\})$. If $n>B_T$, every element of $T_n$ is a sum of terms $c f_1^{a_1}\cdots f_r^{a_r}t_j$ with $c\in S_0$ and $\sum_i a_i=n-e_j$: expand the coefficient of $t_j$ in the degree-one algebra generators, then take its homogeneous component of degree $n-e_j$. Since $n-e_j>\sum_i b_{ij}$, at least one $a_i\ge b_{ij}$, so each term is zero. If $r=0$, no monomial has positive degree, so there are no such terms. If $T=0$, take the empty generating family and $B_T=0$. Thus $T_n=0$ for all $n>B_T$.

Cited statements: 

### Original step 9

Take $n_0=1+\max(B_K,B_Q)\ge0$. For every integer $n\ge n_0$, steps 5 and 8 give $\ker\phi_n=0$ and $\operatorname{coker}\phi_n=0$, so $\phi_n$ is an $S_0$-linear isomorphism. Composing with $\Gamma(\alpha_{M,n})$ from step 3 identifies its target with $H^0(X,\widetilde{M(n)})$ and identifies the map with the one in the statement, since on each standard chart it is $x\mapsto x/1$. Thus the asserted isomorphism holds without a torsion-free hypothesis or a nonempty-Proj hypothesis.

Cited statements: lem-sfb-standard-proj-twist-tensor

## Not duplicates

lem-sfb-finite-graded-proj-section-comparison vs lem-sc-p1-coherent-proj-representation: the existing statement realizes a coherent sheaf on P1 over a field by some finite graded module; it does not give the unit map of an arbitrary supplied finite M or a general graded-map criterion.

lem-sfb-finite-graded-proj-section-comparison vs lem-weil-pbc-projective-space-twisting-sheaf-charts: the existing statement is O(1) on projective space over the integers and its chart bases; it has no arbitrary M or section-unit comparison.

lem-sfb-finite-graded-proj-section-comparison vs def-sfb-coordinate-quotient-grading: the existing statement constructs the grading on a quotient polynomial ring and says nothing about module-to-section maps or graded-map tails.

lem-sfb-finite-graded-proj-section-comparison vs lem-sfb-coherent-hyperplane-restriction-sequence: the existing statement is a hyperplane restriction exact sequence over a field, with neither local section-unit comparison nor a graded-map tail criterion.

lem-sfb-finite-graded-proj-section-comparison vs lem-sfb-finite-graded-module-section-tail: the item asserts the eventual canonical isomorphism to global sections; the geometric node only proves coherence and local comparison, and the algebraic node only applies to an abstract graded map already known to be locally invertible with finite N+.

lem-sfb-finite-graded-proj-section-comparison vs lem-sfb-flat-graded-tail-proj: the existing statement concerns flat relative Proj and Hilbert polynomials of coordinate algebras, not arbitrary graded module maps.

lem-sfb-finite-graded-proj-section-comparison vs lem-sfb-flat-projective-hilbert-polynomial-locality: the existing statement proves local constancy of fibre Hilbert polynomials for flat projective families, not either new assertion.

lem-sfb-finite-graded-proj-section-comparison vs lem-sfb-graded-proj-quotient-twist-comparison: the existing statement compares twists along a quotient of graded rings, rather than the section-unit map of an arbitrary module.

lem-sfb-finite-graded-proj-section-comparison vs lem-sfb-proj-section-module-reconstruction: the existing statement is the counit for an arbitrary quasi-coherent sheaf; it does not assert coherence from finite M or the unit/counit composite and hence the local invertibility of the canonical M-to-N map.

lem-sfb-finite-graded-proj-section-comparison vs lem-sfb-projective-coordinate-ring-euler-polynomial: the existing statement compares dimensions and Euler polynomials of coordinate rings; the new statement is an independent prerequisite with no Euler polynomial conclusion.

lem-sfb-finite-graded-proj-section-comparison vs lem-sfb-projective-curve-isom-graphs: the existing statement represents the curve isomorphism functor by graphs, not a fact about arbitrary finite graded modules.

lem-sfb-finite-graded-proj-section-comparison vs lem-sfb-standard-proj-coherent-section-finiteness: the existing statement assumes a coherent sheaf and proves finiteness of its nonnegative section module; it does not construct the canonical map or its local inverse, or prove the abstract tail criterion.

lem-sfb-finite-graded-proj-section-comparison vs lem-sfb-standard-proj-twist-tensor: the existing statement identifies tensor twists and shifted-module sheaves; it does not prove coherence or the unit/counit composite, and has no kernel/cokernel degree bound.

lem-sfb-graded-local-isomorphism-tail vs def-sfb-coordinate-quotient-grading: the existing statement constructs the grading on a quotient polynomial ring and says nothing about module-to-section maps or graded-map tails.

lem-sfb-graded-local-isomorphism-tail vs lem-sfb-finite-graded-module-section-tail: the item asserts the eventual canonical isomorphism to global sections; the geometric node only proves coherence and local comparison, and the algebraic node only applies to an abstract graded map already known to be locally invertible with finite N+.

lem-sfb-graded-local-isomorphism-tail vs lem-sfb-flat-graded-tail-proj: the existing statement concerns flat relative Proj and Hilbert polynomials of coordinate algebras, not arbitrary graded module maps.

lem-sfb-graded-local-isomorphism-tail vs lem-sfb-flat-projective-hilbert-polynomial-locality: the existing statement proves local constancy of fibre Hilbert polynomials for flat projective families, not either new assertion.

lem-sfb-graded-local-isomorphism-tail vs lem-sfb-graded-proj-quotient-twist-comparison: the existing statement compares twists along a quotient of graded rings, rather than the section-unit map of an arbitrary module.

lem-sfb-graded-local-isomorphism-tail vs lem-sfb-projective-coordinate-ring-euler-polynomial: the existing statement compares dimensions and Euler polynomials of coordinate rings; the new statement is an independent prerequisite with no Euler polynomial conclusion.

lem-sfb-graded-local-isomorphism-tail vs lem-sfb-projective-curve-isom-graphs: the existing statement represents the curve isomorphism functor by graphs, not a fact about arbitrary finite graded modules.

lem-sfb-graded-local-isomorphism-tail vs lem-sfb-standard-proj-coherent-section-finiteness: the existing statement assumes a coherent sheaf and proves finiteness of its nonnegative section module; it does not construct the canonical map or its local inverse, or prove the abstract tail criterion.

lem-sfb-graded-local-isomorphism-tail vs lem-sfb-standard-proj-twist-tensor: the existing statement identifies tensor twists and shifted-module sheaves; it does not prove coherence or the unit/counit composite, and has no kernel/cokernel degree bound.

lem-sfb-finite-graded-proj-section-comparison vs lem-per-finite-graded-module-dehomogenization: the existing statement proves finite generation of a degree-zero localized module for a nonnegative graded M, without Noetherianity or degree-one generation. It does not assert coherence or compare the supplied module to all its twisted sections; its finiteness calculation is a possible tool, not the new statement.

lem-sfb-graded-local-isomorphism-tail vs lem-sc-graded-localization-exact: the existing statement preserves exactness under localization for arbitrary graded maps; it has no finite-generation assumption and no eventual degree bound or bijectivity conclusion.

## Validation

The first dry run exited with the missing-review-heading diagnostic. The repaired delivery is to be checked by the prescribed server check_dag, review_split and deliver.py --no-push, and pushed only after the final dry run exits OK. Results will be appended here.
