# Repair report: lem-trf-ml-countable-colimit

## Files written

- dag/nodes/sec-trace-formula/lem-trf-ml-countable-colimit.json: statement, existing Lean records, source and maintainer fields preserved; replaced the five-step proof with assembly of three independent supporting statements.
- lem-trf-hom-product-stabilization-factorization: statement, unsplit, no Mathlib match.
- lem-trf-countable-directed-function-closure: statement, unsplit, no Mathlib match.
- lem-trf-restricted-colimit-generators-kernels: statement, unsplit, no Mathlib match.
- report.md and citations.json: this review and verbatim statements for every step citation.

## Attachments

None. Searching the project for the blueprint tag and the countable restricted-colimit notion found the existing Sheaf.SecTraceFormula.MLCountableColimit theorem, whose proof is sorry. No finished project declaration states the item or any extracted lemma. No Lean was written or compiled.

## WANTED

None. All sources used are in literature/stacks-project/algebra.tex. No SGA source is used.

## What was wrong and what changed

This repairs the 2026-10-22 human re-split return: the retained five-step proof was 3014 characters, and its separate arguments needed independent tasks. The sandbox initially contained only .brief2/.brief3/.brief4/.brief5, with no delivered node, report or search log. I therefore recovered the exact returned five-step proof from the current read-only repository, saved it as returned-item.json in this sandbox, and preserved it verbatim below. There was no retained search log to reuse. The item statement is unchanged. The new node files are statement-only, status unsplit, proof and proof_deps empty, proof_origin null. They are ready for separate workers; none restates the item's countable-colimit conclusion.

The product-Hom lemma captures the old Step 2 independently of finite presentation, a colimit, countability or a tensor ML condition. The closure lemma captures the whole alternating enlargement argument of old Step 3 independently of modules. The restricted-colimit criterion captures old Steps 4 and 5 independently of finite presentation, ML or countability. Old Step 1 remains explicitly in the assembly: it chooses representatives of a countable generating set and adds an initial index, including the empty generating-set case. These are three comparable proof obligations (old argument lengths 600, 939, and 1068), rather than one renamed copy of the item.

## Extracted arguments retained for future workers

### lem-trf-hom-product-stabilization-factorization

Read Tag 059E, proposition-ML-characterization, proof of (5) implies (3). Fix i and choose j by the stated stabilization hypothesis for P. Let e_j:M_j→P send an element to that element in component j and zero elsewhere. The map e_j composed with f_ij is in the image from Hom(M_j,P); for k≥j, equality of images supplies a_k:M_k→P with a_k f_ik=e_j f_ij. Project to coordinate j, obtaining h_k f_ik=f_ij. For an arbitrary k≥i, choose an upper bound l≥j,k and set h_{i,k}=h_l f_kl. Then h_{i,k} f_ik=h_l f_il=f_ij. This explicitly retains and repairs the source's incomplete final sentence, which only treats comparable j,k: neither comparability nor a linear order is assumed. No finite presentation was used. The family product is indexed by the small set I.

### lem-trf-countable-directed-function-closure

Read Tag 059W, lemma-ML-countable-colimit, the alternating countable-set construction. Choose i_* in I and start with S_0=S∪{i_*}. Given a countable nonempty set A, adjoin s(A), still countable and nonempty. To enlarge a resulting countable nonempty T to a directed countable set, enumerate it as (t_n), repeating entries if finite. Set u_0=t_0; recursively choose u_{n+1}≥u_n,t_{n+1}. Then D=T∪{u_n} is countable and directed, since any two elements of D lie below one u_n. Iterate A↦D(A∪s(A)) countably often, keeping every earlier element, and let J be the union. J contains S and i_*. Each pair of elements belongs to one finite stage and has an upper bound in a later stage. Each i in J has s(i) in the next stage. Thus J is countable, nonempty, directed and s-closed. No monotonicity or extensiveness of s was used. This is the old Step 3 argument with its choices and induction written out, not a request for an uncountable cofinal subset.

### lem-trf-restricted-colimit-generators-kernels

Read Tag 059W, final two paragraphs. Use the statement of lem-weil-pbc-filtered-colimit-modules-elementwise, not any internal construction from its proof. For surjectivity, every generator in E has a representative at a J-stage; each finite linear combination is represented at one common upper J-stage. These combinations exhaust M. If E is empty then M=0 and surjectivity is immediate. For injectivity, represent a restricted-colimit element at M_i with i in J. If its image in M is zero, the full-system zero clause gives k≥i killing that representative. The stipulated j in J has ker(f_ik)⊆ker(f_ij), so the representative dies at j. The zero clause for the J-system now kills the original class. Thus the canonical map is injective and surjective, hence a module isomorphism (the inverse function of a bijective linear map is linear). Both index categories are small and nonempty filtered: I by assumption, J by its inherited directed order. No stage-to-M map is assumed injective, and J need not be cofinal in I. This contains all work of old Steps 4 and 5.

## Review by Q78

I read coord/brief-stage1.md, stages/1-dag.md, the three-level route in SETUP.md, GOAL.md, the worker role, the chapter and sk-i-curve-zero unit, and delivery-errors B–E in full. I also read the current blueprint ancestor lem-trf-local-term-locality, the existing item's entire proof and Lean statement, Stacks 059W in full, Stacks 059E including the (5)⇒(3) proof, and the statement of 059M identifying the tensor-product module condition. The ancestor's supporting module-theory route is unchanged, as are the chapter and unit.

For new Step 1 I opened lem-weil-pbc-filtered-colimit-modules-elementwise: clause (1) gives a stage representative for every generator of the given colimit. I checked smallness, nonemptiness and directedness of I. The extra i_* is necessary when M=0 has an empty generating set.

For new Step 2 I opened lem-trf-mittag-leffler-hom-systems: its statement explicitly quantifies over every module N without finiteness restrictions, so P=∏M_s is permitted, and its conclusion is exactly the image-equality hypothesis of the new product-Hom lemma. The finitely presented stages and tensor-product ML hypothesis are precisely the item's hypotheses. I read the new product-Hom statement against the explicit injection/projection argument above, especially the common-upper-bound correction for incomparable j,k. No conclusion is borrowed from the Hom-system node's proof.

For new Step 3 I checked the closure lemma's complete statement: it returns a nonempty countable J containing the initial set, directed with inherited order and closed under the actual chosen function s. The choices in Step 2 give s:I→I with i≤s(i); monotonicity is neither needed nor claimed. Thus the bound and factorization live at the same J-index j=s(i). Every piece of the old countable-union argument is preserved in the extracted argument above.

For new Step 4 I opened the restricted-colimit criterion and checked each hypothesis separately: Step 1 provides E and its representatives; Step 3 puts those indices in J; composition with h sends zero to zero, giving exactly the required kernel inclusions. The criterion states an isomorphism of the canonical map induced by the restricted cocone, the same map as the item. I read def-weil-pbc-category-colimit to verify this canonical map, and the elementwise node for both the full-system and restricted-system zero tests used in the retained criterion argument. The original surjectivity and injectivity work is preserved above and in the original-proof appendix. citations.json quotes the actual statements, verbatim, for all five citations in the four-step assembly.

Edge cases checked: the zero ring and zero modules; M=0 with E empty (S_0 still contains i_*); finite or singleton I; finite countable sets with repeated enumeration; S empty and constant or nonmonotone s in the closure lemma; incomparable j,k in the product-Hom lemma; J=I or proper noncofinal J; transition maps and cocone maps with nontrivial kernels in the comparison lemma. None needs a cofinality assumption, finite M_i in the abstract Hom lemma, or injective transition maps. Empty I and empty J are excluded where their nonemptiness is used.

I checked delivery-errors B1–B10: self-contained objects, inline products and directed-system identities, cited colimit notion, literal TeX, correct tags and source labels, honest logged searches, no false Mathlib leaf, filled blueprint provenance and no finished Lean attachment. I checked C1–C8 against every cited statement; all non-elementary assembly claims are cited, new nodes have no outgoing proof edges, and the only off-unit proof citation is the preexisting Mathlib elementwise leaf. I checked D1–D5: the three lemmas separate product factorization, a pure order construction, and a general colimit comparison rather than cloning the item's conclusion. I checked E1–E7 through the hypotheses and small cases above. No statement dispute or target change was needed.

## Searches and provenance

Before creation I searched the whole DAG by tag 059E/059W, countable directed/closure keywords, Hom-product stabilization and restricted-colimit kernel/generator keywords, and read the nearby candidate statements. tools/blueprint_refs.py ancestor returned lem-trf-local-term-locality; searches for countable directed, factorization Mittag, 059W, 059E, countable closure, restricted colimit and colimit generators kernel returned no blueprint duplicate. The created nodes use the existing ancestor via chain prefixed by this item, and same_as=[].

All new nodes have exact queries/results recorded from msearch.py in searches.jsonl. I ran LeanFinder twice with different phrasing, LeanSearch, Loogle and grep for each obligation. LeanFinder found only direct-limit constructions and adic identities for the Hom lemma; ordinary countable enumeration and already-directed sequences for the closure lemma; and colimit presentations/representatives or eventually constant diagrams for the comparison lemma. Loogle's LinearMap range lemmas do not quantify over a directed system or prove uniform factorization; Set.Countable, DirectedOn finds measure lemmas, not function-closed directed enlargement. The comparison query has no Loogle hit. Reading Module.DirectLimit.lift_injective at Algebra/Colimit/Module.lean:157 confirmed it requires every stage-to-target map injective, which the comparison criterion does not. CofilteredSystem.lean gives inverse-system ML predicates, not the Hom-product bridge. AtTopBot/CountablyGenerated assumes a countable directed ambient type and gives a filter basis, rather than constructing a countable function-closed directed subset of an arbitrary directed type. Thus all three new nodes remain unsplit, with no Mathlib leaves.

## Not duplicates

lem-trf-hom-product-stabilization-factorization vs lem-trf-mittag-leffler-hom-systems: the existing node derives Hom-image stabilization from a tensor ML colimit of finitely presented modules; the new node assumes only Hom-image stabilization for the product of stages and concludes uniform transition factorizations for arbitrary module systems.
lem-trf-hom-product-stabilization-factorization vs lem-trf-mittag-leffler-eventual-domination: the existing node characterizes a colimit's tensor ML property by tensor-kernel domination of its canonical maps; the new node has no colimit or tensor hypothesis and extracts transition factorizations from product-Hom images.
lem-trf-countable-directed-function-closure vs lem-trf-ml-countable-colimit: the existing item extracts a countable module presentation under finite presentation and ML assumptions; the new lemma constructs only an invariant directed subset for an arbitrary function on a directed poset and says nothing about colimits or modules.
lem-trf-restricted-colimit-generators-kernels vs lem-trf-ml-countable-colimit: the item constructs a countable J using finite presentation and ML; the new criterion starts with an arbitrary directed J and explicit spanning and kernel-capture assumptions, and proves only that its canonical map is an isomorphism. It neither constructs J nor implies the item's hypotheses supply it.
lem-trf-countable-directed-function-closure vs lem-trf-countable-coordinate-closure: the coordinate lemma closes supports of a linear endomorphism in a direct sum, whereas the new lemma also ensures internal upper bounds in a completely general directed poset with an arbitrary unary function.
lem-trf-countable-directed-function-closure vs lem-coef-small-directed-superset: the existing cardinal lemma produces a small directed superset without closure under a chosen function; the new lemma supplies that additional invariance, for which iterating directed enlargement is necessary.
lem-trf-countable-directed-function-closure vs lem-coef-sharp-filtered-poset-subsets: its cardinal hypotheses yield internally filtered subsets but no closure under a chosen function; it does not replace the new iterative invariant-subset lemma in one specialization.
lem-trf-countable-directed-function-closure vs lem-coef-filtered-colimit-cardinal-regrouping: the regrouping lemma constructs subcategories of size less than an uncountable regular cardinal, without closure under a chosen unary function; specializing lambda to aleph_1 does not provide the extra invariance and needs an additional iteration.

## Dry-run repair

The first server preflight required a node citation in each new statement: I added def-weil-pbc-category-colimit for the Hom lemma’s use of a diagram and def-sfb-countable-set for the injection-into-natural-numbers meaning of countability. I opened both statements and checked that these are exactly the notions used. The former does not assert the Hom-system theorem; the latter adds no countability assumption on I. citations.json was regenerated to retain verbatim quotes of the updated new statements. These definition dependencies introduce no proof route changes.

## What remains

The three supporting statements are intentionally unsplit, as required by the re-split brief. Their exact arguments are retained above for independent workers. No other part of the assigned repair remains after successful dry run and push.

## Live-DAG promotion repair, 2026-10-22

The current return is L's promotion refusal: the earlier split had been completed in the side DAG but had not reached the live DAG used by the queue. I kept all four node files, the original-proof appendix, report, citations and searches. Before editing I ran the required initial dry run; it exited successfully at 096bf597534. The delivery tool prepares the replacement commit on its freshly fetched live base, so the new delivery is a promotion of the repaired split onto that base, not an unchanged re-push of the rejected side-project commit.

I compared returned-item.json with the current read-only repository item, field by field: they are identical. Compared with that live item, the retained item changes only proof, proof_deps and split_report. All three supporting node ids are still absent from the current repository. Thus the live item still needs the three extracted obligations, and there is no intervening statement or maintainer-field change to overwrite. The released stage-1 repair note still requests at least two independent statement-only obligations and an assembly of at most 3000 characters; this delivery keeps three and a four-step assembly below that limit.

I reread the current statements of lem-weil-pbc-filtered-colimit-modules-elementwise, lem-trf-mittag-leffler-hom-systems, def-trf-mittag-leffler-module, def-weil-pbc-category-colimit and def-sfb-countable-set, as well as all three retained new statements. Every quote in citations.json is still verbatim in the current cited statement. In Step 1 the elementwise clause supplies stage representatives. In Step 2 the Hom-system statement permits the unrestricted product P and gives exactly the stabilization hypothesis of the extracted factorization lemma. In Step 3 the function-closure statement applies without monotonicity of s. In Step 4 generator representatives and the explicitly proved kernel inclusion supply exactly the restricted-colimit criterion's hypotheses. None of these steps needs a stronger version of a current dependency or material hidden in its proof. I corrected Step 2's source wording: the incomparable-index argument is now carried by the extracted lemma, rather than written in that short assembly step itself.

I reread Stacks algebra.tex, lemma-ML-countable-colimit (059W), proposition-ML-characterization (059E), and proposition-ML-tensor (059M), including the product-coordinate proof. The three retained supporting arguments still realize those exact places. I reread the chapter and unit records and the current Lean theorem; the latter still ends in sorry and is not an attachment. The current project-source search found no finished WeilConjectures declaration for this countable extraction. The existing logged search results were read and retained, without rerunning unchanged questions or adding invented searches. Searching current DAG statements by 059E and 059W still gives the related Hom-system, domination, and projectivity statements distinguished above, not any of the three new statements.

For this repair I checked B–E again against the actual files and the current sources. The new nodes remain self-contained statement-only obligations; their notions are inline or have definition citations, and their search/provenance records remain intact. Each assembly citation states the fact used, both index categories are small and nonempty directed, and no off-route theorem or SGA source is added. The factorization argument handles incomparable indices using a common upper bound; the closure construction handles empty S, finite sets and nonmonotone s; the colimit comparison handles empty generators, zero modules, noninjective transitions and noncofinal J. The four assembly steps are each below 2000 characters and hide no further independent lemma. The final dry run and push below supersede the initial diagnostic receipt.

## Original returned proof (retained verbatim)

### Old Step 1

Choose a sequence $(x_n)$ (finite and repeated when necessary) whose finite $R$-linear span is $M$; if the generating set is empty then $M=0$ and we use the empty sequence. By [lem-weil-pbc-filtered-colimit-modules-elementwise], each $x_n$ is the image of an element of some $M_i$. Choose one such index for each $n$, and also choose $i_*\in I$; let $S_0$ be the resulting countable nonempty set of indices.

Uses: lem-weil-pbc-filtered-colimit-modules-elementwise.

### Old Step 2

Fix $i\in I$. Apply [lem-trf-mittag-leffler-hom-systems] with $N=\prod_{s\in I}M_s$. It gives $j\ge i$ such that the image of $\operatorname{Hom}_R(M_j,N)	o\operatorname{Hom}_R(M_i,N)$ equals the image for every $k\ge j$. Taking the $j$-component and the identity of $M_j$ yields, for every $k\ge j$, a map $h_k:M_k	o M_j$ with $f_{ij}=h_k f_{ik}$. For an arbitrary $k\ge i$, choose $\ell\ge j,k$ by directedness; then $f_{ij}=h_\ell f_{i\ell}=h_\ell f_{k\ell}f_{ik}$, so $f_{ij}$ factors through $f_{ik}$. Thus every $i$ has a stabilizing index $j$ with this factorization property for all $k\ge i$.

Uses: lem-trf-mittag-leffler-hom-systems.

### Old Step 3

Starting from $S_0$, alternate stabilization and directed enlargement. For every $i$ in the current countable set, adjoin a stabilizing index from Step 2, obtained using [lem-trf-mittag-leffler-hom-systems]. To enlarge any resulting nonempty countable set $T$ to a countable directed subset, enumerate it as $(t_n)_{n\ge0}$, repeating entries if finite. Set $u_0=t_0$ and recursively choose $u_{n+1}\ge u_n,t_{n+1}$ in $I$. Then $T\cup\{u_n:n\ge0\}$ is countable and directed: each of its two elements lies below some common $u_n$. Repeat the two operations countably many times, retaining all earlier indices, and let $J$ be the union. It is countable and nonempty. Any two elements lie together in some stage and have an upper bound at the next directed enlargement. Every $i\in J$ receives its stabilizing index in a subsequent stabilization stage. Thus $J$ is directed and has the factorization property from Step 2 for every $i\in J$.

Uses: lem-trf-mittag-leffler-hom-systems.

### Old Step 4

The canonical map $\operatorname{colim}_{i\in J}M_i	o M$ is surjective. Indeed, each generator $x_n$ comes from a stage in $J$ by construction. A finite sum of such generators and scalar multiples is represented at one stage of $J$ after taking a common upper bound of the finitely many stages, and these sums exhaust $M$; if $M=0$ the assertion is immediate. The map is the canonical map induced by the restricted cocone in [def-weil-pbc-category-colimit].

Uses: lem-weil-pbc-filtered-colimit-modules-elementwise, def-weil-pbc-category-colimit.

### Old Step 5

For injectivity, let a class represented by $\tilde{x}\in M_i$ with $i\in J$ map to zero in $M$. The equality and zero clauses of [lem-weil-pbc-filtered-colimit-modules-elementwise] give $k\ge i$ with $f_{ik}(\tilde{x})=0$. By the factorization property of $J$ from Step 3, choose $j\in J$ and $h:M_k\to M_j$ with $f_{ij}=h f_{ik}$; hence $f_{ij}(\tilde{x})=0$. Applying the same zero clause to the restricted filtered system indexed by $J$ shows that the original class is zero in $\operatorname{colim}_{i\in J}M_i$. The canonical map is therefore injective and surjective, hence an isomorphism of $R$-modules.

Uses: lem-weil-pbc-filtered-colimit-modules-elementwise, def-weil-pbc-category-colimit.


## Renewed promotion return: current-base reconciliation

This retry retains the complete prior split, its proof appendix, citations, and original searches. The initial required dry run completed with OK (not pushed) at b633d38f1e3. I then compared the archived returned-item.json, the current read-only repository item, and the sandbox item as parsed JSON. Returned and current items are identical in every field. The sandbox differs only in proof, proof_deps, and split_report; all current statement, statement dependencies, source, blueprint, Lean records, review records, and other metadata are retained. The three new ids are absent from the current read repository. The delivery tool freshly fetches the server base and constructs its own worktree, providing the requested rebase without a git command in the read-only repository.

I reread the current cited statements and all three new statements. All five citations.json entries remain verbatim, and each entry corresponds to precisely one of the five uses in the four-step proof. The product-Hom application now explicitly notes that the current Hom-system statement permits every module N without a finiteness assumption. This is necessary because its specialization is the full small product of the stages, which need not be finitely presented. The finite-presentation assumption belongs to the source stages, where the item supplies it. This refinement changes the assembly proof while preserving the original argument and statement.

I reread Stacks 059W in full, the product-coordinate (5)⇒(3) argument of 059E, and the equivalence in 059M. The four assembly steps have the same hypotheses and conclusions as their current citations: representative existence, uniform transition factorizations, countable function-closed directed enlargement, and the restricted-colimit isomorphism criterion. In particular the kernel implication in Step 4 is written explicitly, and no cofinality or injectivity hypothesis is slipped in. The report retains the complete extracted proofs, including the common-upper-bound repair of the source's incomparable-index omission and the empty-generating-set case.

I also reread the existing countable-coordinate, small-directed-superset, sharp-filtered-poset, cardinal-regrouping and eventual-domination statements. They do not subsume the three obligations, for the reasons in Not duplicates. The fresh blueprint searches for countable directed, 059W, and Hom product have no blueprint matches, and ancestor lookup still gives lem-trf-local-term-locality. The project source search finds no finished countable-extraction declaration; the existing Sheaf theorem still ends in sorry. The retained logged Mathlib hits and their verdicts were read and reused; no statement or search question changed.

Review by Q78 for this retry: B–E were checked against these actual current statements and source passages. Each new node is self-contained and statement-only; each non-elementary assembly operation cites its complete result, and every cited hypothesis is supplied above. The zero-module, empty-generator, singleton-index, incomparable-index, nonmonotone-function and noncofinal-subset cases remain covered. Every assembly step is below 2000 characters and their combined text is below 3000. No source, target, route, or Lean file was changed. The subsequent final dry run and push are the delivery of this reconciled version.


## Promotion-return repair, 2026-10-23

The required initial dry run exited 0 with `OK (not pushed)` at e63a3ffabd7. This is a new repair of L's refusal to land a side-DAG completion into the live queue DAG. I compared the archived returned item, the retained sandbox item, and the present read-only live item as parsed JSON: returned and live items agree in every field; the sandbox changes only proof, proof_deps, and split_report. I rebuilt the sandbox item from the current live JSON, carrying across only those three permitted fields. Thus all current statement, source, blueprint, Lean and maintainer records are retained. The delivery tool's fresh fetched base supplies the delivery rebase. All three new ids are still absent from the current repository, and the released stage-1 re-split order still requires these obligations.

This repair also makes the proof concrete against the current criterion: Step 1 now names the given countable generating set E, the cocone maps u_i, and one stage representative (i(x), y_x) for each x in E. Step 4 explicitly applies the comparison criterion to this same E and those same representatives. This removes the former change of notation from a possibly empty generating sequence to an unnamed set and records exactly why its image indices are countable. No statement or hypothesis changed. The previous sequence argument and all three extracted proofs are preserved above.

For this retry I reread algebra.tex Tag 059W (lemma-ML-countable-colimit), Tag 059E (proposition-ML-characterization), in particular (5) implies (3), and Tag 059M (proposition-ML-tensor). I read all five cited statements and checked every citations.json quote against its present statement. Step 1 uses only the elementwise lemma's representative clause; Step 2's unrestricted product is allowed by the Hom-system statement and supplies the product-factorization hypothesis; Step 3 uses precisely function-closed directed enlargement; Step 4 proves the kernel inclusion by evaluating h at zero, so that every hypothesis of the general comparison criterion is supplied. No step takes a result from a cited proof instead of its statement.

I checked B--E again against the actual files: the three supporting nodes remain complete, statement-only, independently smaller obligations with the old arguments retained in this report. They have unchanged genuine search records, sources and provenance. The logged Mathlib results were read and reused because the supporting statements and search questions are unchanged; no new search record was invented. Current blueprint searches for countable directed, 059W and Hom product returned no duplicate; the ancestor is still lem-trf-local-term-locality. I reread the candidate cardinal-enlargement, coordinate-closure and eventual-domination statements distinguished in Not duplicates. None provides the required additional unary-function invariance or the product-Hom factorization/comparison conclusions. The project-source search still has no finished attachment, and the existing Sheaf theorem explicitly ends in sorry.

The relevant small cases remain E empty and M zero (the extra i_* ensures nonemptiness), finite or singleton I, incomparable stabilization and vanishing indices (use a common upper bound in the extracted factorization proof), nonmonotone s (closure needs no monotonicity), and proper noncofinal J with noninjective transitions (the kernel condition replaces cofinality and injectivity). Both index diagrams used by the comparison are small nonempty directed diagrams. All four assembly steps are below 2000 characters and their total is below 3000. No SGA source, Lean edit, compiler call, or repository write was used. The final dry run and push of this repaired content follow this review.
