# Worker report: lem-trf-local-common-summand-surjections

## Files written

- dag/nodes/sec-trace-formula/lem-trf-local-common-summand-surjections.json: unchanged statement, four-step assembly, status split.
- dag/nodes/sec-trace-formula/lem-trf-field-common-section.json: statement, status unsplit; no Mathlib match after two semantic phrasings, LeanSearch, Loogle, and source grep.
- dag/nodes/sec-trace-formula/lem-trf-residue-simultaneous-section-lift.json: statement, status unsplit; no Mathlib match after two semantic phrasings, LeanSearch, Loogle, and two source greps.
- citations.json: one verbatim statement quotation for every node used by every parent proof step.

## Attachments

None. Project searches for the blueprint tag and common summand/complement/section found no exact finished declaration under lean/WeilConjectures. The recorded declaration exists_common_summand_surjections in lean/Sheaf/TraceFormula/LocalCommonSummandSurjections.lean:65 has a sorry proof. Its type agrees with the parent; it is not evidence of completion. No Lean file was changed and no compiler was run.

## WANTED

None. Stacks more-algebra.tex and the current blueprint are available locally.

## What was wrong and what changed

This is the human-mandated re-split of an otherwise correct but oversized proof. The sandbox held no node or report at start (only dispatcher markers), so the current repository's full eight-step version was copied and used as the returned argument. No prior argument or source was replaced. The mathematical statement and every maintainer-owned field stay unchanged. In particular there is no statement dispute and no route departure. The report below preserves the old proof paragraphs verbatim instead of shortening them to meet the size bound.

The two separate jobs are the graph-complement construction over a field (old steps 2--5, 2232 characters of argument) and the residue/column lifting and image argument (old steps 1,6--8, 2260 characters). They have comparable workloads and neither asserts the original local-ring common-summand conclusion: the first is only a field section, the second starts from a supplied good residue map and concludes properties of each lift and its image. The second node includes the explicit kernel decomposition and its inverse/projection formula, so all eight old argument paragraphs are assigned to new work items. The parent chooses U as that image and reads off the conclusions. The initial four parent proof texts totalled 1230 characters; after the landing-return clarifications the current total is 1394 characters, below 3000. No non-elementary parent step exceeds 2000 characters.

## What remains

The two new nodes intentionally have statements only, proof=[], proof_deps=[], proof_origin=null, status unsplit: other workers will split their proofs. Their complete inherited arguments are assigned below. No required parent argument is omitted.

## Not duplicates

lem-trf-field-common-section vs lem-trf-local-common-summand-surjections: the new statement is restricted to a field and produces a linear q with aq=id and bq invertible; it has no assertion about lifting through a local ring, nor a local-ring summand U. It carries the nontrivial graph-complement argument, not the parent's complete conclusion.
lem-trf-field-common-section vs lem-trf-surjective-two-term-determinant-calculus: the existing statement gives homotopy/composition identities for determinant maps of two-term complexes, not simultaneous sections of two maps of vector spaces.
lem-trf-residue-simultaneous-section-lift vs lem-trf-local-common-summand-surjections: the new statement assumes an externally supplied residue map q with both composites invertible, handles arbitrary alpha,beta without surjectivity, and asserts the coefficient lift and invertibility; it does not construct q. Its conditional image/kernel conclusions require that supplied certificate, so this is the lifting half of the argument rather than the original unconditional existence assertion.
lem-trf-residue-simultaneous-section-lift vs lem-trf-surjective-two-term-determinant-calculus: residue reduction and a matrix-lift certificate have no determinant complexes or homotopy identities, which are the existing node's content.
lem-trf-field-common-section vs lem-trf-vector-subspace-complement: that existing Mathlib leaf supplies a complement to ONE subspace; it supplies neither a simultaneous complement to two kernels nor the resulting q.
lem-trf-field-common-section vs lem-trf-equal-dimension-linear-equivalence: that leaf supplies theta between two spaces already known to have equal dimension; it supplies no graph complement or simultaneous section.
lem-trf-residue-simultaneous-section-lift vs lem-sc-local-free-base-change-reflects-iso: that generic tool only reflects an already given map's invertibility after a local base change. The new statement also forms reduced maps, proves surjectivity survives reduction, lifts every q by columns, and identifies the scalar extensions of the two composites. Those comparisons and the construction are not the existing statement.
lem-trf-residue-simultaneous-section-lift vs lem-pc-finite-free-map-residue-localization: that theorem finds a principal localization where an already given map has a specified property; it does not lift a prescribed residue linear map or identify the two composites.
lem-trf-residue-simultaneous-section-lift vs lem-sc-finite-locally-free-residue-isomorphism: that scheme theorem tests a given morphism on every fibre; it does not construct a coefficient lift through the residue quotient.

The whole DAG was searched for 0FJK and for common complement/summand, simultaneous complement, two surjections, residue section and column lifts. The only existing nodes whose source carries 0FJK are the parent and its determinant-calculus ancestor, distinguished above. Blueprint searches for common complement, common summand, simultaneous, surjective linear, residue lift and base change reflects found no statement matching either new node; broad residue field and finite free searches likewise supplied no match. The current ancestor remains lem-trf-local-term-locality; the full inherited via chain is retained and the item is prepended for the new nodes.

## Mathlib search assessment

All new searches were run using the required msearch.py command and their exact query strings, hit summaries and digests were transferred from searches.jsonl without inventing searches. The old parent's existing searches are retained. The field search hits are individual complements (Submodule.exists_isCompl), individual splittings and dimension criteria; none supplies one subspace simultaneously complementary to two kernels. The relevant source at Basis/VectorSpace.lean:280--283 was read, as was FiniteDimensional/Lemmas.lean:172--176. The lifting hits include Module.IsLocalRing.linearCombination_bijective_of_flat at RingTheory/LocalRing/Module.lean:294--301 and IsLocalRing.split_injective_iff_lTensor_residueField_injective at 334--337. Both were read: they are useful tools for a fixed family/map, but the new node's coefficient lift, tensor comparison, surjection reduction and the two-composite conclusion require the inherited argument, not a one-line specialization. No service was unavailable in this run.

## Review by Q26

I read Stacks more-algebra.tex, label lemma-homotopic-surjections (Tag 0FJK), including the final paragraph's explicit local-ring problem and its sentence that field linear algebra and residue-field lifting give the solution, with details omitted. This is the source for the parent and both new nodes; the supplied details remain marked agent-written. The field and lifting workloads are now 2232 and 2260 characters respectively; the latter includes the image calculation, so the original argument is fully distributed. I also read the current main-20261015 blueprint lem-trf-local-term-locality and the chapter/unit records; this repair acts only inside the existing auxiliary algebra input and changes no higher route.

For parent step 1 I checked the complete new residue-lifting statement: it explicitly makes k a field and states that the reductions of the given surjections are surjective. Its unique-maximal-ideal hypothesis is exactly the parent's local-ring hypothesis. For step 2 I checked the complete new field statement: a,b have the same finite source and target ranks, k is a field by step 1, both maps are surjective, and the statement supplies exactly aq=id and bq invertible. No infinite-field assumption is used. For step 3 I checked the lifting statement's quantified q and its conclusion for every lift: the field section from step 2 satisfies both invertibility hypotheses, so the asserted lift has alpha s and beta s invertible and s injective. For parent step 4 I checked the added image clause in the lifting statement: it asserts the two restriction isomorphisms, both kernel decompositions, and the explicit projection formula. Taking exactly U=im(s) gives the parent conclusion. The old argument proving this clause is preserved under old step 8 below and is assigned to the lifting work item: its inverse sends s(t) to t, and its projection to U is (gamma restricted to U)^(-1) gamma. No argument is lost in this transfer. I copied verbatim parts of precisely these statements into citations.json and checked each quotation.

For the future field argument I opened and read the actual statements of lem-trf-vector-subspace-complement (one arbitrary subspace has a direct complement), lem-weil-pbc-idempotent-charpoly-rank-nullity (dimension of image plus kernel equals source dimension), lem-trf-equal-dimension-linear-equivalence (finite equal dimensions give a bijective linear map), and def-weil-finite-dimensional-subspace (finite spanning family). They suffice at exactly the old uses recorded below: complement projection gives finite spanning families, and rank-nullity applies to a,b and to the projections with kernel C. The decompositions C+A0+B0+D are direct, and the displayed two subtraction formulas verify both complements even in characteristic two.

For the future lifting argument I read def-weil-pbc-free-module (basis), def-weil-module-base-change (tensor extension and its map), and lem-sc-local-free-base-change-reflects-iso (local ring homomorphisms reflect isomorphisms between finite free modules). The map rho is local because the target field has maximal ideal zero and its inverse image is m. The two maps to which reflection applies are alpha s and beta s, each from R^m to R^m; their tensor comparisons are checked on every standard vector, not assumed by an unexplained transport. The same local algebra tool can be used when that new item is split; no off-unit proof tool remains in the parent's assembly.

The boundary cases m=0 and n=0 allow empty bases and give U=0 whenever the hypotheses can hold; n=0 with m>0 cannot have a surjection over a nonzero local ring. If n=m, the residue surjections are already bijections, and q=a^(-1) works. The equal-kernel case has A0=B0=0 and the chosen D is the complement; transverse kernels allow the graph construction, including over F2. For the local-lift criterion the essential square finite-rank condition is present; injectivity of s follows from that of alpha s. No henselian, noetherian, completeness or infinite-residue-field hypothesis enters. The small finite checks are recorded below once run.

Against delivery-errors B--E I checked statement-only shape, self-contained objects and inline local terminology, single TeX escapes, actual tag/label, definition dependencies, source and blueprint fields, every real search, and the nearest ancestor. C1/C4 were checked by reading the statements just listed and by the quotes, not by taking facts from node proofs. D1/D2 are avoided by separating the field construction from the local lifting computation and including the image/decomposition calculation in the lifting item; no new node asserts the full parent. E's hypothesis and object checks include q having direction k^m to k^n and the square composites acting on R^m. Nothing in the original argument was disproved or silently removed; the correction is its distribution across two concurrent work items.

## Preserved argument and work allocation

The following paragraphs are copied verbatim from the repository's returned eight-step proof. They are worker guidance in this report, not proof fields on the new unsplit nodes.

### Old step 1 -> lem-trf-residue-simultaneous-section-lift

Let $\mathfrak m$ be the unique maximal ideal and $k=R/\mathfrak m$. This quotient is a field: for $a\notin\mathfrak m$, maximality gives $1=ra+b$ with $b\in\mathfrak m$, so $\bar r\bar a=1$. Reduction is a local ring homomorphism $\rho:R\to k$, since its inverse image of the maximal ideal $0$ of $k$ is $\mathfrak m$. Reducing the coefficients of $\alpha,\beta$ in the standard bases gives $k$-linear maps $a,b:k^n\to k^m$. Both are surjective: lift a target vector coordinatewise to $R^m$, choose a preimage under the corresponding original surjection, and reduce that preimage. Put $V=k^n$, $A=\ker a$ and $B=\ker b$. The case $m=0$ already has the solution $U=0$; the following argument also covers it.

Cited nodes: def-weil-pbc-free-module

### Old step 2 -> lem-trf-field-common-section

We first construct a simultaneous complement over $k$. Apply [lem-trf-vector-subspace-complement] to $C=A\cap B$ inside $A$ and inside $B$, obtaining $A=C\oplus A_0$ and $B=C\oplus B_0$. Apply it also to $A+B$ inside $V$, obtaining $V=(A+B)\oplus D$. Every subspace $P$ of $V$ is finite-dimensional: choose its complement using the same lemma and project the finite standard spanning family of $V$ onto $P$; the images span $P$. Thus all subspaces just named are finite-dimensional.

Cited nodes: lem-trf-vector-subspace-complement, def-weil-finite-dimensional-subspace, def-weil-pbc-free-module

### Old step 3 -> lem-trf-field-common-section

By [lem-weil-pbc-idempotent-charpoly-rank-nullity] applied to $a$ and $b$, $\dim A+m=n=\dim B+m$, hence $\dim A=\dim B$. Apply that same theorem to the projections $A\to A_0$ and $B\to B_0$ along $C$, whose kernels are $C$, to obtain $\dim A_0+\dim C=\dim A=\dim B=\dim B_0+\dim C$. Therefore $\dim A_0=\dim B_0$. By [lem-trf-equal-dimension-linear-equivalence] choose a linear isomorphism $\theta:A_0\to B_0$.

Cited nodes: lem-weil-pbc-idempotent-charpoly-rank-nullity, lem-trf-equal-dimension-linear-equivalence

### Old step 4 -> lem-trf-field-common-section

The sum $A+B=C\oplus A_0\oplus B_0$ is direct. Indeed if $c+x+y=0$ with $c\in C$, $x\in A_0$, $y\in B_0$, then $y=-c-x\in A\cap B=C$, so $y=0$ and then $c=x=0$. Consequently every vector of $V$ has unique coordinates $c+x+y+d$ in $C,A_0,B_0,D$. Define $G=\{x+\theta(x):x\in A_0\}$ and $\overline U=G+D$. This is a subspace by linearity of $\theta$, and its elements have unique expressions $x+\theta(x)+d$. The displayed decompositions justify these assertions directly, without a dimension count.

Cited nodes: none (elementary)

### Old step 5 -> lem-trf-field-common-section

The subspace $\overline U$ is complementary to both $A$ and $B$. For $v=c+x+y+d$, put $z=\theta^{-1}(y)$; then $v=(c+x-z)+(z+\theta(z)+d)$ lies in $A+\overline U$. Also $v=(c+y-\theta(x))+(x+\theta(x)+d)$ lies in $B+\overline U$. If $x+\theta(x)+d\in A$, the unique coordinates force $d=0$ and $\theta(x)=0$, so $x=0$. Membership in $B$ similarly forces $d=x=0$. Thus $a|_{\overline U}$ and $b|_{\overline U}$ are injective. They are surjective because $a,b$ are surjective and vanish on $A,B$, respectively: decompose any preimage using the corresponding direct sum. The inverse of $a|_{\overline U}$, followed by inclusion, is a linear map $q:k^m\to k^n$ with image $\overline U$, $aq=1$, and $bq$ an isomorphism. Linearity of the inverse follows by applying the injective linear map $a|_{\overline U}$ to the addition and scalar identities.

Cited nodes: none (elementary)

### Old step 6 -> lem-trf-residue-simultaneous-section-lift

For each standard basis vector $e_j$ of $k^m$, choose a vector $v_j\in R^n$ reducing to $q(e_j)$. Define $s:R^m\to R^n$ by $s((r_j))=\sum_j r_jv_j$. Its reduction is exactly $q$. In the scalar extension of [def-weil-module-base-change], identify $R^t\otimes_R k$ with $k^t$ by $(r_i)\otimes c\mapsto(\rho(r_i)c)$; its inverse is $(c_i)\mapsto\sum_i e_i\otimes c_i$. The tensor relations verify the two composites on the standard generators and pure tensors. Under these identifications, the scalar extensions of $\alpha s,\beta s:R^m\to R^m$ are $aq$ and $bq$, respectively: evaluate on each $e_j\otimes1$.

Cited nodes: def-weil-pbc-free-module, def-weil-module-base-change

### Old step 7 -> lem-trf-residue-simultaneous-section-lift

Apply [lem-sc-local-free-base-change-reflects-iso] to the local homomorphism $\rho:R\to k$ and separately to $\alpha s$ and $\beta s$. Both source and target are the finite free module $R^m$, and their scalar extensions are isomorphisms by steps 5--6. Hence $\alpha s$ and $\beta s$ are isomorphisms over $R$. In particular $s$ is injective: $s(t)=0$ implies $(\alpha s)(t)=0$ and then $t=0$.

Cited nodes: lem-sc-local-free-base-change-reflects-iso, def-weil-pbc-free-module, def-weil-module-base-change

### Old step 8 -> lem-trf-residue-simultaneous-section-lift

Set $U=\operatorname{im}s\subseteq R^n$. The map $s:R^m\to U$ is an isomorphism, with inverse $s(t)\mapsto t$ by injectivity. Thus $\alpha|_U$ and $\beta|_U$ are isomorphisms because their composites with this parametrization are $\alpha s$ and $\beta s$. Finally, for either $\gamma=\alpha$ or $\beta$, write $x=(x-u)+u$ with $u=(\gamma|_U)^{-1}(\gamma x)$; then $x-u\in\ker\gamma$. If $u\in U\cap\ker\gamma$, injectivity of $\gamma|_U$ gives $u=0$. This proves both asserted direct-sum decompositions. All sums and maps above allow empty standard bases.

Cited nodes: none (elementary)

## Small-case checks

A sandbox-only Python enumeration checked every pair of surjective F2-linear maps for (m,n)=(0,0),(0,2),(1,1),(1,2),(2,2),(2,3), including 1812 pairs altogether; every pair had q with aq=id and bq invertible. A separate enumeration over R=Z/4Z, m=1,n=2 checked all 768 good lifted columns for all alpha,beta and all q satisfying the two residue-composite conditions. Both lifted scalar composites were units and s was injective in every case. These are small-case sanity checks, not claimed as proofs. finite-checks.json records the counts and confirms that the parent statement is unchanged.


## Repair of the landing return (2026-10-22)

The return reports that the approved side-project completion had never been promoted to the live DAG. This retry continues the retained sandbox rather than replacing its split. The prior durable dry-run receipts name 7639cc6d3bf and 019665c7ecb; the first dry run in this retry completed at 84c0819c25f and passed preflight. The delivery tool fetches current sheaf-dag and rebuilds one delivery commit there, preserving current maintainer-owned fields. The live read clone still has the original eight-step proof. A field-by-field comparison found only proof, proof_deps, proof_origin and split_report different in the retained parent. In particular its statement, source, ancestry, statement dependency and Lean records agree with current live. Both proposed child ids are still absent from live, so both remain new work items.

I reread the current statements of both child nodes and every live node used by their statements or the preserved argument: def-weil-field, def-weil-pbc-free-module, def-weil-module-base-change, lem-trf-vector-subspace-complement, lem-weil-pbc-idempotent-charpoly-rank-nullity, lem-trf-equal-dimension-linear-equivalence, def-weil-finite-dimensional-subspace and lem-sc-local-free-base-change-reflects-iso. None is merged, and each still says the fact assigned to it above. Thus no dependency replacement is needed. I also reread the current Stacks final paragraph (more-algebra.tex:37092--37104), current chapter/unit records and main-20261015 ancestor statement/proof. This repair retains the auxiliary algebra route; it does not modify a higher unit.

For C4, assembly step 1 uses precisely the residue node's field and surjectivity assertions; step 2 uses precisely the field node's section and second-composite assertions; step 3 uses precisely the residue node's lift and invertibility assertions; step 4 uses precisely its image and kernel-decomposition assertions. I made the chosen lift's reduction equation explicit in step 3 so the lift used in step 4 is fixed with its certificate. The hypotheses checked are the same unique maximal ideal, finite coordinate ranks, and invertibility of aq and bq from step 2. The two-composite condition is not inferred from a one-map splitting theorem. All four citations.json quotes were checked again against the full current child statements and are verbatim.

For the repair order's preservation requirement, a direct check confirms that each of the eight current live proof paragraphs occurs verbatim in the retained report's allocation section. Both children remain statement-only with the same complete workloads; the parent remains a short assembly. The earlier small-case results and actual search log were read and retained, without inventing or repeating searches for an unchanged mathematical question. Project-source searches again find no exact finished WeilConjectures declaration; the Sheaf theorem at line 65 still ends in sorry. The historical report's description of starting from an empty sandbox refers to the first attempt, not this retry.


## Current landing-return retry

I continued the retained delivered sandbox, including its report, citations, two child statements, actual searches.jsonl results and finite-checks.json. The first required dry run exited successfully at 71e4e143677. The live return entry identifies the refused delivery as 432de369514 and reports an unpromoted side completion, rather than a mathematical defect. The delivery command fetches current origin/sheaf-dag and overlays only stage-1-owned fields, so this retry is rebased by the required tool; it preserves current Lean, audit, review and creation records.

I compared the retained parent with the current read clone field by field: only proof, proof_deps, proof_origin and split_report differ. The statement, statement dependencies, source, blueprint ancestry and all Lean records agree; the two child ids are still absent from live. I reread all eight live proof paragraphs and verified that each remains verbatim in this report. I reread the two child statements, the eight existing definition/tool statements listed in the previous repair section, Stacks 0FJK at lemma-homotopic-surjections, and the chapter, unit, current blueprint ancestor and released stage-1 repair note. The same hypotheses and citations remain valid, so no child statement or dependency replacement is required.

As a concrete refinement to the retained split, assembly step 3 now chooses the lifted standard columns v_j and writes s((r_j))=sum_j r_j v_j before invoking the child's scalar comparison and invertibility conclusions. This fixes the constructed map and the certificate used by step 4 explicitly. Step 1 still uses exactly the child's field and surjectivity assertions; step 2 uses exactly aq=id and bq invertible; step 3 uses exactly its column construction, reduction identity and conditional invertibility assertions; step 4 uses exactly its image and both kernel decompositions. Every citation remains a verbatim statement quotation and is checked again. No parent proof step exceeds 2000 characters, and the complete assembly remains below 3000.

The recorded Mathlib searches were read rather than repeated for unchanged statements. Their hits supply individual complements, dimension comparisons or single-map residue criteria, not either whole new statement. Source checks confirmed Submodule.exists_isCompl and the local-ring candidate criteria recorded above. The project-source search still gives no exact finished WeilConjectures declaration, and the Sheaf theorem still ends in sorry. Boundary cases remain m=0, n=0, equal ranks, equal kernels and characteristic two, including the retained finite enumerations. This retry changes neither a mathematical statement nor the inherited route. Final validation and push follow this report update.


## Landing-return repair and review, 2026-10-23

This is a repair of the promotion failure reported by L, not a replacement of the approved mathematics. I ran the retained delivery's dry run first: it exited 0 with OK at 58203cdbec3. The delivery tool fetched the current server DAG and rebuilt the commit there. I then compared every field of the retained parent with the current read clone. Only proof, proof_deps, proof_origin and split_report differ; the statement, statement dependencies, source, blueprint ancestry, creation, review and Lean records agree. Both proposed child files are still absent from the current DAG. The retained report records the previously refused head 432de369514; all mathematical content of that retained attempt, including its citations and search results, survives this repair.

I re-read both full child statements, all three definition dependencies (field, free module, module base change), and the current statements of the complement, rank-nullity, equal-dimension equivalence and local finite-free reflection nodes used in the preserved arguments. I also re-read the two nearby residue-isomorphism nodes distinguished under Not duplicates. No changed live statement requires a dependency substitution. All eight current live proof paragraphs occur verbatim in the preserved-argument section. The field and residue-lift workloads therefore remain separately available, including the full graph construction, tensor comparison and image calculation.

The concrete assembly correction in this retry is in step 4: it now specifies $u=s((gamma s)^{-1}(gamma x))$ and verifies both $x-uinkergamma$ and $Ucapkergamma=0$. This is the projection formula already in the lifting statement, expressed in the chosen parameter $s$, and spells out why the same image gives each decomposition. It adds no hypothesis or statement change. Step 1 still takes only field/reduction/surjectivity from the residue node; step 2 takes $aq=1$ and invertibility of $bq$ from the field node; step 3 takes the column lift, its reduction equation, and the two square-map isomorphisms from the residue node. Step 4's isomorphisms and projection are explicitly clauses of that residue statement, not assertions taken from its proof. Each citations.json quotation remains verbatim and covers its step. All ranks are finite; the local homomorphism is the quotient to the residue field, and both square composites act on $R^m$. Zero ranks and characteristic two remain covered by the inherited checks. No non-elementary step exceeds 2000 characters.

For the B--E review I re-opened Stacks more-algebra.tex at lemma-homotopic-surjections (Tag 0FJK), especially its final paragraph, for the parent and each child. Its omitted field/lifting details are exactly the two retained work allocations, with agent origin recorded. I re-read the current chapter and unit and the main-20261015 ancestor text; the repair stays within the inherited auxiliary algebra input. The child statements remain self-contained and statement-only, and neither asserts the parent's unconditional local-ring existence statement. Repeated DAG tag searches still find only this parent and the determinant-calculus ancestor with 0FJK; blueprint searches for common complement and residue lift return no matching node. The recorded Mathlib searches were read and reused because neither child statement nor search question changed. I re-opened the individual-complement, rank-nullity, and local-ring module candidates; none states either whole child. The project-source tag/notion searches find no exact completed WeilConjectures declaration, and the Sheaf declaration at line 65 still has sorry. No Lean file or launcher file was changed and no compiler was run. A final dry run and direct push follow this update.
