# Worker report: lem-sfb-high-genus-hom-closure

Repair of the 2026-10-22 batch-5 return. The dispatcher described retained files, but this item's sandbox initially contained only .brief markers. I therefore copied the current shared-repository item without running git there. The current reviewed ten-step argument matches the return's lengths; returned-node.json preserves that full baseline. The initial required dry run exited with the missing report diagnostic. No prior report or searches.jsonl existed in this sandbox. Existing item searches, citations, metadata and statement from the live copy are retained; all searches for the three new tasks were genuinely run with msearch.py and are in searches.jsonl.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-high-genus-hom-closure.json: unchanged statement; five-step assembly, originally 2875 characters, then 2919, and now 2954 after the current promotion repair.
- dag/nodes/sec-six-functors-basics/lem-sfb-projective-hom-graph-parameter.json: statement, unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-nodal-trait-map-extension.json: statement, unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-quasiprojective-point-closure-projectivity.json: statement, unsplit, no Mathlib match.
- report.md and citations.json; searches.jsonl is the unmodified search-command log. Local helper files and the returned-node.json preservation copy stay in the sandbox and are not DAG deliveries.

## Attachments

None. Searches for the item tag and the Hom/nodal/closure notions in lean/WeilConjectures found no exact project declaration without sorry. The landed Sheaf/AlgebraicGeometry/HighGenusHomClosure.lean main theorem ends in sorry at line 189; naturality and the group-action theorem end in sorry at lines 230 and 288. Their explicit nodal, reducedness, smooth/geometrically-integral generic fibre and no-rational-maps hypotheses agree with this item's statement; they are not completed proofs.

## WANTED

WANTED: literature/de-jong-families-curves-alterations-1997.pdf, printed p.609, sections 3.9--3.12 and Lemma 3.13, for the item and the three new nodes. The primary publisher PDF https://aif.centre-mersenne.org/item/10.5802/aif.1575.pdf was opened and printed p.609 was read online. Nothing was downloaded or written to literature. The new results are agent formulations expanding that route, rather than claims that the generalized statements occur verbatim in de Jong.

## What was wrong and what was repaired

The return requests workload distribution: the accepted 8686-character proof is too much for a single worker. Its mathematical statement is unchanged. Three independent unsplit tasks now carry the geometric arguments; each has a complete quantified statement, definitions, a source, genuine semantic and Loogle and source-grep searches, and no proof steps or proof dependencies. The old argument is not shortened out of existence: its full text is assigned below as the work brief for each new node. The item merely checks hypotheses, obtains the three inputs and proves naturality/action laws explicitly. There is no statement dispute, no route change, no new axiom, no compiler use, and no write outside the sandbox.

The three tasks are comparable substantive arguments: old steps 1--3 (2467 characters), old steps 4--6 (2900 characters), and old steps 7--8 (2085 characters). The base-change/DVR set-up from old step 4 stays explicit in assembly step 2; its properness-criterion use belongs to the third task. Returned step 9 is retained as assembly step 4; step 10 remains the elementary action calculation in assembly step 5, with its reference renumbered and its composition formula made explicit. The full old text is preserved below. No new node restates the whole item: the first has no curve or rational-map condition; the second is a local trait graph theorem with no Hom parameter space; the third is a general closure criterion with DVR lifting as an assumption and no curves or morphism functor.

## Searches and duplicate review

Before creation I searched all DAG node statements and titles for relative morphism/Hom representability, nodal traits and map extensions, quasi-projective proper closures, generic-DVR criteria, and the source tags 0D1A, 0D1B and 0208. Blueprint searches used morphism functor, nodal, generic point, Hilbert, valuative, rational curve and closure, across the whole import. The Hilbert hits concern finite-degree Hilbert schemes of points, not graphs of arbitrary maps. The valuative hits concern valuation tests, not H-projective closure with a dense-base-open conclusion. Existing generic-DVR properness, graph-open Hilbert, projective Hilbert representability, rational domination, finite birational normality, and generic-fibre spreading nodes are reused as the children's existing inputs; none states a whole child. Each new id was checked absent from the live DAG and no completed project Lean declaration was found. The ancestor command returns None, as for the item's existing imported alteration chain; new blueprint.from.node follows that exact answer, via prepends the item to its existing via chain, and place identifies the precise returned steps. same_as is empty on all three.

All three search groups have a second semantic phrasing, plus Loogle and grep. For the first two groups LeanSearch was rate-limited and is recorded unavailable; LeanFinder and Loogle completed. The third LeanSearch completed but found no match. The semantic hits are Proj properness/constructions, general valuation-ring criteria, rational-map APIs and elliptic-curve points. They neither provide the Hom parameter construction nor the nodal contraction theorem nor the generic-point DVR closure criterion. I read Mathlib/AlgebraicGeometry/ValuativeCriterion.lean, whose future-project note explicitly says the Noetherian DVR criterion is not implemented, and Proj/Proper's general valuative existence theorem; neither makes the third task a one-line leaf.

## Not duplicates

lem-sfb-projective-hom-graph-parameter vs def-sfb-proper-hilbert-presheaf: the existing node defines a presheaf of proper closed families; the new node constructs a scheme with projective-polynomial pieces and controls a generic point's closure.
lem-sfb-projective-hom-graph-parameter vs def-sfb-relative-morphisms-presheaf: the existing node only defines relative maps and graphs; the new theorem constructs a representing scheme and generic closure.
lem-sfb-projective-hom-graph-parameter vs lem-sfb-projective-curve-isom-graphs: that node concerns isomorphisms between flat curve families; this node concerns every map into an arbitrary H-projective target, and generic closure properties.
lem-sfb-projective-hom-graph-parameter vs lem-sfb-graphs-open-in-hilbert: the existing theorem supplies the graph-open transformation, not projective Hilbert pieces, an actual representing scheme, or properties of the generic reduced closure. It is an input to the new task.
lem-sfb-projective-hom-graph-parameter vs lem-sfb-projective-hilbert-polynomial-representability: the latter represents all flat projective closed families; it is combined with the graph-open theorem and a separate generic-closure argument.
lem-sfb-projective-hom-graph-parameter vs lem-sfb-space-hom-representability: the latter gives an algebraic space locally of finite presentation, not a scheme expressed as opens in projective Hilbert pieces or a reduced generic point closure.
lem-sfb-projective-hom-graph-parameter vs lem-pc-hilb-representable: the latter is finite-degree Hilbert representability for zero-dimensional subschemes; graph Hilbert polynomials have positive degree for a curve source.
lem-sfb-nodal-trait-map-extension vs lem-sfb-nodal-trait-rational-domination: the existing lemma has no target or extension conclusion; it constructs a dominating modification with rational fibres. The new task proves its images are singletons, the graph is finite, and normality makes it an isomorphism.
lem-sfb-nodal-trait-map-extension vs lem-sfb-nodal-trait-regularization: regularization resolves the nodal source; it gives no extension to a specified target, or isomorphism of a graph projection.
lem-sfb-nodal-trait-map-extension vs lem-sfb-high-genus-hom-closure: the new task is over a single DVR and has no Hom scheme, base modification, projective parameter closure, or naturality/group-action conclusion.
lem-sfb-quasiprojective-point-closure-projectivity vs lem-sfb-generic-dvr-properness-criterion: the existing criterion assumes lifts into R and concludes properness only; the new task assumes lifts into the ambient M, proves scheme-theoretic factorization, then a closed H-projective immersion and an isomorphism over a dense base open.
lem-sfb-quasiprojective-point-closure-projectivity vs lem-sfb-noetherian-dvr-properness: the existing node tests arbitrary DVR diagrams and concludes properness; the new task needs only the fixed function field, allows lifts initially into M, and proves projectivity and a dense-open isomorphism.
lem-sfb-quasiprojective-point-closure-projectivity vs lem-sfb-birational-isomorphism-dense-open: the existing theorem only supplies a dense-open isomorphism under birational hypotheses; it supplies neither ambient-lift factorization nor properness nor a closed projective embedding.
lem-sfb-quasiprojective-point-closure-projectivity vs lem-sbc-generic-fibre-iso-spread-base-open: spreading is an affine generic-isomorphism theorem; the new task globalizes it using properness and proves projectivity from the ambient immersion. Spreading remains its existing input.

lem-sfb-projective-hom-graph-parameter vs lem-sfb-bounded-double-graph-hilbert-locus: the existing theorem represents isomorphisms between two flat proper families over an affine base with a fixed graph polynomial; the new theorem represents all morphisms, allows a nonflat target and nonaffine integral base, and describes the reduced closure of a specified generic map. Neither statement specializes to the other whole statement.
lem-sfb-projective-hom-graph-parameter vs lem-sfb-graph-projection-functor-comparison: the existing theorem assumes a presheaf of closed families, an open graph locus and, for its representing conclusion, an existing Hilbert representative; it proves the formal graph comparison and evaluation. The new theorem constructs projective Hilbert pieces and proves integral generic-closure and finiteness properties absent there.
lem-sfb-projective-hom-graph-parameter vs lem-sfb-hilbert-graph-family-base-change: the existing theorem constructs a natural graph transformation and proves base-change stability of closed proper flat families; it does not represent the Hom functor by a scheme or describe a generic closure.
lem-sfb-quasiprojective-point-closure-projectivity vs lem-sfb-dvr-proper-domination-closed-immersion: the existing theorem assumes a proper domination and lifting of every DVR diagram into its base source, and concludes an ambient immersion is closed. The new theorem uses only the fixed function field of S, starts with lifts into the open ambient M, and proves factorization into R, properness, H-projectivity and an isomorphism over a dense base open.
lem-sfb-quasiprojective-point-closure-projectivity vs lem-sfb-integral-chow-envelope-compactification: the existing theorem constructs a proper surjective Chow envelope over an affine base and its projective closure, with no DVR-extension assumption; it does not prove the original R proper or projective. The new theorem already has a quasi-projective ambient embedding and uses DVR lifting to close it.
lem-sfb-quasiprojective-point-closure-projectivity vs lem-sfb-nongeneric-point-same-field-dvr: the existing theorem produces a DVR dominating a prescribed nongeneric local ring of an integral locally Noetherian scheme. It supplies neither ambient-lift factorization, properness, nor projectivity; the new theorem is a global closure criterion with lifts as a hypothesis.

## Review by Q128

I read the return against the actual live ten-step proof, the parent alteration blueprint ancestry and the current blueprint direct-image proof (3). The re-split remains inside exactly that de Jong prerequisite; no chapter or unit record was changed. I read de Jong p.609 online: 3.9 constructs Mor and the closure, Claim 3.10/3.12 use traits, 3.11 gives projectivity and the action, and 3.13 contracts rational exceptional curves. The general target replaces the source's genus hypothesis exactly at that contraction step. I read local Stacks quot.tex lemma-Mor-into-Hilb (0D1A) and lemma-Mor-into-Hilb-open (0D1B) for the first task, and limits.tex lemma-Noetherian-dvr-valuative-proper (0208) plus lemma-descend-finite-presentation (01ZM) for the third. I also read morphisms.tex H-projective base change/composition (01WF/01WE) and finite-birational-over-normal (0AB1). For the second task, I opened the statements of nodal-trait-rational-domination, projective-proper, finite-iff-proper-finite-fibres (02OG), and finite-birational-normal-iso, rather than taking properties from their proofs.

Assembly step 1 cites finite-type-over-noetherian only for Noetherianity after the explicit field argument. Projective-base-change uses the blueprint's H-projective convention, checked against def-pc-projective-morphism and def-kun-projective; composition supplies the finite ambient embedding. The new graph-parameter statement gives each claimed output explicitly: M, the open M_P in H_P, evaluation, integral separated finite-type locally finitely presented R, R_eta=Spec K, and function field K. Q needs no flatness, and W need not be nodal for this input.

Assembly step 2 cites projective-nodal-family-geometry for stability of projectivity/flatness/finite presentation and the connected nodal geometric fibres, with Noetherian T justified by the DVR principal-ideal argument. The reduced-fibre condition is preserved because geometric fibres are the same after base change; generic smoothness and geometric integrality are the original W_eta conditions. Projective-base-change gives H-projective Q_T. For every geometric point of T, composition with T to S supplies exactly the original no-rational-maps hypothesis, including for geometric points of C used in rational domination. The new trait extension statement then gives an actual map C to X. Representability in step 1 gives its map into M; connectedness of Spec A and the clopen polynomial component put the whole map in M_P. This last observation is written explicitly rather than silently applying a properness criterion with an ambient point in the wrong component.

Assembly step 3 cites the closure criterion, whose statement explicitly allows lifts into M instead of presupposing lifts into R, and explicitly concludes a closed immersion into H, H-projectivity and an isomorphism over a dense open. R and H_P satisfy its finiteness hypotheses from step 1, and step 2 supplies every DVR A subset K required in its quantifier, with no excellence or finite-type restriction on A. The child's factorization argument uses an ideal pulling back to zero in K and the injection A into K; it does not infer scheme-theoretic factorization from a set-theoretic image. Generic-fibre spreading is applied on affine S0 and V only; properness removes f(R minus V), which misses eta. These two distinctions retain the substantive content of old steps 7--8.

Assembly step 4 is the retained explicit conjugation argument on all test schemes. Inverse conjugation proves the representing schemes are isomorphic; it preserves the generic point, hence its reduced closure, and the same formula proves evaluation compatibility. Step 5 writes c_g(c_h(f))=c_{gh}(f) and c_1=id explicitly, giving the left group action and equivariance, including semilinear isomorphisms. Its references now point to assembly step 4, not old step 9. These are elementary once representation and closure are fixed, not a hidden geometric existence theorem. The action is canonical without preserving the chosen embedding or polynomial labelling. citations.json contains exact statement excerpts for every citation of every new assembly step.

For B1--B10 I checked that all new nodes are self-contained statement-only nodes with correctly escaped TeX and definitions, precise sources and blueprint places; no speculative Mathlib leaf was created. For C1--C8 I opened every cited statement, kept the proof_deps union exact, and kept only existing off-unit generic tools in split_report.tool_uses. For D1--D5 the three independent hypotheses/conclusions split distinct arguments; the full old work text below ensures no argument was hidden or removed. For E1--E7 I checked each hypothesis against the actual use, scheme versus topological closure, and actual fibre products; no statement correction was needed. All new assembly steps are below 2000 characters, total 2875, and all three children are left unsplit for parallel workers.

Small cases: W empty is allowed in the first general tool (the empty graph has polynomial zero), although the item excludes it. A smooth constant curve over a trait and constant u are covered by the second tool; its proof never uses a nonconstant function-field inclusion into X. A zero-dimensional or disconnected target is permitted, since only rational-curve images enter. The empty target has no generic morphism when W_eta is nonempty, so the quantified assertion is then vacuous. When S is Spec K, the third tool gives R=Spec K and has no nontrivial DVR subrings with compatible structure if K contains A inversely; when the generic closure already is S, the conclusion is the identity modification. A point closure of a K-rational point in a separated K-scheme is a reduced Spec K even if the ambient scheme has nilpotents. None of these tests needs normality of Q, flatness of Q, excellence of the trait, or preservation of reduced closures under arbitrary base change.

## Repair of the promotion return (2026-10-22)

L returned the accepted delivery because side completion had not been promoted into the live queue DAG, and requested a delivery based on the current DAG. I compared returned-node.json with the current shared-repository item: every field agrees, so there is no changed parent statement or proof to overwrite. The released stage-1 repair note still requires the re-split despite the old reviewed split flag. The three child ids are still absent from the live DAG. The delivery command rebuilds the commit against current origin/sheaf-dag while preserving maintainer-owned metadata; no git command was run in the read-only repository.

I re-opened the current statements of every assembly input and every input assigned to the three children, and compared the report's retained statement extracts and citations.json with those current statements. Every extract still matches; no changed hypothesis invalidates the retained split. I retained the three child statements, their genuine Mathlib searches and unavailable-service verdicts, all old proof text, and the existing source citations. I re-read de Jong printed p.609 (3.9--3.13), Stacks quot.tex 0D1A/0D1B and limits.tex 0208; the graph/Hilbert, trait contraction and generic-DVR closure route is unchanged.

The first resumed dry run exited with duplicate-review diagnostics for six newer live nodes. I opened all six statements: bounded-double-graph-hilbert-locus requires both families flat and represents isomorphisms with fixed polynomial, while graph-projection-functor-comparison and hilbert-graph-family-base-change supply only parts of the graph construction. The other three respectively prove a closed immersion under full DVR lifting and proper domination, construct a Chow envelope, and produce a local dominating DVR. None states a child or a generalization of its complete conclusion. The six comparisons under Not duplicates record the precise differences. This repairs the current-DAG failure rather than merely rebasing an unchanged report.

I also corrected assembly step 5's stale Step 9 references to Step 4 and replaced the ambiguous composition-order sentence with the formula c_g(c_h(f))=c_{gh}(f). This is the elementary substitution of the left-action identities on W and Q, with no new lemma or changed hypothesis. The original old sentence remains below for provenance. The item statement is byte-identical to the live statement, its proof is under 3000 characters, its citation union is unchanged, and every step is under 2000 characters. Small-case checks remain valid, including constant maps, empty source for the first tool, nonflat target, S a field, and semilinear actions. Search questions and all three new statements are unchanged, so no logged Mathlib search was repeated.

## Resumed promotion repair: current-DAG comparison (2026-10-22)

The first dry run of this resumed attempt passed at e88c6a366cc. I nevertheless performed the requested comparison rather than treating an earlier receipt as completion. The preserved returned-node.json and the current read-clone item agree in every JSON field, including its stage-2 Lean and review records; the sandbox differs only in proof, proof_deps and split_report. Its three child ids remain absent from the current DAG. Thus no changed parent hypothesis or new child collision requires replacing the retained mathematical plan. The delivery tool supplies the fresh server base; I ran no git command in the shared repository.

I read the current statements of all eight assembly citations (seven distinct nodes) and all fourteen existing inputs named in the retained child work briefs. The eight entries of citations.json still occur verbatim in those statements and exactly cover the assembly's uses pairs. The trait-geometry input explicitly gives base-change stability only for Noetherian bases; assembly Step 2 proves this for Spec A before applying it. Its reduced-fibre assertion follows from the same geometric fibres, not from commuting reduction with arbitrary base change. The graph/Hilbert statements give the actual open transformation, not merely a definition of the morphism presheaf. The generic-DVR criterion quantifies over all DVR subrings of the source function field; the closure child identifies that field with K and permits lifts first into M. The finite-birational result still requires normality of C, supplied by rational domination in the child work brief.

I re-read de Jong printed p.609, sections 3.9--3.12 and Lemma 3.13, at the publisher PDF, and local Stacks quot.tex lemma-Mor-into-Hilb / lemma-Mor-into-Hilb-open (0D1A/0D1B) and limits.tex lemma-Noetherian-dvr-valuative-proper (0208). The three retained child statements keep precisely the previously reviewed graph construction, trait contraction and projective-closure route. I checked the three live Lean theorem bodies: all still end in sorry, so there is no completed attachment. The genuine searches.jsonl results and all new-node Mathlib records remain unchanged because neither their statements nor their search questions changed.

The repaired delivery also changes the assembly text: Step 1 now specifies the H-projective projection W times_S Q to W before composing with W to S, and explicitly obtains H-projective finite-type H_P from the parameter lemma. These are the exact hypotheses subsequently used in Step 3; they are no longer left implicit in the phrase about a finite projective embedding. The existing citation quotes already cover both facts, so no citation or new lemma is needed. The resulting assembly has 2919 characters, with step lengths 649, 753, 364, 757 and 396, below both the assembly limit and the long-step threshold. Item and child statements, the three independent tasks, all retained original proof text, and the constant-map/nonflat-target/field-base checks are preserved. This report and the actual proof adjustment accompany the fresh-base delivery, rather than an unchanged re-push.

## Current promotion-return repair (2026-10-23)

The required initial dry run passed at 02c0550486f. I compared the retained returned-node.json, the sandbox item, and the current read-clone item without git commands in the read-only repository. The returned head and current live item agree in every field. The sandbox changes only proof, proof_deps and split_report; the three child ids remain absent from the live DAG. The released stage-1 keep_plan order still requires at least two independent statement-only tasks and an assembly of at most 3000 characters. This delivery retains all three tasks and every old argument in the work briefs above. The delivery tool rebuilds against the current server branch; an earlier side-project completion is not treated as a live landing.

I re-opened the statements of all seven distinct assembly inputs and the fourteen existing inputs allocated to the children. There are no changed cited statements requiring a different proof. All eight citations.json entries are verbatim in the current statements and cover exactly the step/node citation pairs. Step 1 still uses the explicit H-projective convention in def-pc-projective-morphism and def-kun-projective; Step 2 meets the nodal-family base-change theorem's Noetherian-base requirement because the DVR is Noetherian. Step 3 uses precisely the closure criterion's lifts into the open ambient M_P, rather than presupposing lifts into R. I made its unique scheme-theoretic factorization conclusion explicit in the assembly, using the existing citation that already states it. The assembly now has 2954 characters; no step exceeds 2000 characters.

For the source check I re-read de Jong printed p.609, sections 3.9--3.13, at [the publisher PDF](https://aif.centre-mersenne.org/item/10.5802/aif.1575.pdf), together with local Stacks quot.tex lemma-Mor-into-Hilb and lemma-Mor-into-Hilb-open (0D1A/0D1B), and limits.tex lemma-Noetherian-dvr-valuative-proper (0208). These supply, respectively, the graph parameter, trait-contraction and generic-DVR closure route described in the existing signed review. The constant-map case is handled by the graph argument, not the source's function-field inclusion for a nonconstant map. The child statements and search questions are unchanged: I read the retained searches.jsonl results, including actual unavailable LeanSearch responses, and reused them without inventing or repeating searches. Fresh whole-blueprint searches for morphism functor, nodal trait and 0208 found no replacement blueprint node. The first fresh dry run found no additional same-tag duplicate-review failures.

The live project's HighGenusHomClosure.lean existence, naturality and action theorems still have sorry at lines 189, 230 and 288; exact-tag and declaration-name searches in WeilConjectures yielded no finished attachment. The previously signed checks of B--E still apply to the unchanged child statements: they are statement-only, self-contained, distinct in scope, and sourced; no target flatness or integrality is assumed, constant maps and a field base are allowed, and the action is independent of an embedding. This repair changes the actual assembly as well as the report and obtains a fresh-base delivery; it is not an unchanged re-push. No Lean, compiler, Lake, repository write or launcher edit was used.

## Full argument allocated to the new statement-only tasks

These are work briefs in the report, not proof fields in the new nodes. Every old sentence is retained; the new workers must prove the precisely stated intermediate results and can reuse all cited existing DAG inputs. The original old-node statement and proof also remain in returned-node.json.


### lem-sfb-projective-hom-graph-parameter

Old steps 1, 2, 3:


Returned step 1:

A field is Noetherian, since its only ideals are $0$ and the unit ideal. Thus [lem-weil-pbc-finite-type-over-noetherian] makes $S$ Noetherian. Apply [lem-pc-projective-base-change] to $Q\to S$ and $W\to S$, and then [lem-trf-h-projective-composition]: $E=W\times_SQ\to S$ is H-projective. By [lem-pc-projective-proper], both $W\to S$ and $Q\to S$ are proper, in particular separated. Choose a finite projective-space embedding of $E$.

Existing inputs: lem-weil-pbc-finite-type-over-noetherian, lem-pc-projective-base-change, lem-trf-h-projective-composition, lem-pc-projective-proper.


Returned step 2:

Apply [lem-sfb-projective-hilbert-polynomial-representability] to $E\to S$. Its Hilbert functor is represented by $H=\coprod_P H_P$, with $H_P$ H-projective and of finite type over $S$. Apply [lem-sfb-graphs-open-in-hilbert] with $Z=W$ and $X=Q$: the hypotheses are properness, flatness and finite presentation of $W$, and separatedness of $Q$, all available. A closed subscheme of $E_T$ is proper over $T$, because $E_T\to T$ is proper by [lem-pc-projective-proper] and a closed immersion is proper; so the flat finitely presented closed subschemes of the Hilbert theorem are exactly the proper flat finitely presented ones of the graph statement. Its graph transformation identifies the required morphism functor with an open subscheme $M\subset H$. Consequently $M=\coprod_P M_P$, where $M_P=M\cap H_P$ is quasi-projective over $S$, meaning an open subscheme of an H-projective $S$-scheme. Its inverse graph projection gives the universal evaluation $W\times_SM\to Q\times_SM$.

Existing inputs: lem-sfb-projective-hilbert-polynomial-representability, lem-sfb-graphs-open-in-hilbert, lem-pc-projective-proper.


Returned step 3:

Let $m:\operatorname{Spec}K\to M$ be the point of $u_\eta$. It belongs to one $M_P$, which is open and closed in $M$. Thus its reduced closure $R$ lies in this same $M_P$. A closure of a point is irreducible; giving it the reduced induced structure makes $R$ integral. Since $S$ is Noetherian, $H_P$ and its open $M_P$ are Noetherian, and $R\to S$ is finite type and separated. On restricting to $\eta$, closure and reduction localize. The point $m$ is closed in $M_\eta$: it is the image of a section of the separated $K$-scheme $M_\eta$. Hence $R_\eta=\operatorname{Spec}K$, with its given structure map. In particular $k(R)=K$. Moreover $R\to S$ is locally of finite presentation: locally, a finite-type algebra is a quotient of a finite polynomial algebra over a Noetherian ring; that polynomial algebra is Noetherian by [lem-weil-pbc-finite-type-over-noetherian], so its kernel ideal is finitely generated. Birationality is proved in Step 8, after properness. Restrict the evaluation of Step 2 to $R$; its generic restriction is precisely $u_\eta$.

Existing inputs: lem-weil-pbc-finite-type-over-noetherian.


Input-statement checks for this task:


lem-weil-pbc-finite-type-over-noetherian:

Call a scheme Noetherian if it is locally Noetherian [pqf-def-locnoeth] and quasi-compact (Stacks Properties, Definition 01OV). Let $f:X\to S$ be a morphism of schemes [def-pc-scheme] of finite type [def-weil-finite-type-morphism] with $S$ Noetherian. Then $X$ is Noetherian. In particular $\operatorname{Spec}\mathbf Z$ is Noetherian ($\mathbf Z$ being a Noetherian ring), so every scheme of finite type over $\operatorname{Spec}\mathbf Z$ is Noetherian.


lem-pc-projective-base-change:

Let $f:X\to S$ be a projective morphism of schemes [def-pc-scheme, def-pc-projective-morphism] and let $g:S'\to S$ be any morphism of schemes [def-pc-scheme]. Form the fibre product $X':=X\times_S S'$ [def-pc-fibre-product, def-pc-base-change] and let $f':X'\to S'$ be its projection. Then $f'$ is projective [def-pc-projective-morphism].


lem-trf-h-projective-composition:

If $g:X\to Y$ and $h:Y\to S$ are H-projective morphisms [def-kun-projective], then the composite $h\circ g:X\to S$ is H-projective.


lem-pc-projective-proper:

A projective morphism of schemes is proper. In particular a
smooth projective curve
over a field is proper over it, and its base changes along field
extensions are proper.


lem-sfb-projective-hilbert-polynomial-representability:

Let $S$ be a Noetherian scheme [pqf-def-locnoeth] (quasi-compact and locally Noetherian), and let $E\hookrightarrow\mathbf P^n_S$ be a closed immersion [def-weil-closed-immersion, def-kun-projective]. For an $S$-scheme $T$, put $E_T=E\times_ST$ [def-pc-fibre-product], and let $\operatorname{Hilb}_{E/S}(T)$ be the set of closed subschemes $Z\subset E_T$ flat [def-weil-flat-morphism] and finitely presented [def-sbc-locally-finite-presentation] over $T$. Pullback makes this a functor, represented by a scheme $H=\coprod_P H_P$. The index is the numerical Hilbert polynomial of each geometric fibre with respect to the specified projective embedding: the polynomial eventually equal to the dimension of the degree-$m$ part of its homogeneous coordinate ring. Each $H_P\to S$ is H-projective [def-kun-projective], hence separated and of finite type [def-weil-proper-morphism, def-weil-finite-type-morphism], and $H_P$ represents the subfunctor with fibre Hilbert polynomial $P$ everywhere. The universal closed subscheme in $E\times_SH$ and this identification commute with arbitrary base change. No flatness of $E\to S$ is assumed. The empty subscheme is allowed.


lem-sfb-graphs-open-in-hilbert:

Let $S$ be a scheme [def-pc-scheme]. Let $Z\to S$ be proper [def-weil-proper-morphism], flat [def-weil-flat-morphism] and finitely presented [def-sbc-locally-finite-presentation], and let $X\to S$ be separated [def-weil-proper-morphism]. Write $Z_T=Z\times_ST$, $X_T=X\times_ST$ [def-pc-fibre-product]. The graph construction is a natural injective transformation from $T\mapsto\operatorname{Hom}_T(Z_T,X_T)$ into the functor of closed subschemes [def-weil-closed-immersion] of $(Z\times_SX)_T$ that are proper, flat and finitely presented over $T$. This transformation is representable by open immersions [def-weil-open-immersion]. Explicitly, for each such closed subscheme $D\subset Z_T\times_TX_T$, there is an open $U\subset T$ such that, for every $T'\to T$, $D_{T'}\to Z_{T'}$ is an isomorphism exactly when $T'\to T$ factors through $U$. On this open the corresponding morphism is $\operatorname{pr}_2\circ(\operatorname{pr}_1|_D)^{-1}$. In particular, any representing Hilbert scheme contains the relative morphism functor as this open subscheme, with universal evaluation and compatibility with all base changes.


### lem-sfb-nodal-trait-map-extension

Old steps 4, 5, 6:


Returned step 4:

To prove properness use [lem-sfb-generic-dvr-properness-criterion] with the integral source $R$, whose function field is $K$ by Step 3. Fix a DVR $A\subset K$ with fraction field $K$ and a compatible $b:T=\operatorname{Spec}A\to S$. By [lem-trf-projective-nodal-family-geometry], $C=W_T\to T$ retains projectivity, flatness, finite presentation and the connected nodal geometric curve fibres; $T$ is Noetherian because a DVR is a principal ideal ring, and [lem-weil-pbc-finite-type-over-noetherian] makes $C$ Noetherian. Its generic fibre is the given smooth geometrically integral $W_\eta$. Put $X=Q_T$, which is H-projective by [lem-pc-projective-base-change]. Let $\Gamma$ be the reduced closure of the graph of $u_\eta$ in $C\times_TX$. The graph over $K$ is closed because $X_K$ is separated, so $\Gamma_K\to C_K$ is an isomorphism. The graph is integral and its reduced closure is integral. The projection $p:\Gamma\to C$ is H-projective: $C\times_TX\to C$ is H-projective by base change, and restricting its projective-space embedding to a closed subscheme is again a closed immersion.

Existing inputs: lem-sfb-generic-dvr-properness-criterion, lem-trf-projective-nodal-family-geometry, lem-pc-projective-base-change, lem-weil-pbc-finite-type-over-noetherian.


Returned step 5:

Apply [lem-sfb-nodal-trait-rational-domination] to $C/T$ and $p:\Gamma\to C$. It says $C$ is normal integral and supplies $Y\xrightarrow{a}\Gamma\xrightarrow{p}C$, with $a$ proper surjective and $h=pa$ having reduced geometric fibres that are points or connected unions of projective lines. Compose $Y\to\Gamma\subset C\times_TX$ with projection to $X$. Over each geometric point of $C$, each of those lines maps constantly into the corresponding geometric fibre of $Q\to S$ by the hypothesis that every geometric morphism $\mathbf P^1_\Omega\to Q_\Omega$ is constant. Constants on intersecting components agree, and the intersection graph of a finite connected union is connected. Thus the whole geometric fibre has a singleton image in $X$. The same is immediate for a point fibre. Surjectivity of $a$ persists after field extension: a nonempty fibre has a point with residue field $L$, and tensoring $L$ with a field extension is nonzero (a vector-space basis remains a basis). Thus, since $a$ is surjective after base change, the geometric fibre of $\Gamma\to C$, as a subscheme of $X$ over that point, has a singleton underlying space. In particular every ordinary fibre of $p$ has finitely many points.

Existing inputs: lem-sfb-nodal-trait-rational-domination.


Returned step 6:

The morphism $p$ is proper by [lem-pc-projective-proper] and $C$ is locally Noetherian. Its fibres are finite by Step 5, so [thm-pqf-finite-iff-proper-finite-fibres] makes $p$ finite. It is birational between integral schemes, since it is an isomorphism on the dense generic fibre. Its target $C$ is normal by Step 5. Hence [lem-trf-finite-birational-normal-iso] makes $p$ an isomorphism. Compose $p^{-1}$ with $\Gamma\to X$ to obtain a $T$-morphism $C\to X$ extending $u_\eta$. This also treats constant $u_\eta$, without a separate lifting argument or any flatness or integrality assumption on $X$.

Existing inputs: lem-pc-projective-proper, thm-pqf-finite-iff-proper-finite-fibres, lem-trf-finite-birational-normal-iso.


Input-statement checks for this task:


lem-sfb-generic-dvr-properness-criterion:

Let $S$ be a locally Noetherian scheme [pqf-def-locnoeth], and let $f:R\to S$ be separated and of finite type [def-weil-proper-morphism, def-weil-finite-type-morphism], with $R$ integral [def-pc-integral-scheme], generic point $\xi$ [def-sc-generic-point], and function field $L=\kappa(\xi)$ [def-sc-function-field]. Suppose that for every discrete valuation subring $A\subset L$ [def-sc-discrete-valuation-ring] with fraction field $L$, and every morphism $b:\operatorname{Spec}A\to S$ whose generic restriction is $\operatorname{Spec}L\to R\xrightarrow{f}S$, the canonical generic-point morphism $\operatorname{Spec}L\to R$ extends to a morphism $\operatorname{Spec}A\to R$ over $b$ [def-weil-affine-spectrum]. Then $f$ is proper [def-weil-proper-morphism]. Conversely properness implies this extension property. The extension, whenever it exists, is unique.


lem-trf-projective-nodal-family-geometry:

Let $Y$ be a Noetherian scheme (a scheme with a finite affine open cover by spectra of Noetherian rings). Let $f:X\to Y$ be a projective flat finitely presented morphism all of whose geometric fibres are nonempty connected curves of pure dimension $1$, smooth except at ordinary double points. The ordinary double point condition means that the completed local ring on a geometric fibre at a singular point is $\Omega[[u,v]]/(uv)$ with $\Omega$ algebraically closed. Then the relative smooth locus $U\subset X$ is open, and there exists a closed subscheme $S_f\subset X$ with underlying set $X\setminus U$, unramified over $Y$ and with finite underlying fibres. For every morphism $Y_1\to Y$ with $Y_1$ Noetherian, the base change $f_1:X\times_Y Y_1\to Y_1$ again has all of these projectivity, flatness, finite presentation, connectedness, dimension, and nodal singularity properties. Its smooth locus is $U\times_Y Y_1$, and $S_f\times_Y Y_1$ is a closed unramified subscheme supported exactly on its nonsmooth locus. No assertion that taking the reduced closed subscheme commutes with base change is made.

Conventions for the notions used here: Noetherian rings [def-weil-pbc-noetherian-ring]; projectivity [def-kun-projective]; flatness [def-weil-flat-morphism]; finite presentation [def-sbc-locally-finite-presentation]; geometric integrality, connectedness and reducedness [def-pc-geometrically-irreducible]; smoothness [def-sbc-smooth-morphisms]; reduction [def-weil-pbc-scheme-reduction]; fibre products and base change [def-pc-fibre-product]; unramified morphisms [def-weil-unramified-morphism]; closed subschemes [def-weil-closed-immersion]; dimension [def-kun-dimension].


lem-pc-projective-base-change:

Let $f:X\to S$ be a projective morphism of schemes [def-pc-scheme, def-pc-projective-morphism] and let $g:S'\to S$ be any morphism of schemes [def-pc-scheme]. Form the fibre product $X':=X\times_S S'$ [def-pc-fibre-product, def-pc-base-change] and let $f':X'\to S'$ be its projection. Then $f'$ is projective [def-pc-projective-morphism].


lem-weil-pbc-finite-type-over-noetherian:

Call a scheme Noetherian if it is locally Noetherian [pqf-def-locnoeth] and quasi-compact (Stacks Properties, Definition 01OV). Let $f:X\to S$ be a morphism of schemes [def-pc-scheme] of finite type [def-weil-finite-type-morphism] with $S$ Noetherian. Then $X$ is Noetherian. In particular $\operatorname{Spec}\mathbf Z$ is Noetherian ($\mathbf Z$ being a Noetherian ring), so every scheme of finite type over $\operatorname{Spec}\mathbf Z$ is Noetherian.


lem-sfb-nodal-trait-rational-domination:

Let $A$ be a discrete valuation ring [def-sc-discrete-valuation-ring], with fraction field $F$, and put $T=\operatorname{Spec}A$ [def-weil-affine-spectrum]. Let $C\to T$ be H-projective [def-kun-projective], flat [def-weil-flat-morphism] and finitely presented [def-sbc-locally-finite-presentation], with smooth geometrically integral generic fibre [def-sbc-smooth-morphisms, def-pc-geometrically-irreducible] and nonempty connected reduced geometric fibres of pure dimension one [def-weil-geometric-fibre, def-kun-topological-krull-dimension]. Suppose every singularity of a geometric fibre has completed local ring $\Omega[[u,v]]/(uv)$ [def-weil-pbc-adic-completion, def-weil-pbc-multivariate-power-series]. Then $C$ is integral [def-pc-integral-scheme] and normal, meaning that all its local rings are integrally closed domains. For every integral $\Gamma$ with an H-projective morphism $p:\Gamma\to C$ whose restriction over $\operatorname{Spec}F$ is an isomorphism, there are an integral scheme $Y$, an H-projective morphism $h:Y\to C$ also an isomorphism over $\operatorname{Spec}F$, and a proper surjective $C$-morphism $a:Y\to\Gamma$ [def-weil-proper-morphism, def-weil-surjective-morphism], with $pa=h$, having the following property: for every algebraically closed field $\Omega$ and $\operatorname{Spec}\Omega\to C$, the reduction [def-weil-pbc-scheme-reduction] of the geometric fibre $Y\times_C\operatorname{Spec}\Omega$ is either a point or a nonempty connected union of finitely many irreducible components, each isomorphic to $\mathbf P^1_\Omega$ [def-sc-p1-standard].


lem-pc-projective-proper:

A projective morphism of schemes is proper. In particular a
smooth projective curve
over a field is proper over it, and its base changes along field
extensions are proper.


thm-pqf-finite-iff-proper-finite-fibres:

Let $f:X\to S$ be a morphism of schemes, where $S$ is
locally Noetherian. The following are
equivalent:

1. **(1)** $f$ is
finite;
1. **(2)** $f$ is
proper with finite
fibres, in the sense of
[pqf-def-quasifinite].

(*Stacks Project, Cohomology of Schemes, Lemma 30.21.1, Tag
[02OG](https://stacks.math.columbia.edu/tag/02OG).*)


lem-trf-finite-birational-normal-iso:

Let $X$ and $Y$ be integral schemes [def-pc-integral-scheme], and let $f:X\to Y$ be a finite morphism [def-weil-finite-integral-morphism] inducing an isomorphism $k(Y)\xrightarrow{\sim}k(X)$ of function fields [def-sc-function-field]. Assume every local ring of $Y$ is a normal domain in the sense of [def-weil-pbc-normal-ring]. Then $f$ is an isomorphism.


### lem-sfb-quasiprojective-point-closure-projectivity

Old steps 7, 8:


Returned step 7:

The representing property in Step 2 sends this extension to a morphism $v:T\to M$ with generic restriction $m$. It factors through $R$ scheme-theoretically: any local equation of the reduced closure $R$ pulls back to a function that vanishes on the generic point of $T$; it is zero because $A\hookrightarrow K$. This local calculation gives the factorization on an affine cover. Thus every DVR diagram of Step 4 lifts to $R$. The criterion [lem-sfb-generic-dvr-properness-criterion] now proves $R\to S$ proper. Uniqueness is included in that criterion, using the separatedness already checked in Step 3.

Existing inputs: lem-sfb-generic-dvr-properness-criterion.


Returned step 8:

The immersion $R\hookrightarrow M_P\hookrightarrow H_P$ is proper by [lem-weil-pbc-proper-to-separated], since $R\to S$ is proper and $H_P\to S$ is separated. By [lem-weil-pbc-proper-immersion-closed] it is a closed immersion. Compose it with a closed immersion $H_P\hookrightarrow\mathbf P^N_S$ supplied by Step 2; composition of closed immersions is checked on affine rings by composition of surjections. This gives H-projectivity of $R\to S$. Birationality: write $f:R\to S$. Choose a nonempty affine open $S_0\subset S$; it contains $\eta$ and is integral. Choose an affine open $V\subset f^{-1}(S_0)$ containing $m$. By Step 3, $V_\eta$ is an open subscheme of $R_\eta=\operatorname{Spec}K$ containing $m$, so $V_\eta\to\operatorname{Spec}\kappa(\eta)$ is an isomorphism, and $V\to S_0$ is locally of finite presentation by Step 3. Apply [lem-sbc-generic-fibre-iso-spread-base-open] to $V\to S_0$ and $\mathrm{id}:S_0\to S_0$: there are an open $U\ni\eta$ of $S_0$ and an isomorphism $V\cap f^{-1}(U)\to U$ over $S_0$; as it commutes with the structure maps, it equals $f$. Since $f$ is proper, it is a closed map, so $f(R\setminus V)$ is closed; it misses $\eta$ because $f^{-1}(\eta)=\{m\}\subset V$. Thus $U_1=U\setminus f(R\setminus V)$ is a dense open (it contains the generic point), $f^{-1}(U_1)\subset V\cap f^{-1}(U)$, and $f^{-1}(U_1)\to U_1$ is an isomorphism. Together with Step 3, this proves the asserted projective birational conclusion and extending evaluation.

Existing inputs: lem-weil-pbc-proper-to-separated, lem-weil-pbc-proper-immersion-closed, lem-sbc-generic-fibre-iso-spread-base-open.


Input-statement checks for this task:


lem-sfb-generic-dvr-properness-criterion:

Let $S$ be a locally Noetherian scheme [pqf-def-locnoeth], and let $f:R\to S$ be separated and of finite type [def-weil-proper-morphism, def-weil-finite-type-morphism], with $R$ integral [def-pc-integral-scheme], generic point $\xi$ [def-sc-generic-point], and function field $L=\kappa(\xi)$ [def-sc-function-field]. Suppose that for every discrete valuation subring $A\subset L$ [def-sc-discrete-valuation-ring] with fraction field $L$, and every morphism $b:\operatorname{Spec}A\to S$ whose generic restriction is $\operatorname{Spec}L\to R\xrightarrow{f}S$, the canonical generic-point morphism $\operatorname{Spec}L\to R$ extends to a morphism $\operatorname{Spec}A\to R$ over $b$ [def-weil-affine-spectrum]. Then $f$ is proper [def-weil-proper-morphism]. Conversely properness implies this extension property. The extension, whenever it exists, is unique.


lem-weil-pbc-proper-to-separated:

Let $f:X\to Y$ be proper and let $g:X\to W$ be a $Y$-morphism with $W$
separated [def-weil-pbc-scheme-conventions] over $Y$. Then $g$ is proper.


lem-weil-pbc-proper-immersion-closed:

Let $f:X\to Y$ be a morphism of schemes which is proper (separated, of finite type and universally closed, [def-weil-proper-morphism], as in [def-weil-pbc-scheme-conventions]) and an immersion (it factors as a closed immersion $X\to U$ followed by an open immersion $U\to Y$, [def-weil-closed-immersion], [def-weil-open-immersion]). Then the image $f(X)$ is a closed subset of $Y$, and $f$ is a closed immersion. (Only universal closedness of $f$ is used.)


lem-sbc-generic-fibre-iso-spread-base-open:

Let X,Y,S be affine schemes [def-weil-affine-spectrum], S integral [def-pc-integral-scheme], and f:X -> S and g:Y -> S locally finitely presented [def-sbc-locally-finite-presentation]. Let eta be a generic point and e:X_eta -> Y_eta an isomorphism of fibres [def-pc-scheme-fibre] over Spec kappa(eta). There exists an open U of S containing eta and an isomorphism f^{-1}(U) -> g^{-1}(U) commuting with their structure maps to S. The fibres may be empty.


The third task receives the generic-DVR properness application first introduced in returned step 4; the first task supplies the integral generic-closure prerequisites it assumes. The second task proves the local graph theorem independently; base-change set-up is in assembly step 2. The first task's sources use the existing projective Hilbert representability theorem as a black box (not a new duplicate); the second uses the existing rational-domination theorem as a black box (not a new regularization node).

### Retained naturality and action arguments

These old assembly arguments remain visible here as well as their current corrected forms in the item.

Returned step 9:

For compatible isomorphisms $\alpha_S:S\simeq S'$, $\alpha_W:W\simeq W'$ and $\alpha_Q:Q\simeq Q'$ preserving the generic morphism, conjugation sends a map $f:W_T\to Q_T$ to $\alpha_Q\circ f\circ\alpha_W^{-1}$ over the transported test scheme. The inverse conjugation makes this an isomorphism of the represented morphism functors, hence of their representing schemes by uniqueness of representing objects. It takes $m$ to $m'$, and therefore takes its topological closure with reduced induced structure to the corresponding $R'$. Universal evaluation commutes with this isomorphism because the displayed conjugation formula holds on every test scheme. This argument uses the intrinsic representing functor, so no projective embedding needs to be preserved.

Returned step 10:

For a finite group action on the datum, apply Step 9 to each group element. Identity conjugation is the identity, and conjugation for $gh$ is conjugation for $g$ followed by that for $h$ in the prescribed left-action order. Thus uniqueness of the represented maps gives the action laws on $R$. The evaluation identity of Step 9 for each group element is exactly equivariance. The calculation also applies to semilinear isomorphisms induced by automorphisms of the ground field.

## What could not be finished

No mathematical part of the requested re-split remains. Required server dry run and delivery results are recorded after execution.

## Delivery validation

Historical dry run 189fd34cfb2 and the initial resumed dry run e88c6a366cc passed. The revised 2919-character assembly and current-DAG comparison passed the server dry run at 8d3b8319d04. A final receipt refresh after correcting the report input count precedes direct delivery. No Lean or build tool was run.
Current repair: initial fresh-base server dry run passed at 02c0550486f. Final validation below applies to the revised 2954-character assembly and this report.
