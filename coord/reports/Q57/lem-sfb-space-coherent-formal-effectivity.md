# Q57: lem-sfb-space-coherent-formal-effectivity

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-coherent-formal-effectivity.json: item split into five steps; statement preserved.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-complete-local-map-effectivity.json: statement, unsplit; no Mathlib match. Complete local algebraic-space points, Tag 0AQH.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-supported-adic-existence.json: statement, unsplit; no Mathlib match. Non-flat proper-support Grothendieck existence over an arbitrary complete Noetherian adic ring, Tags 08BE and 08BF.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-adic-flatness-near-closed-fibre.json: statement, unsplit; no Mathlib match. The open flat locus and its containment of the closed inverse image, Tag 08VP.
- citations.json: exact quotations for every node used by every step. search-results.json and searches.jsonl retain actual search results and the command's log. report.md is this report.

## Attachments

None. Searched the live WeilConjectures source for the exact blueprint id and the coherent/formal/effectivity notions. GrothendieckExistence.lean does contain scheme Grothendieck-existence statements, but their variable is X : Scheme, so they do not attach the algebraic-space item or its new algebraic-space existence input. No compiler or Lake command was run.

## WANTED

None: the sources needed are in literature/stacks-project/.

## Corrections and route

The imported item was unsplit and had no proof. Its statement is correct against quot.tex, Tag 08W9 (lemma-coherent-existence), and Situation 08KB (situation-coherent). I preserved every hypothesis and conclusion. In particular I did not assume that X is proper, that B is separated, that B is of finite type, or that f is flat. I did not use algebraicity of the coherent-family stack to prove its effectivity: that would be circular in the parent stack-algebraicity proof.

The inherited unit is sk-thm-sf-ctf-stability. I read its DAG record and the current blueprint at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, especially (3). This is the inherited stable-moduli/Quot prerequisite branch of that direct-image route; the proof below the item follows the cited Stacks input exactly. The ancestor tool reports None, as does the live item's blueprint.from.node; I retained that field and the recorded via chain, and gave each new node the specific paragraph of Tag 08W9 that it serves. No unit or chapter file was edited.

The only off-unit proof tool is lem-weil-pbc-finite-presentation-base-change-composition, the generic commutative-algebra base-change statement used on affine etale charts. It is declared in split_report.tool_uses. It replaces no part of the unit route.

## Not duplicates

lem-sfb-space-supported-adic-existence vs prop-weil-pbc-grothendieck-existence: the existing theorem is for schemes; the new input is the algebraic-space theorem, with arbitrary ideal I, non-flat modules, all module maps and the first-support target condition. Scheme Grothendieck existence does not directly imply it.

lem-sfb-space-supported-adic-existence vs lem-sfb-space-flat-proper-support-inverse-effectivity: the existing node concerns existence for flat modules over general surjective locally-nilpotent-kernel towers; it gives neither the non-flat category nor full faithfulness. Conversely, the new theorem assumes a Noetherian ring complete for powers of one ideal. Neither theorem subsumes the other.

lem-sfb-space-adic-flatness-near-closed-fibre vs lem-weil-pbc-noetherian-flat-locus-neighborhood: the existing ring theorem gives openness around an already-flat stalk. It does not infer stalk flatness from every quotient by powers of an ideal. The new node is the formal criterion on algebraic spaces, with no proper-support or completeness assumption, and concludes flatness only near the closed fibre.

lem-sfb-space-adic-flatness-near-closed-fibre vs lem-sfb-space-relative-flat-locus-base-change: the existing statement is about flatness of a morphism between two spaces flat/finite-presentation over another base, and its behavior under base change; it is not the module formal criterion.

lem-sfb-space-complete-local-map-effectivity vs lem-sfb-space-coherent-formal-effectivity: the former is a theorem about B-valued points, with no module or f at all; it does not state a clause of the latter's conclusion about coherent families. It is precisely the first reduction input of the source proof.

lem-sfb-space-supported-adic-existence vs lem-sfb-space-coherent-formal-effectivity: the new theorem is the general non-flat Grothendieck theorem for a fixed space over any complete adic Noetherian ring, not effectivity of the flat-family stack with variable map to B. The item still proves base-map recovery, checks the geometric hypotheses, derives global flatness using proper support, and proves the restriction to invertible arrows.

I searched the whole DAG by the source tags 0AQH, 07X8, 08BE, 08BF and 08VP and the complete-local, compatible-map, proper-support and flat-locus concepts. No existing node states any of the three new inputs. I also ran blueprint_refs.py search for the tags, Grothendieck existence, coherent existence, formal flat and proper support. The few proper-support blueprint results concern cohomology/constructibility, not adic coherent algebraization. Broader adic results concern coefficient complexes, not quasi-coherent modules on algebraic spaces.

## Mathlib search assessment

For each new node I ran leanfinder, leansearch, loogle and grep with that node's statement in mind, using the prescribed msearch.py. The two semantic searches use different formulations. All returned successfully. The exact queries and full printed results are in each node; all are logged in searches.jsonl. The item retains the inherited four searches, including the no-hit complete-adic/module Loogle search.

I read the plausible hits in Mathlib/RingTheory/AdicCompletion/RingHom.lean (IsAdicComplete.liftAlgHom and its compatibility/uniqueness context), AdicCompletion/Algebra.lean, Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean (local finite-presentation definitions), and RingTheory/Flat/Localization.lean (flat_of_isLocalized_maximal and flat_of_localized_maximal). The ring lifting theorem handles affine targets; reaching a general algebraic space needs an etale atlas, finite etale extension and descent as in 0AQH, not a one-line specialization. The module-sheaf definitions do not assert Grothendieck existence. Localization tests and flatness of completions do not give the formal criterion or the open relative flat locus. The grep hits for quotient maps concern topological quotient maps of flat scheme morphisms. Thus none is a Mathlib leaf. No query was invented or recorded without execution.

## Review by Q57

I read quot.tex Situation 08KB and the entire proof of Tag 08W9. For the first new node I read formal-spaces.tex Tag 0AQH (lemma-map-into-algebraic-space), including its inverse-limit formulation and its finite-etale/descent proof, and artin.tex Tag 07X8, Case II. This confirms that the target B need not be separated or finite type and that its base map is uniquely recovered. For the second I read spaces-more-morphisms.tex Tags 08BE and 08BF (theorem-grothendieck-existence and remark-reformulate-existence-theorem), and the finite-presentation/coherent equivalence in spaces-cohomology.tex Tag 07UB (lemma-coherent-Noetherian), plus spaces-morphisms.tex Tag 04ZK (lemma-locally-finite-type-locally-noetherian). On a finite-type space over Noetherian A, the modules called finitely presented in the node are exactly the coherent modules of that theorem. I read spaces-perfect.tex Tag 0CZI (lemma-module-support-proper-over-base): the proper-support condition is exactly the closed-carrier formulation used by the item. These formulation changes add no hypothesis. For the third new node I read spaces-more-morphisms.tex Tag 08VP (lemma-flatness-over-Noetherian-ring), including the opening sentence of the proof that makes the locus open, and again used 04ZK and 07UB to express coherent as finitely presented quasi-coherent. This input asserts flatness only over the inverse image of V(I).

For step 1 I opened lem-sfb-space-complete-local-map-effectivity and verified that its statement gives BOTH existence and uniqueness of b, with exactly the complete/local/Noetherian assumptions available. The specified transition arrows force the maps b_n to agree as maps, rather than only up to an unspecified equivalence. Canonical fibre-product identifications place the modules on one tower without assuming effectivity of the coherent stack.

For step 2 I opened each cited statement. lem-sfb-space-separated-fp-composition explicitly gives arbitrary algebraic-space base-change preservation of separatedness. lem-sfb-space-quasicompact-affine-tests gives arbitrary base-change preservation of quasi-compactness. lem-sfb-space-local-properties-chart-test allows the displayed surjective etale charts and the reverse implication from their chart map. lem-weil-pbc-finite-presentation-base-change-composition(1) states the tensor-product algebra finite-presentation assertion actually used, with an arbitrary base ring map, so no flatness is smuggled in. Finite generation from a finite algebra presentation is elementary. This establishes all the separated/finite-type hypotheses of the existence input and the local finite-presentation hypothesis of the flatness input.

For step 3 the quoted new theorem states an equivalence with ALL module maps for a fixed separated finite-type algebraic space over complete Noetherian A. I checked I=m, the n>=1 indexing, the first-term proper-support condition, and the actual specified transition isomorphisms. It returns a finitely presented module with proper support, which is exactly what the next step needs; flatness is not part of that theorem's statement.

For step 4 I checked that the formal-flatness statement gives an open flat locus containing the entire closed fibre, not global flatness. The other two cited statements give a proper closed carrier and the universally closed property of its structural map. The complementary closed nonflat locus lies in the carrier because the module is zero off it. Its nonempty image would be a nonempty closed subset of Spec A, hence contain m. This contradicts the criterion. This explicit argument supplies the proper-support use that the last line of 08W9 leaves implicit. It uses no false assertion that an open set containing the closed fibre equals Y.

For step 5 I opened lem-sfb-space-module-base-change-flat-proper-support: the statement allows arbitrary T' -> T and only needs local finite type of p, already proved. Its conclusion supplies finite presentation, quasi-coherence, flatness and proper support of every restriction. I then checked the exact statements of both new equivalences again. Injectivity of the point restriction gives emptiness of both arrow sets for distinct base maps. Fullness of module restriction lifts the compatible arrow and its inverse, and faithfulness gives both inverse identities, so the output is really an isomorphism. No inverse-limit exactness assertion is needed.

I checked delivery-errors B through E against the written node files and the source text. The new nodes introduce their rings, ideals, spaces, categories and maps explicitly and have statement-only bodies, no hidden proof dependency lists. Every non-elementary parent input is in uses, and proof_deps is their exact union. citations.json quotes the statements literally; in particular no quotation substitutes for a missing conclusion. All proof steps are shorter than 2000 characters. I checked the three new statements are not elementary, duplicates, or mere restatements of the item's conclusion. The complete proof follows a document, so proof_origin.by is document. The blueprint is only the inherited route context.

Small cases: for A a field, m=0, all three restrictions are constant and the item reduces to the identity equivalence, including the zero module and empty space. For the existence theorem I=0 gives the constant system and I nilpotent gives a tower eventually equal to Y; for I=A, completeness forces A=0. For the flatness criterion I=0 forces F itself to be flat by its hypothesis, while I=A makes the near-V(I) conclusion vacuous. To check why the criterion does not claim global flatness, take A=k[t], I=(t), Y=Spec(A[1/t]) and F=tilde(A[1/t]/(t-1)): all Y_n are empty and all reductions are flat, but F is not A-flat. Its support is the closed point t=1, which is proper over A. Thus this example also checks the need for the parent's LOCAL base: over a nonlocal ring a nonempty closed image can avoid the selected closed subset V(I). In the local complete-base setting, a nonempty closed image avoiding the closed point is impossible. These tests preserve the exact hypotheses used in step 4 rather than assuming completeness alone implies global flatness.

## Source error

Tag 08VP has two typographical slips in its statement: it calls F_n a pullback to X rather than X_n, and says flat over X rather than over S in its last line. Its proof explicitly says flat over S and invokes the module-powers flatness criterion. The new input states the intended, well-typed assertion with F_n on Y_n and flatness relative to Spec A. This is a source wording correction only; the item's imported statement needs no change.

## Unfinished work

No parent proof step remains unfinished. The three new inputs intentionally remain unsplit, as required for a one-level stage-1 split. Their future splits are separate items. This delivery writes no Lean and claims no new completed Lean theorem.

## Validation

The first required deliver.py --no-push run exited successfully: OK (not pushed), preflight passed at e829c814155. The final run is repeated after polishing the wording of the edge-case discussion.
