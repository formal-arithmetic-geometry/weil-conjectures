# Stage-1 delivery: lem-sfb-pseudocoherent-algebra-scalar-restriction

## Files written
- dag/nodes/sec-six-functors-basics/lem-sfb-pseudocoherent-algebra-scalar-restriction.json: item, statement unchanged, six proof steps; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-pseudocoherent-terms-bounded-above.json: new statement, Tag 064Y, unsplit; no Mathlib match.
- citations.json: exact statement quotations for every use in each proof step.
- searches.jsonl: actual msearch records; existing item search history retained in its JSON.
- report.md: this signed review.

## Attachments
None. Searched WeilConjectures for the item tag and the notion, and searched the project library for pseudo-coherence with restriction/scalar keywords. The only relevant restriction/localization result is localization-specific and does not state this general change-of-rings theorem. Project sorry declarations were not treated as finished proofs.

## WANTED
None. All mathematical sources used are present in literature/stacks-project/more-algebra.tex.

## Corrections and scope
The statement of Tag 064Z is correct as imported: no flatness, surjectivity or Noetherian condition is needed. No statement was changed. The source gives the stronger fixed-m result; this item only asks for pseudo-coherence. For the converse I reuse the existing Tag 064U finite-cone construction, instead of introducing a new copy of either implication of Tag 064Z. This is an agent assembly from the cited source results, marked proof_origin.by = agent. The forward implication is the bounded-above finite-free model argument of Tag 064Z and Tag 064Y.

The inherited blueprint ancestry is broken: tools/blueprint_refs.py ancestor returns None. The item already carries from.node = null; retain that, its recorded place and its via chain. Read the newest blueprint at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/, including _section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. This is a supporting commutative-algebra prerequisite in the inherited proper/direct-image dualizing chain, not a replacement of its geometric route. No unit or chapter file changed.

## Not duplicates
No existing node source carries Tag 064Y, as checked by whole-DAG searches for the tag and lemma-complex-pseudo-coherent-modules. The broader keyword searches were also read. In particular, lem-sfb-pseudocoherent-terms-bounded-above vs lem-sfb-pseudocoherent-algebra-scalar-restriction: the new lemma concerns a single ring and arbitrary pseudo-coherent terms, and states neither change-of-rings implication. lem-sfb-pseudocoherent-terms-bounded-above vs lem-sfb-finite-free-algebra-pseudocoherent-resolution: the latter concerns a finite-free algebra and lifting a scalar-restricted object; it does not assert closure under arbitrary bounded-above complexes of pseudo-coherent modules. lem-sfb-pseudocoherent-terms-bounded-above vs lem-pc-ring-pseudo-coherent-distinguished-triangle: the latter is a finite-cutoff triangle theorem, not bounded-above termwise pseudo-coherence. The new lemma is not a two-line consequence: its source truncates at each cutoff, inducts through the bounded complex using cone closure, then applies all-m pseudo-coherence. That argument belongs to its future split.

Whole-blueprint searches with blueprint_refs.py for pseudo-coherent, complex pseudo, 064Y, pseudo and restriction scalar produced no equivalent statement (the lone pseudo hit is a categorical pseudocolimit). Grep of the latest blueprint likewise found no equivalent ring-complex assertion. No duplicate was created.

## Mathlib review
All new searches were run using the required msearch.py; the log records the exact query texts. For each statement semantic search, Loogle and Mathlib grep were run, with a second semantic phrasing. The whole Mathlib grep pseudo.?coher|pseudoCoherent returned no hits. Loogle returned no hits. Read the semantic hits: scalar-restriction pseudofunctors define functors, not the finiteness equivalence (Pseudofunctor.lean:38,49); formally-unramified projectivity assumes an essentially finite type formally unramified algebra (Unramified/Finite.lean:279), absent here; general projective resolutions (Projective/Resolution.lean:341) impose no finite generation on their terms; K-projectivity of bounded-above projective complexes (KProjective.lean:113) proves a lifting property, not existence of a finite-free model. None is an exact match or a one-line specialization. No unavailable search was counted as no match.

## Review by Q42
I read Tag 064Z, lemma-finite-push-pseudo-coherent, in more-algebra.tex, including both implications. I also read Tag 064Y, lemma-complex-pseudo-coherent-modules, for the sole new node, and Tags 064Q, 064R, 064S and 064U for the reused algebra facts. The new node states exactly the final pseudo-coherent assertion of 064Y, introduces its ring, complex and strict upper bound, cites both definition nodes, and has no proof or proof dependencies.

For step 1 I opened def-pc-ring-pseudo-coherent-complex: it supplies precisely a bounded-above finite-free model, so its finite direct sums prove pseudo-coherence of each finite-free T-module after restriction. The rest of this step is the explicit kernel/image/cohomology and signed cone formula; it requires no flatness or additional lemma. It includes rank zero.

For step 2 I checked that the new 064Y statement applies over S to the strictly bounded-above complex obtained by restricting a finite-free T-model. Its term hypotheses are proved in step 1, not borrowed from the source of the cited node. The definition node supplies the model, and restriction preserves its quasi-isomorphism.

For step 3 the definition node gives cohomological boundedness over S, hence over T since the additive groups are identical. The tests are genuinely all bounded finite-free T-complexes F and all chain maps F to C, with arbitrary top cutoff n. Each restricted term is pseudo-coherent by step 1 and 064Y applies to this bounded complex. No claim that C has finite terms or that its actual terms vanish above b is used.

For step 4 I opened lem-pc-ring-pseudo-coherent-iff-all-m and lem-pc-ring-pseudo-coherent-distinguished-triangle and checked their statements. The first gives all integer cutoffs, hence m+1 for the first object and m for the second. The first clause of the triangle node gives m for the cone. Repeating for every m gives precisely pseudo-coherence of the restricted cone. Restriction gives the actual cone triangle by step 1. No statement about finite generation of arbitrary lower cohomology is inferred.

For step 5 I opened lem-sc-finite-cohomology: its exact hypotheses are n-pseudo-coherence and vanishing strictly above n, both established here. It concludes only finite generation of H^n, exactly what is needed. The displayed coefficient expression proves that finite S-generation implies finite T-generation, without requiring f to be surjective. This is the elementary final step, not an unstated flatness theorem.

For step 6 I opened lem-pc-ring-finite-cone-free-model and checked every quantified hypothesis: one ambient universe, cohomological upper bound b on C, and finite top cohomology for every specified cone. Its conclusion is a chain-level quasi-isomorphism from a finite-free complex strictly bounded above by b, exactly the definition of pseudo-coherence. The criterion is not assumed over S and is not applied to only a chosen collection of cones. This avoids hiding a new inductive construction inside the item.

I checked delivery-errors B through E: new statements are self-contained, source tags/labels are correct, no new node merely restates an implication, no unsplit node contains a proof, every non-elementary input is a cited statement, and citations.json quotes those statements literally. Every proof step is shorter than 2000 characters and the whole assembly is below 3000 characters. Generic tools from the Picard unit are declared in split_report.tool_uses, with reasons; they do not change the unit route. The dependency traversal has no path from those tools back to this item (server check still required).

Small cases: the zero ring and zero algebra give zero modules and rank-zero witnesses; identity S=T gives a tautological equivalence; S=Z, T=Z/2 tests a non-flat map with a finite-free S-resolution, and the argument never tensors a quasi-isomorphism along it. An acyclic or arbitrarily shifted C is handled by any cohomological upper bound b; the finite-cone criterion needs no nonzero top cohomology. For 064Y a single nonzero term gives its shift; the zero complex is included; no uniform projective-dimension bound on all terms is imposed. Removing bounded-above would be false, e.g. a field in every degree with zero differential, so that hypothesis is explicit.

## Unfinished work
Only the new 064Y supporting node remains unsplit, as required for one-level stage 1. No Lean was written or compiled, no git command was run in the shared repository, and all writes are inside the assigned sandbox. Required dry run and delivery are performed by the prescribed launcher tool.
