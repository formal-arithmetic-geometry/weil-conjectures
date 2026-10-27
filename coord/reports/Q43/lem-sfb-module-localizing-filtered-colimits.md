# Q43 stage-1 delivery: lem-sfb-module-localizing-filtered-colimits

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-module-localizing-filtered-colimits.json: item, split into five steps; statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-directed-module-bar-augmentation.json: one new statement-only algebraic lemma, unsplit, no Mathlib match.
- citations.json: one verbatim statement quote for each citation in each numbered step.
- searches.jsonl: actual msearch.py output records; existing item searches retained as well.

## Attachments

None. Searches of WeilConjectures by the item tag, localizing/filtered terminology, and bar/simplicial replacement terminology found no declaration proving the item. The existing module-filtration telescope is a usable dependency, not an attachment for arbitrary directed colimits. No Lean files were written and no compiler was invoked.

## WANTED

None. The proof is explicitly agent-written; it does not pretend that the Stacks exactness-of-colimits lemma states the localizing-subcategory result or the bar lemma. All background documents used are present locally.

## Source and route audit

Read GOAL.md, the stage-1 brief, stages/1-dag.md, SETUP.md's three levels, the worker role, and delivery-errors B--E (both copies). Read the chapter and unit records. Read the CURRENT latest blueprint's sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, especially clause (3). The item is a subsidiary algebra lemma along the inherited alteration/relative-duality/localizing-generation chain; this work neither changes that route nor adds a geometric hypothesis. The latest blueprint has no statement of this bar lemma or of the item. The ancestor command returns None for this existing creation chain; the delivery retains the null ancestor, the chain, and the specific supporting place rather than inventing an imported blueprint ancestor.

The item was unsplit and the sandbox had no previous node, report or search log. No repair-note file exists for it. There is no statement dispute: arbitrary directed posets, arbitrary commutative rings and noninjective transitions are all covered. The source field is retained: Tag 00DB, algebra-lemma-directed-colimit-exact, is background, explicitly not a verbatim source for this corollary. Read algebra.tex at lemma-directed-colimit (00D6), lemma-zero-directed-limit (00D7), and lemma-directed-colimit-exact (00DB). Read derived.tex at lemma-direct-sums (0A5L), lemma-compute-colimit, and lemma-colim-hocolim (0949), and verified the tag/label correspondences in tags/tags. The new node's background source is 00DB; its actual construction and proof below are by Q43.

The generic coproduct and module-filtration telescope citations are tools from other units, declared in split_report.tool_uses. The unit does not supply either universal property. The ring-module Grothendieck fact and cone comparison are existing Mathlib leaves. No SGA source is used.

## Independent proof retained for the new node

Write a generator of B_n as [i_0,...,i_n;x], linear in x. All chains are weakly increasing, so repeated vertices, including the eventual appended endpoint, are allowed. The face operators satisfy d_a d_b = d_{b-1} d_a for a < b. When both operations involve the first vertex this is u_jk u_ij = u_ik; in every other case it is deletion of the same vertices with the same unchanged coefficient or the same single transition. Terms therefore cancel in pairs in the square of the alternating boundary. Compatibility q_j u_ij = q_i gives epsilon partial_1 = 0. This proves that all the displayed data are actual differentials and an augmentation, independently of any claimed exactness.

Fix k and restrict to chains all of whose vertices are at most k, retaining the coefficients M_{i_0}. Augment this subcomplex to M_k by alpha_k([i;x]) = u_ik(x). There is an augmented contraction

h_n([i_0,...,i_n;x]) = (-1)^(n+1)[i_0,...,i_n,k;x]  (n >= 0),
h_{-1}(x) = [k;x].

Indeed partial_{n+1} h_n + h_{n-1} partial_n = 1. For n >= 1 the terms deleting one of the old vertices cancel, leaving the last-face term with sign (-1)^(n+1) times (-1)^(n+1) = 1. For n = 0 the equation is partial_1 h_0([i;x]) = [i;x] - [k;u_ik(x)], and h_{-1} alpha_k supplies the missing term. Also alpha_k h_{-1} = 1. These identities use no inverse or injection for any u_ij.

A positive-degree cycle z has finite support in the direct sum. The finitely many vertices of its supporting chains have a common upper bound k, obtained by induction from binary directedness (the empty support is the zero cycle). Regard z in the subcomplex bounded by k. Its boundary is still zero, since that subcomplex includes into the full complex by a summand inclusion in each degree. The contraction yields z = partial h_n(z). Thus all positive chain homology vanishes.

For z in B_0 with epsilon(z) = 0, choose an upper bound k for its finite support. Set y = alpha_k(z) in M_k. Its image q_k(y) is zero. Stacks 00D6/00D7 identify the directed module colimit elementwise and give l >= k with u_kl(y) = 0, without monic transition maps. Now alpha_l(z) = 0, and the degree-zero contraction with endpoint l gives z = partial_1 h_0(z). Finally every element of M is q_i(x) for some i,x by 00D6, and is therefore epsilon([i;x]). This proves exactness including surjectivity. Reindexing B_n as B^{-n} proves that the given chain augmentation is a quasi-isomorphism to M[0]. This proof is retained here as source material for the next split; the new node itself has no proof or proof dependencies.

## Review by Q43

I checked every cited node's statement, rather than using a construction hidden in its proof. Step 1 uses exactly the new bar-augmentation statement: its poset, transition identities, all-chain sums, and quasi-isomorphism match the given system. Its module direct sums exist in the common universe. The augmentation proof above treats finite supports in an arbitrary directed set, not just a cofinal sequence.

Step 2 uses lem-weil-pbc-ring-modules-grothendieck-abelian for its explicit assertion that Mod(R) is Grothendieck abelian, then lem-kun-grothendieck-derived-coproducts for the image of the specified termwise coproduct, including its coprojections. I opened both node statements. The latter assumes a Grothendieck category and arbitrary small families, precisely supplied here. Applying it to degree-zero complexes gives the degree-zero direct sum of the original modules. This step does not replace arbitrary I by the natural numbers.

Step 3 uses lem-pc-cone-short-exact-quasi-iso for its explicit canonical map from a cone to the quotient complex in a short exact sequence, and def-weil-abstract-derived-category for inversion of quasi-isomorphisms and the distinguished cone triangle. The split short exact sequence is written out: the inclusion is of the higher-degree brutal tail, and its quotient is B_n in degree -n. This checks the direction of the inclusion, the sign/shift convention B_n[n], and the induction base F_0. No claim that cohomology truncations are subcomplexes is made. The induction uses only the given closure under triangles and shifts. The source is Stacks 0152; the existing cone lemma states exactly the required quotient comparison.

Step 4 uses lem-pc-derived-module-filtration-telescope. I read its full statement and its project declaration/docstring, which explicitly supplies a colimiting cofan and a triangle with Q(L) as the third term. Its hypotheses are commutative R, actual complexes, monomorphisms into the one ambient complex, compatible inclusions, and degreewise exhaustion. Each holds for the explicitly defined F_n. In particular, F_n -> B is monic even though the original u_ij need not be. The telescope index ULift N is a set in the module universe. The two coproduct terms belong to the subcategory, so closure under distinguished triangles applies. This is a generic tool; it is not confused with an ordinary categorical colimit in D(R).

Step 5 uses exactly the localization and isomorphism inversion in def-weil-abstract-derived-category, followed by the subcategory's assumed isomorphism closure. It is elementary after the preceding steps. I stored full verbatim statements for every uses entry in citations.json, so every quote includes the hypotheses checked above. The proof_deps list is exactly the union of uses. Each non-elementary step is under 2000 characters; none hides another comparison lemma. The finite-complex induction is a direct application of the cited cone comparison to the written split sequence, not a separate new lemma.

I checked the new algebraic statement on the singleton poset (the unnormalized alternating identity/zero complex), the zero ring and zero modules, a two-object ordered set, noninjective transitions such as Z -> Z/2, and a constant system on a directed set with no countable cofinal subset. Repeated vertices are necessary for the displayed contraction and are explicitly allowed. Finite support, rather than countability of I, is the only finiteness used in exactness. The empty poset is excluded by the statement. No Noetherian, flatness, projectivity or transition injectivity hypothesis enters. The original item needs no correction.

Against delivery-errors B--E: the new node introduces all data and differentials and carries only a statement; its complex, colimit and quasi-isomorphism terminology cites the exact definitions. The source names a verified tag and label while distinguishing the agent lemma from that tag. All recorded Mathlib searches were actually run using msearch.py and their results read. The generic left-resolution and group bar constructions in the search hits are different complexes; neither identifies the diagram-specific complex in one line. The coproduct and telescope steps are reused, so the new node neither restates the item nor takes all of its content. The dependency direction runs from the item to a purely algebraic lemma with only definition dependencies, so it cannot cycle back. There is no change of coefficient category or unproved naturality assertion.

## Mathlib and duplicate searches

For the item, kept the inherited searches and added two new semantic phrasings, Loogle, source grep and LeanSearch, all in searches.jsonl. For the new node, two semantic phrasings, Loogle, LeanSearch, and two source greps were run. Read the returned types and the relevant source passages: LeftResolution/Basic.lean, RepresentationTheory/Homological/Resolution.lean, Algebra/Homology/GrothendieckAbelian.lean, and CategoryTheory/Triangulated/LocalizingSubcategory.lean. In particular, Verdier relative-localizing predicates do not mean closure under coproducts. There is no match for either statement.

Searched the entire DAG by tags and statement concepts, the project Lean roots, and blueprint_refs.py by 'localizing', 'bar resolution', 'simplicial replacement', 'homotopy colimit', 'directed bar', 00DB, and 00D6. Generic space/model-category bar resolutions have different coefficient objects and weak-equivalence hypotheses; the existing group bar resolution concerns Z[G] and group actions. Neither directly supplies this R-module resolution of a directed diagram. The existing filtered module elementwise lemma gives the eventual-vanishing input used in the retained proof above, not the bar differential or its higher exactness.

## Not duplicates

lem-sfb-directed-module-bar-augmentation vs lem-sc-sequential-colimit-derived-homology-representative: the existing statement represents H^0 classes at a sequential stage; the new lemma instead constructs a directed bar complex and asserts all-degree augmented exactness.

lem-sfb-directed-module-bar-augmentation vs lem-sc-filtered-module-complex-homology-zero: the existing statement detects eventual vanishing of a sequential homology class; the new lemma states exactness of an explicitly constructed all-chain complex for an arbitrary directed poset.

lem-sfb-directed-module-bar-augmentation vs lem-sfb-module-localizing-filtered-colimits: the item asserts localizing-subcategory membership in D(R); the new lemma constructs and proves exact a specific algebraic bar augmentation, and has no subcategory at all. Membership still requires the independent finite-subcomplex and telescope argument.

lem-sfb-directed-module-bar-augmentation vs lem-weil-pbc-filtered-colimit-abelian-groups-exact: the existing statement preserves exact sequences of abelian groups under filtered colimits; it does not construct or resolve the colimit by the directed bar complex of R-modules.

lem-sfb-directed-module-bar-augmentation vs lem-weil-pbc-colimit-rings-flat: the existing statement detects flatness of a ring map from colimit stages; it neither constructs the bar differential nor states augmented exactness.

lem-sfb-directed-module-bar-augmentation vs lem-weil-pbc-ring-modules-grothendieck-abelian: the existing statement gives AB5 and a generator for Mod(R), reused in step 2; it does not state exactness of the particular chain-indexed bar augmentation.

lem-sfb-directed-module-bar-augmentation vs lem-weil-pbc-polynomial-local-weak-regular-sequence-descent: the existing statement concerns weak regularity in localized polynomial rings after directed descent, not a bar augmentation of an arbitrary module diagram.

lem-sfb-directed-module-bar-augmentation vs lem-weil-pbc-directed-union-subrings-flat-module: the existing statement proves flatness across a directed union of subrings, whereas the new statement has one fixed ring and resolves an arbitrary diagram of its modules.

lem-sfb-directed-module-bar-augmentation vs lem-weil-pbc-relative-global-complete-intersection-local-regular-sequence: the existing statement is a local regular-sequence result for complete intersections, not an exact augmented chain complex of a module diagram.

lem-sfb-directed-module-bar-augmentation vs lem-weil-pbc-finite-filtered-colimit-comparison: the existing statement is an isomorphism criterion via finite filtrations of abelian groups; no explicit bar differential or augmented resolution occurs.

lem-sfb-directed-module-bar-augmentation vs lem-sc-compact-cech-cohomology-coproduct: the existing statement preserves coproducts in finite-cover Cech cohomology of sheaves; the new lemma has no site, covering or Cech nerve and uses chains of a directed poset.

lem-sfb-directed-module-bar-augmentation vs lem-weil-pbc-directed-colimit-homology: the existing statement says abelian-group homology preserves directed colimits of supplied complexes; it does not construct or prove exactness of the directed module bar complex.

lem-sfb-directed-module-bar-augmentation vs lem-weil-pbc-finite-filtered-colimit-model: the existing statement constructs a finite filtration on a colimit of abelian groups; the new statement specifies an unbounded-to-the-left augmented module resolution.

lem-sfb-directed-module-bar-augmentation vs lem-weil-pbc-spectral-sequence-finite-page-comparison: the existing statement compares finite spectral-sequence pages under directed colimits; the new lemma contains no spectral sequence and instead resolves the module colimit explicitly.

## Unfinished work

None within this one-level stage-1 split. The one new algebraic node is intentionally statement-only for its own later split. The item and every cited hypothesis have been checked; dry-run and delivery results are recorded by the delivery tool.
