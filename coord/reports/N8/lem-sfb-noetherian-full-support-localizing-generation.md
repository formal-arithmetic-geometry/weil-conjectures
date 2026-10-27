# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-noetherian-full-support-localizing-generation.json`: item, statement, split into seven proof steps; no exact Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-module-localizing-filtered-colimits.json`: one new statement-only supporting lemma; unsplit, no Mathlib match, zero Mathlib leaves.
- `citations.json`: complete verbatim statement for every dependency actually cited in every item step.

## Attachments

None. Read-only searches of `lean/WeilConjectures/` for the exact blueprint tag and localizing/localising/full-support terminology gave no declaration stating this item. The ordinary-module free-generation source theorem is already represented by `lem-pc-derived-module-free-generation`; it is an input, not an attachment of full-support generation. No Lean was written, no compiler or Lake command was run, and no git command was run in the shared repository.

## WANTED

None. Both algebra.tex and more-algebra.tex are available locally. This corollary and its additional filtered-colimit lemma have agent-written proofs, identified as such; the named Stacks tags are supporting inputs, not assertions that Stacks states either corollary verbatim.

## Problems found and corrections

The original item is true, including the zero ring, and its statement and statement dependencies are retained. No STATEMENT-DISPUTED correction is needed. Its source suggests residue-field extraction followed by Noetherian induction, but did not provide that argument in the node. I supplied it in the proof steps. I did not assume E perfect or that its residue-field tensor has bounded cohomology: this tensor may have infinitely many negative cohomology groups. The field splitting input explicitly covers arbitrary complexes, so a single shifted copy of the residue field is still a retract.

During self-review I replaced an unnecessarily complicated transitivity instantiation with the actual extension-of-scalars comparison explicitly stated in clause (2) of `lem-pc-derived-tensor-transitivity`. I removed the now unused restriction-K-flat citation. I also used the existing prime-filtration node instead of creating a new support-filtration lemma. Annihilator containment of its factors is proved in the item steps directly; the support equality of Tag 00L4 is unnecessary.

## Sources and blueprint route

Read the chapter record `dag/chapters/sec-six-functors-basics.json`, unit record `dag/units/sk-thm-sf-ctf-stability.json`, SETUP's three levels, and the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and direct-images and unit proof files. The latest direct-images proof (3) is the ancestor route named by this item's existing prerequisite chain. Full-support generator normalization is a generic affine algebra prerequisite below that route, and does not change a unit or chapter statement or use an SGA source. The existing ancestor lookup prints `None`, so the new node preserves that null nearest ancestor and prepends this item to its existing via chain; no ancestor is fabricated.

Read Stacks algebra.tex, Tag 00L0, label lemma-filter-Noetherian-module, including its maximal-counterexample proof, and Tag 00L4, label lemma-filter-primes-in-support. The former is the exact finite prime-filtration theorem used in steps 5 and 6; the latter is not needed. Read more-algebra.tex, Tag 09PB, label remark-P-resolution, in particular its free resolution filtration, telescope triangle, and the stated three-property generation criterion. This supplies the existing free-generation input used in step 2. Read algebra.tex, Tag 00DB, label lemma-directed-colimit-exact, its statement and elementwise proof; this supplies the exact-colimit background for the new lemma. The remaining non-elementary facts are the existing nodes whose statements are quoted in citations.json, rather than uncited imports from these source proofs.

## Independent proof of the new supporting node

Let I be the small directed poset in the new node. Form the augmented bar complex C of the module system, with

\[
 C^{-n}=\bigoplus_{i_0\le\cdots\le i_n}M_{i_0}\quad(n\ge0),\qquad C^j=0\quad(j>0),
\]

and augmentation C^0 to colim M_i. On a labelled element x the first face removes i_0 and applies u_(i_0,i_1); each other face removes the corresponding index and leaves x unchanged. The differential is the alternating sum of the faces. The simplicial identities, checked by removing two indices, give d^2=0. Repetitions of indices are permitted, so adjoining a largest vertex is always defined.

This augmentation is a quasi-isomorphism. A positive homological-degree cycle has finite support in these direct sums. Choose one upper bound r for every index in that support. On its chains append r; the alternating face calculation gives a contracting homotopy on positive-degree cycles (the last face is the original chain, and all other faces cancel with the appended boundary). In degree zero, a finite tuple with augmentation zero can be moved along the relations to its sum in a single common upper stage r. The elementwise criterion for zero in the directed colimit gives a later stage t in which this sum is zero. Applying the same appended-vertex calculation with t expresses the tuple as a boundary. Surjectivity of the augmentation follows because every colimit element has a stage representative. Thus H^0(C) is colim M_i and all other cohomology vanishes. This is an actual module bar calculation, and does not assume that an arbitrary coproduct-closed subcategory is already closed under arbitrary triangulated-category colimits.

Each C^{-n}[0] belongs to L by coproduct closure and the hypotheses on M_i. Each brutal truncation C_(>=-n) has finitely many nonzero terms, hence is built by finite cones and shifts of those terms, so belongs to L. These truncations embed as subcomplexes and exhaust C. Their sequential mapping telescope is isomorphic in D(R) to C: the degreewise sequence from direct sum of truncations, by 1-shift, to the same direct sum, and then to their union is short exact. Injectivity follows recursively from its component zero, and the cokernel is the union by moving a finite tuple to one upper stage. This is exactly the mechanism of existing `lem-pc-derived-module-filtration-telescope`, with derived coproducts computed termwise by `lem-pc-derived-module-direct-sums`. Consequently C belongs to L; its augmentation gives (colim M_i)[0] in L. This proof uses no Noetherian condition and allows arbitrary transition kernels. It is longer than two or three elementary lines and genuinely supplies a reusable homological-algebra input, rather than restating a clause of full-support generation. The node itself remains statement-only as required.

## Searches and reuse

Before creating the one new node I searched the whole DAG's statements and titles for localizing/localising, filtered colimit, derived module, residue-field generation, prime filtration, and the tags 00L0, 00L4, 09PB, 00DB. I ran `tools/blueprint_refs.py search` on localizing, localizing subcategory, localizing module, filtered, filtered colimit, filtered colimits of modules, directed colimits, filtration, and Nakayama; I also searched the entire latest blueprint directly. No blueprint statement duplicates directed-module-colimit closure. Exact-tag and concept searches in project Lean found free generation and the existing sequential telescope, not this arbitrary directed-system closure theorem. The small-index hypothesis is explicit in the new node and its application.

All new-node Mathlib queries were run through msearch.py, with their exact text, results and digests preserved in searches.jsonl. Two semantic phrasings each were used for the item and for the new lemma, as well as LeanSearch, Loogle, and grep. The printed results were read. The derived-category IsGE/IsLE/truncation results do not give localizing generation. ModuleCat.FilteredColimits.colimit constructs a module colimit but does not assert membership in a localizing derived subcategory. The presentability/orthogonal-reflection hit assumes cardinal-presentable testing maps and is not the closure result here. I read Mathlib/CategoryTheory/Triangulated/LocalizingSubcategory.lean: its Verdier relative-localizing predicates concern factorization between two subcategories, not closure under coproducts. I also read ModuleCat/FilteredColimits.lean, and narrowed grep to Algebra/Homology and CategoryTheory/Triangulated so that unrelated probability-theory localizing sequences could not hide a relevant result. None is an exact or one-line-specialization match.

The existing prime-filtration node is already a Mathlib leaf. Existing ordinary-module exact tensor, free generation, local derived-tensor nonvanishing, field-complex splitting, derived scalar comparison, direct sums, and complex-SES triangle nodes are reused. These external-unit results are generic tools rather than replacements for the unit's proof route; the non-Mathlib tool citations are declared in split_report.tool_uses. Traversing each of their dependency closures found no path to the item, excluding a newly introduced cycle.

## Not duplicates

lem-sfb-module-localizing-filtered-colimits vs lem-sc-sequential-colimit-derived-homology-representative: the new node asserts membership of an arbitrary directed module colimit in every coproduct-closed triangulated subcategory of D(R); the existing node states “Sequential colimit derived cohomology has finite-stage representatives”, which does not assert that closure.

lem-sfb-module-localizing-filtered-colimits vs lem-sc-filtered-module-complex-homology-zero: the new node asserts membership of an arbitrary directed module colimit in every coproduct-closed triangulated subcategory of D(R); the existing node states “A class zero in filtered complex homology vanishes at a later stage”, which does not assert that closure.

lem-sfb-module-localizing-filtered-colimits vs lem-weil-pbc-filtered-colimit-abelian-groups-exact: the new node asserts membership of an arbitrary directed module colimit in every coproduct-closed triangulated subcategory of D(R); the existing node states “Filtered colimits of abelian groups are exact”, which does not assert that closure.

lem-sfb-module-localizing-filtered-colimits vs lem-weil-pbc-colimit-rings-flat: the new node asserts membership of an arbitrary directed module colimit in every coproduct-closed triangulated subcategory of D(R); the existing node states “Flatness over a filtered colimit of rings”, which does not assert that closure.

lem-sfb-module-localizing-filtered-colimits vs lem-weil-pbc-ring-modules-grothendieck-abelian: the new node asserts membership of an arbitrary directed module colimit in every coproduct-closed triangulated subcategory of D(R); the existing node states “The category of modules over a ring is Grothendieck abelian”, which does not assert that closure.

lem-sfb-module-localizing-filtered-colimits vs lem-weil-pbc-polynomial-local-weak-regular-sequence-descent: the new node asserts membership of an arbitrary directed module colimit in every coproduct-closed triangulated subcategory of D(R); the existing node states “Weak regularity descends from finite coefficient-subring polynomial localizations”, which does not assert that closure.

lem-sfb-module-localizing-filtered-colimits vs lem-weil-pbc-directed-union-subrings-flat-module: the new node asserts membership of an arbitrary directed module colimit in every coproduct-closed triangulated subcategory of D(R); the existing node states “A module that is the directed union of flat modules over directed subrings is flat”, which does not assert that closure.

lem-sfb-module-localizing-filtered-colimits vs lem-weil-pbc-relative-global-complete-intersection-local-regular-sequence: the new node asserts membership of an arbitrary directed module colimit in every coproduct-closed triangulated subcategory of D(R); the existing node states “The equations of a relative global complete intersection form a regular sequence at every prime”, which does not assert that closure.

lem-sfb-module-localizing-filtered-colimits vs lem-weil-pbc-finite-filtered-colimit-comparison: the new node asserts membership of an arbitrary directed module colimit in every coproduct-closed triangulated subcategory of D(R); the existing node states “Finite filtered-colimit comparison from graded models”, which does not assert that closure.

lem-sfb-module-localizing-filtered-colimits vs lem-sc-compact-cech-cohomology-coproduct: the new node asserts membership of an arbitrary directed module colimit in every coproduct-closed triangulated subcategory of D(R); the existing node states “Finite compact Cech cohomology preserves existing coproducts”, which does not assert that closure.

lem-sfb-module-localizing-filtered-colimits vs lem-weil-pbc-directed-colimit-homology: the new node asserts membership of an arbitrary directed module colimit in every coproduct-closed triangulated subcategory of D(R); the existing node states “Homology of abelian-group complexes preserves directed colimits”, which does not assert that closure.

lem-sfb-module-localizing-filtered-colimits vs lem-weil-pbc-finite-filtered-colimit-model: the new node asserts membership of an arbitrary directed module colimit in every coproduct-closed triangulated subcategory of D(R); the existing node states “Finite colimit filtration with compatible graded colimit isomorphisms”, which does not assert that closure.

lem-sfb-module-localizing-filtered-colimits vs lem-weil-pbc-spectral-sequence-finite-page-comparison: the new node asserts membership of an arbitrary directed module colimit in every coproduct-closed triangulated subcategory of D(R); the existing node states “Filtered-colimit comparison on every finite spectral-sequence page”, which does not assert that closure.

## Review by N8

I read the item statement against its source intent, preserving bounded finite cohomology, every prime localization nonzero, the ordinary unbounded module category, no finite homological-dimension assumption, and B=0. I read the new node against 00DB and the independent bar proof above: 00DB alone asserts exactness, and I have explicitly supplied the missing passage from exact directed colimits to localizing membership. The two sequential homology nodes with the same tag do not suffice for an uncountable directed set. The new lemma is self-contained, has empty proof/proof_deps, states the index size and directedness explicitly, and has the actual three kinds of search recorded.

In step 1 the empty coproduct is exactly zero, which handles the zero ring without choosing a prime. In step 2 I checked the statements of `lem-pc-derived-tensor-second-factor-functor`, `def-pc-module-kflat-complex`, `lem-pc-derived-module-direct-sums` and `lem-pc-derived-module-free-generation`: they respectively give exact derived tensor on K-flat inputs, its quasi-isomorphism criterion, the actual derived coproduct, and generation for every module-derived object. The sum argument is written out; thus tensor ideal closure is deduced here, not assumed as a property of arbitrary triangulated subcategories.

In step 3 I opened `def-weil-pbc-localization-at-prime`, `def-weil-pbc-noetherian-ring`, `lem-weil-pbc-localization-module-exact`, `lem-weil-pbc-localization-flat`, `lem-trf-local-derived-tensor-nonvanishing`, and `lem-pc-derived-tensor-transitivity`. The local-ring definition supplies exactly the local ring and residue field; the contraction argument supplies its Noetherian property. Exact localization supplies finite localized cohomology. The nonvanishing node requires two nonzero bounded-above finite-cohomology complexes over a Noetherian local ring: E_p and k meet precisely those assumptions. Its tensor need not be bounded below. The scalar comparison used is explicitly in clause (2) of the transitivity node, with A=B and C=B_p, as stated in the step. This corrected the earlier overcomplicated instantiation before delivery.

In step 4 I opened `lem-trf-field-complex-cohomology-splitting`. Its first paragraph applies to any complex, so the residue-field tensor's potentially unbounded negative tail is allowed. Selecting one cohomology basis vector gives the inclusion and projection of a line directly; no unsupported perfectness claim or bounded idempotent-splitting clause is used. Restriction of scalar-linear chain maps and their homotopies preserves the equations, so this really is a retract in D(B).

In step 5 I opened the prime-filtration and complex-SES triangle nodes. The first states finite modules over Noetherian rings have quotients exactly B/q, and B/J is cyclic and finite; the second gives exactly the triangles of the degree-zero short exact filtration sequences. Annihilators pass to subquotients directly. If J is nonprime, every occurring prime is strictly larger. The induction uses ascending ideals, not a finite dimension bound; the Noetherian hypothesis justifies the maximal counterexample. In step 6 the same two statements are used only on finite submodules of C, and I checked that the product of their finitely many denominators lies outside p. Hence every filtration prime strictly contains p. The new directed-colimit node applies to the small set of finite submodules, which contains zero and has binary upper bounds; its colimit is the ordinary union C. No theorem about only sequential colimits is substituted for this input.

In step 7 I re-read `lem-weil-pbc-complex-ses-triangle`: it gives the triangle from the actual injection B/p to its fraction field and quotient C. Its rotation uses only the defining triangle/shift closure of L. The middle term came from step 4, not from an unproved induction hypothesis, so the induction is not circular. The resulting contradiction proves all B/J, and J=0 gives B itself.

For small cases I checked B=0 separately, B a field (the residue argument reduces to a nonzero vector-space cohomology line), B a nonreduced Artinian local ring such as k[epsilon]/epsilon^2 (a residue-field object need not be perfect and is still allowed), and B=Z with p=(0) (C=Q/Z is an infinite union of finitely generated torsion submodules). The new lemma allows I with one object, constant zero systems, noninjective maps such as the zero maps in a sequential system, and directed sets with no countable cofinal subset. The bar proof covers each; the main proof only needs the inclusion-system case. I checked B1-B10, C1-C8, D1-D5, E1-E7 against the final node files. Every non-elementary step has its exact cited statement in citations.json, no new node is a clause or restatement of the item, and all steps are shorter than 2000 characters. No source error, unresolved hypothesis, or remaining mathematical task in this one-level split was found.

## Unfinished work

None in the requested one-level split. The single supporting node is intentionally unsplit and joins the later queue. Maintainer review remains independent.
