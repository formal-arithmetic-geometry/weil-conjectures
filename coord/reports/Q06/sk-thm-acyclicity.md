# Worker report: sk-thm-acyclicity

## Files written

- `dag/nodes/sec-proper-base-change/sk-thm-acyclicity.json`: statement, split; Mathlib searches do not give either the complete two-clause statement or a one-line specialization. Preserved the statement verbatim, filled its notion dependencies and blueprint search result, replaced the imported proof with nine explicit steps, and declared three generic tool uses.
- `dag/units/sk-thm-acyclicity.json`: only `realized` and `realized_by`, binding the statement and the unit's dimension-shifting step to this item.
- No new nodes; no new Mathlib leaves. `citations.json` gives one verbatim quotation for every step/node pair. `searches.jsonl` retains the actual search records.

## Attachments

No full attachment. `CategoryTheory.Functor.nonempty_rightDerivedObjIso_homology_of_acyclic`, in `lean/WeilConjectures/CategoryTheory/Abelian/RightDerived/Acyclic.lean:305`, proves the nonnegative resolution clause with the stated hypotheses. Its body contains no sorry, but it does not state the canonical total-derived comparison for an arbitrary bounded below complex, and therefore does not cover the item. The same file supplies `Functor.quasiIso_map_of_rightAcyclic`, but that is a statement about quasi-isomorphisms of complexes, not the canonical comparison in the second clause. I did not report either as a complete attachment or infer a transitive sorry audit from the source alone.

## WANTED

None. All mathematical sources used are available locally.

## Corrections to the imported work

The imported statement is correct and unchanged. Its proof did not cite nodes for long exact sequences, injective replacement, injective vanishing, the cone criterion, or computation of the total derived functor on injectives. Its first two steps had `elementary: null`. The citation of `sk-thm-groth-ss` contradicted the text's explicit explanation that no spectral sequence was used: it was an explanatory pointer, and has been removed as a proof dependency. There is no statement dispute and no departure from the unit route.

The main-20261015 statement adds the derived-category clause to the older unit record's resolution criterion. Steps 1–3 realize that record's single dimension-shifting step exactly. Steps 4–9 expand the imported proof's cone argument for the additional clause. The origin remains `agent`: the unit and imported proof are agent-written. Stacks supplies and verifies the individual facts, and its 05TA proof uses precisely the same cycle-induction and acyclic-cone argument; I do not claim that this proof follows the different stupid-truncation proof of 015E verbatim.

## Existing-node and Mathlib searches

I searched the whole DAG by titles/statements for acyclic objects, derived functors, long exact sequences, injective resolutions, and mapping cones, and read the statements of the nodes ultimately used. Blueprint searches ran for `acyclic`, `derived functor`, `acyclic resolutions`, `Leray acyclicity`, `injective resolution`, and `mapping cone`, as well as `ancestor sk-thm-acyclicity`. No new node is needed. `lemma-weil-pbc-leray-acyclicity` overlaps the resolution clause, but its complex clause imposes Grothendieck hypotheses and states cohomology comparisons, so it does not state the full item with its weaker hypotheses and canonical derived comparison. `lem-weil-pbc-leray-acyclicity-quasi-iso` is an existing complex-level preservation statement; I read it but did not move the argument into that unsplit black box. The nine steps contain the actual dimension shifting and cone proof.

The prescribed msearch commands recorded LeanFinder, Loogle, LeanSearch, and grep searches for this item. A second semantic phrasing searched preservation of quasi-isomorphisms between acyclic complexes. I read Mathlib's `CategoryTheory/Abelian/RightDerived.lean` and `Algebra/Homology/DerivedCategory/ExactFunctor.lean`: the former constructs the classical derived functors from injective resolutions (and explicitly notes the planned bounded-below total functor); the latter requires finite colimits as well as finite limits, i.e. an exact functor. Neither is the theorem here for a merely left exact functor and termwise acyclic objects. Search hits about preservation of homology likewise require a stronger functor hypothesis. Queries are copied exactly from the command log, with no invented searches. No service was unavailable in this run.

## Generic tool uses

- `lem-weil-pbc-derived-functor-long-exact`: supplies the long exact sequences explicitly required by the unit's own proof. It leaves the dimension-shifting argument here.
- `lem-weil-pbc-complex-injective-resolution-mono`: supplies a genuine bounded below injective replacement with the same lower bound, needed in the imported complex proof.
- `lem-pur-quasi-iso-cone-acyclic`: supplies the generic equivalence between acyclic cones and quasi-isomorphisms, applied in both abelian categories.

These three off-unit facts are declared in `split_report.tool_uses` for the maintainer's judgment. Definitions and existing Mathlib leaves supply the remaining notions/tools. No `tool_uses` maintainer field is edited.

## Review by Q06

I read the current source `literature/blueprint/main-20261015/blueprint/sec-proper-base-change/sk-thm-acyclicity/_section.md`, the older unit record and chapter record, and the imported three proof paragraphs. I checked Stacks `derived.tex` at 013K (`lemma-injective-resolutions-exist`, part (3)), 015B (`lemma-higher-derived-functors`, parts (1)–(3)), 05TD (`lemma-left-exact-higher-derived`, part (3)), 015C (`lemma-F-acyclic`), 05TA (`proposition-enough-acyclics`, especially its cone/cycle proof), 05TH (`lemma-injective-acyclic`), 05TI (`lemma-enough-injectives-right-derived`), and 015E (`lemma-leray-acyclicity`). I verified tag/label correspondences in the local tags table. No SGA source is used. There are no new statements to source or to test separately.

Step 1 uses the actual cohomology/cycle definition in `def-weil-abstract-derived-category` and the positive-derived-vanishing definition in `def-sp-acyclic`. Exactness of the augmentation gives the displayed cycle short exact sequences; it does not assume that the resolution terms are injective. This is an elementary unpacking, not a new lemma.

Step 2 cites `lem-weil-pbc-derived-functor-long-exact`, whose statement really gives the entire sequence for every short exact sequence in any abelian category with enough injectives, and `lem-sp-derived-well-defined`, whose statement explicitly gives the natural identification of degree zero with v. `def-sp-acyclic` is used only for its definition. The vanishing flanks give the displayed cokernel and degree-shift isomorphisms; no uncited claim that v preserves arbitrary short exact sequences is made.

Step 3 uses the kernel-preservation and additivity definition `def-sp-left-exact-additive`, the cohomology quotient definition, and the degree-zero isomorphism just mentioned. The preceding step supplies all the nontrivial derived isomorphisms. I wrote out the factorization of the differential through its image and the monomorphism into the next term, so left exactness is applied to the correct kernel. For q=1 the shifting chain ends immediately; q=0 is separately vF; no negative-degree term or R^(-1) is used.

Step 4 cites the statement of `lem-weil-pbc-complex-injective-resolution-mono`: it gives an actual quasi-isomorphism A→J of complexes with J zero below the same integer a, and termwise injectivity. `lem-weil-pbc-derived-functor-injective-vanishing` explicitly states all positive right derived functors vanish on any injective object in any such abelian category. The injective definition supplies the elementary verification that zero is injective. I checked that neither theorem needs a Grothendieck hypothesis or enough injectives in the target category beyond the item's hypotheses.

Step 5 uses the cone formula of `def-weil-abstract-derived-category` and the actual statement of `lem-pur-quasi-iso-cone-acyclic`, which is the equivalence needed, not merely a definition of a cone. The lower bound is a−1 rather than a, since the cone term contains A^(n+1). The criterion applies to integer-indexed complexes in an arbitrary abelian category, hence in both A and B later.

Step 6 cites the long exact derived sequence and the definition of acyclicity. The sequence 0→J^n→J^n⊕A^(n+1)→A^(n+1)→0 is split in any abelian category. The three-object segment in each positive degree has zero outer terms, so the middle derived object is zero. This is a few-line consequence of already cited statements; I deliberately did not create a node for finite-sum closure or use the existing binary-product node, which concerns products of functors valued in abelian groups and does not state this claim for arbitrary target categories.

Step 7 again uses the actual long exact derived sequence, degree-zero identification, kernel preservation, and cohomology definition. I checked the induction's base: the cone is exact and zero below b=a−1, so its cycles T^b vanish as the image of the zero preceding term. The inductive claim quantifies over every positive r; the isomorphism R^r v T^(n+1)≅R^(r+1) v T^n has exactly the needed direction. The low-degree sequence is short exact because R^1 v T^n vanishes. Its surjectivity identifies boundaries with cycles after v, including the first possible degree and the degrees below the bound. This argument is here, not hidden in a newly named exact-complex lemma.

Step 8 uses additivity from `def-sp-left-exact-additive`, the displayed cone differential, and the cone criterion. The canonical biproduct comparison carries each entry of the differential to its v-image and the negative differential to its negative; this is a direct matrix verification, so there is no unstated comparison lemma or sign convention. The cone criterion is used in B only after exactness of vC has actually been proved.

Step 9 cites `lem-weil-pbc-right-derived-plus-injective`. Its statement gives a natural comparison on K^+, the bounded-below right derived functor on D^+, and invertibility of the comparison specifically on bounded below complexes of injectives; it is not an unbounded K-injective existence theorem with stronger hypotheses. The localization definition ensures Q(s) and Q(v(s)) are invertible in their respective categories. I wrote the naturality equation and solved for alpha_A, so this proves the canonical comparison, not just existence of an abstract isomorphism. The target has the same derived object as the statement.

I checked B–E against the final node: the statement is unchanged and retains both clauses, the notions have actual definition dependencies, all proof dependencies are exactly the step-use union, each citation was checked against its node's statement rather than its proof, and there are no new nodes duplicating a clause, a blueprint node, or an elementary consequence. The three tool nodes are genuinely general facts, not replacements for the unit's argument. The old spectral-sequence edge is gone. No step exceeds 2,000 characters. Empty/zero complexes and arbitrary negative lower bounds cause no exception to the cone/cycle proof; q=0 and q=1 have explicit treatments. No hypothesis of exactness of v, boundedness above, Grothendieckness, or termwise injectivity of A was introduced. All files written are in this item's sandbox; no Lean, repository or launcher file was changed and no compiler was run.

## What could not be finished

Nothing remains in the mathematical split. Server validation and direct delivery follow this report.

## Validation repairs

The standalone server review_split passed. The first delivery dry run required four citation excerpts to contain at least 40 characters; I replaced the short degree-zero and injective-vanishing excerpts with their full verbatim statements, including hypotheses. No mathematical statement or proof step changed in that repair.
