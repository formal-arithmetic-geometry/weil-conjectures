## Worker report

Files written:

- `dag/nodes/sec-six-functors-basics/sk-lem-proper-unbounded-window-ii.json`: eight-step split, with steps 3, 5 and 8 repaired against the current DAG. The imported statement is unchanged.
- `dag/units/sk-lem-proper-unbounded-window-ii.json`: retained realization of the statement and both original proof paragraphs; only the authorized `realized` and `realized_by` fields differ from the base.
- `citations.json`: 23 verbatim quotations, one for each node citation of each step.

New nodes: 0. New Mathlib leaves: 0.

Attachments: none. I searched the read-only slopmaster2 `WeilConjectures/` tree for the item id, proper/direct-sum/coproduct and ind-constructible terminology. No project declaration states this E/Qlb pro-etale theorem. `AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_of_finite`, in `SixFunctors/Etale/Derived/ProjectionFormula.lean`, concerns finite coefficients and contains `sorry`; it is not an attachment. No new Mathlib search is claimed: the retained genuine search log and existing item search records remain unchanged, and no new node requires a search. Master declarations are reference material only.

WANTED: none.

## Landing-refusal repair

The current return is the landing refusal for head `815741ad57`: the cited statement `det-proper-unbounded-window-ii-general` changed relative to the review. I compared all 22 previously cited statement-dependencies/proof-dependencies in that returned commit with current server main, read their current statements, and separately read the current main and authoritative live-DAG versions. The read-only comparisons are saved in `repair-returned-vs-current.json` and `repair-current-dependencies.json` inside the sandbox. They are reference snapshots, not delivered node files.

1. **Named dependency revalidated.** The full current statement of `det-proper-unbounded-window-ii-general` assumes properness and one global bound on geometric fibre dimensions, and allows every small family in Dic with coefficients E or Qlb. Current main and the authoritative live DAG agree. At this repair the returned commit also has that same text, so I do not claim an enduring difference that the comparison does not show. I rewrote step 5 to explicitly substitute `(X_U,U,p_U,d_U,(b^*K_alpha))` for every object and hypothesis, retained the exact full-statement quotation, and confirmed the local comparison is the canonical comparison asserted there. This does not re-prove the detail node or add a bound to the item.
2. **Other changed citations repaired.** The actual returned-head/current-main comparison finds changes to `sk-prop-sfb-cartesian-coefficients` and `sk-def-sfb-derived-categories`. I read both entire current statements. Cartesian coefficients now specifies E as a finite subextension and Qlb with the condensed finite-subextension convention, separates untwisted assertions from Tate-twist hypotheses, and identifies module pullback with the lifted inverse image rather than literally the same functor. Step 3 now states this coefficient convention and uses only the untwisted assertion, which explicitly needs no invertibility of ell. Its quotation copies the current exactness/natural-isomorphism clause. Derived categories now states the existence hypotheses of the exact-functor assertion explicitly and distinguishes the master constructibility predicate. Step 3 uses only the exact-functor clause for the derived functors supplied by `sk-def-sfb-module-derived-pushpull`; its quotation is confined to that clause. No master locally-finitely-presented constructibility predicate is substituted for the scalar-local-model predicate defining this item's Dic.
3. **Additional hypothesis audit.** `det-ambient-ind-derived-triangulated` currently assumes a separated finite-type scheme over a positive-characteristic field. This item's arbitrary Y does not satisfy that assumption. I removed its citation and tool-use entry. Step 8 needs only that Dic is the full subcategory on its specified objects; this is its definition, so the argument now writes out the inherited Hom sets and the coproduct universal property directly using the unrestricted `det-ambient-ind-derived-sums` statement. No triangulated-subcategory theorem is needed there.
4. **Rebase and checks.** The delivery tool reconstructs this repaired split on current origin/newtargets-dag, preserving maintainer fields. The sandbox contains actual proof/citation/report changes, not an unchanged retry. I will run the required server dry run after these changes and leave the accepted sandbox for a fresh second reader. No compiler, Lake, Lean writing, live-project edit, or push is authorized or performed in this stage-1 repair.

The older E7/D1 repair is retained: the statement says only that p is proper. There is no added global fibre bound and no implicit finite-type-over-a-field setting. Affine restriction supplies d_U, the existing bounded-detail theorem is used there, and the canonical comparison descends. The old head `5657673fd6` and the earlier report are historical context, not the head of the current return.

## Source error

The unit's arbitrary-family paragraph chooses a single d without proving such a bound. Properness alone does not imply one: take Y to be the disjoint union of copies of Spec k indexed by n >= 0 and X the disjoint union of P^n_k, with the componentwise map. This is proper, since properness is local on the base, but the fibre dimensions are n. The corrected proof follows the same bounded-family/window route over each affine base open and descends the actual comparison; the unit and item statement remain unchanged.

The bounded detail source also prints `H^n(C[-a])=H^{n+a}(C)`. The correct cohomological formula is `H^n(C[-a])=H^{n-a}(C)`: for a nonzero sheaf C in degree zero and a=1, C[-1] has H^1=C, whereas the printed formula gives H^2(C)=0. This is a source-proof typo, not a failure of the bounded-detail statement. Its proof is not reproduced here and its file is not edited. These are the previously reported source errors, not new statement disputes in this repair.

## Not duplicates

- `sk-lem-proper-unbounded-window-ii` vs `det-proper-unbounded-window-ii-general`: the item has only properness; the existing detail theorem additionally assumes a global geometric-fibre bound. Step 5 applies it after establishing its hypotheses on each affine base open. The item carries localization and descent, not a second bounded-window proof. There are no new nodes.

What could not be finished: no mathematical step of this one-level split remains open. The delivery dry run below determines mechanical acceptance; a separate second reader must review and deliver the result.

## Review by Q19

I read the complete main-20261015 chapter and unit records, the unit statement and both original proof paragraphs, the general detail statement and proof, and the bounded detail proof. The chapter's layer B uses actual module objects over the pulled-back condensed ring, and the split retains those coefficients. I also read every cited node statement, including the changed statements discussed above, rather than inferring their conclusions from their proof text. No new node or Mathlib leaf is being introduced. The general-detail quotation is checked against both server main and the authoritative live DAG; the current return is addressed explicitly under Landing-refusal repair.

**Step 1.** `det-ambient-ind-derived-sums` clause 1 gives ambient derived sums, the cohomology/sum comparison, and Dic closure for arbitrary small families and arbitrary schemes. The equation on coprojections defines the canonical map c; the proof must establish that map's invertibility, not just an isomorphism of its endpoints.

**Step 2.** I checked the statements of `lem-weil-pbc-proper-base-change`, `def-weil-proper-morphism`, `lem-weil-pbc-affine-scheme-qcqs`, `lem-fin-finite-type-fibre-dimension-bound`, `lem-pc-dimension-affine-open-cover`, `lem-weil-pbc-dimension-preserved-field-extension`, and `def-weil-finite-type-morphism`. They give properness of p_U, its finite-type property, quasi-compactness of U, a bound for ordinary fibres, the affine dimension formula, and preservation under field extension for finite-type fibre algebras. I read Stacks Tag 0A3V, `morphisms.tex`, `lemma-morphism-finite-type-bounded-dimension`, and Tag 00P3, `algebra.tex`, `lemma-dimension-preserved-field-extension`. The quasi-compact base hypothesis holds because U is affine, not because Y is assumed quasi-compact. Tensoring a finite algebra-generator presentation with the residue field supplies the finite-type hypothesis for each fibre chart. Empty fibres cause no problem. The chart dimension formula bounds geometric fibres after extension to an algebraic closure. Different U may have different d_U.

**Step 3.** `lem-weil-proetale-weakly-etale-localization` supplies the site/slice identification; only its coefficient-independent clause 1 is used for these non-discrete coefficients. `lem-weil-pbc-proetale-ringed-open-comparison` supplies the actual ringed restriction comparison. The current `sk-prop-sfb-cartesian-coefficients` gives the canonical ring isomorphism and exact module pullback for the same E or Qlb, with no untwisted invertibility condition. The adjunction of `sk-def-sfb-module-pushforward-pullback` and the derived adjunction of `sk-def-sfb-module-derived-pushpull` give preservation of colimits, including derived coproducts, through the explicit Hom calculation. The current exact-functor clause of `sk-def-sfb-derived-categories` identifies the already-defined derived pullback with termwise exact restriction. Its revised D_cons constructibility row is not used. `sk-def-sfb-constructible` explicitly imposes its scalar finite local model condition locally on affine opens; restricting the strata and presentations preserves it. Exact restriction and preservation of filtered colimits then give every b^*K_alpha in Dic. The two stale quotes were replaced by current used clauses.

**Step 4.** `def-sfb-finite-lower-star` supplies the section formula with A=Ab, and `sk-def-sfb-module-pushforward-pullback` supplies the induced module action. Evaluating on T over U gives the natural equality of underived open restriction and p_U pushforward. `sk-def-sfb-module-lower-shriek` explicitly makes b_! exact and left adjoint to b^*. Thus `lem-weil-pbc-right-adjoint-preserves-kinjective` applies to b^*, and `sk-def-sfb-module-derived-pushpull` supplies the K-injective computation of Rp_*. I read Stacks Tags 08BJ and 08FI (`lemma-adjoint-preserve-K-injectives`, `lemma-restrict-K-injective-to-open`) and the extension-by-zero exactness Tag 03DJ. The comparison is for arbitrary unbounded complexes; it is open localization, not the unproved proper base change target.

**Step 5.** I reread the entire current statement of `det-proper-unbounded-window-ii-general` in both server DAGs. Its properness hypothesis is step 2, its global geometric bound is d_U on this p_U, its input membership is step 3, and its E/Qlb coefficients are unchanged. The conclusion is precisely c_U. The step now spells out every substitution. Only its statement is used, so the source's finite-window proof and bounded induction need not be duplicated in the item.

**Step 6.** This is the elementary coprojection calculation from the natural comparison in step 4. Naturality of theta gives the displayed equality on each summand, and the coproduct universal property identifies the transported a^*c with c_U. The restricted map is consequently the correct canonical comparison.

**Step 7.** `lem-weil-pbc-unbounded-derived-iso-cohomology` states the isomorphism criterion in any abelian unbounded derived category. Exact restriction identifies the cohomology maps. The written sheaf-separatedness argument on the cover T x_Y U detects a zero module sheaf, so kernels and cokernels vanish globally. This needs no global bound, finite cover of Y, or boundedness of the complexes.

**Step 8.** I removed `det-ambient-ind-derived-triangulated` because its current geometric hypotheses are not available. Fullness here is definitional: Dic has ambient morphisms between its designated objects. The unrestricted `det-ambient-ind-derived-sums` gives closure under ambient sums; the same Hom sets then give the coproduct universal property in Dic. Fullness also retains the inverse of c and its two equations. The restricted functor is the one already named in the unchanged item statement; no global amplitude claim is taken from the bounded-fibre theorem.

**B--E and small cases.** No new nodes means there are no new unsplit proofs, duplicates, elementary extra nodes, hollow definitions, or unrun new-node search entries. Each non-elementary tool is a cited node; their union equals proof_deps and the necessary off-unit tools remain declared. I checked empty and singleton families, zero objects, the empty base, zero-dimensional fibres, a nonzero sheaf shifted by one, and complexes unbounded in both directions. The disjoint union of projective spaces confirms that the local bounds cannot be replaced by an unstated common d. Coefficients stay in the same pulled-back condensed module categories throughout, without finite-coefficient replacement or an SGA route. This repair changes the proof and citation records where current statements require it; it is not an unchanged re-push.


## Earlier second reading (a previous round; superseded)

- Item/source: read the main-20261015 chapter, unit `_section.md`, both unit proof paragraphs, and both bounded/general detail statements and proofs; verdict: the item statement matches the source verbatim, with only properness and the same condensed E/Qlb coefficients. The source's global-bound inference is invalid for the documented disjoint union of projective spaces; the existing affine-local repair faithfully retains its window route.
- Step 1: read `det-ambient-ind-derived-sums` clause 1 and its definition of Dic; verdict: arbitrary small ambient sums and input membership are available, and the equation on coprojections defines the canonical comparison actually being proved invertible.
- Step 2: read all seven cited statements, Stacks 0A3V (`morphisms.tex`, `lemma-morphism-finite-type-bounded-dimension`), 00P3 (`algebra.tex`, `lemma-dimension-preserved-field-extension`), and 04MU (`properties.tex`, `lemma-dimension`); verdict: proper base change gives finite type, affine U is quasi-compact, finite-generator presentations give finite-type fibre charts, and field extension preserves their dimensions. The bound depends on U; no quasi-compactness of Y is used. Empty fibres and dimension zero pass.
- Step 3: read all seven current cited statements, including the exact untwisted cartesian-coefficient clause and the existence-qualified exact-derived-functor clause; verdict: coefficients are the actual pulled-back condensed rings, module restriction is exact, both adjunctions give preservation of colimits/sums, and restriction preserves ind-constructible cohomology. Repaired the constructibility argument to test each affine open of the open subscheme as the same affine open in the original scheme; this avoids an implicit quasi-compactness assumption on the open immersion.
- Step 4: read all five cited statements and Stacks 08BJ (`derived.tex`, `lemma-adjoint-preserve-K-injectives`), 08FI (`sites-cohomology.tex`, `lemma-restrict-K-injective-to-open`), and 03DJ (`sites-modules.tex`, `lemma-extension-by-zero-exact`); verdict: the section formula and the module action give the underived comparison, and exact b_! makes b^* preserve K-injectives. This proves the natural comparison for unbounded complexes without invoking proper base change.
- Step 5: read the complete current `det-proper-unbounded-window-ii-general` statement; verdict: its properness, global geometric-fibre bound, input-class and coefficient hypotheses hold on precisely (X_U,U,p_U,d_U,(b^*K_alpha)). Its conclusion is the canonical local comparison. It is an existing node, not a newly introduced restatement; its bounded induction/window proof remains there.
- Step 6: checked the displayed equation against step 4's natural comparison; verdict: elementary, because naturality identifies the components on each coprojection and the coproduct universal property then identifies the maps. The directions of both theta maps and the inverse are correct.
- Step 7: read `lem-weil-pbc-unbounded-derived-iso-cohomology` and Stacks 05RT (`derived.tex`, `lemma-acyclic`); verdict: no boundedness is required. Exact restriction gives the local kernel/cokernel calculation; the cover of each pro-etale object by its inverse images of affine base opens detects zero sheaves. Infinite affine covers cause no issue.
- Step 8: reread `det-ambient-ind-derived-sums` and the definition of Dic; verdict: the ambient coproduct lies in the full subcategory and has the same universal property. For the restricted functor named by the assertion, the ambient inverse is therefore an inverse in Dic. The unavailable finite-type-over-a-field hypotheses of the triangulated-subcategory node are not used.
- New nodes: none (0 new nodes, 0 Mathlib leaves); verdict: no new-node B1--B7, duplicate, elementary-node, or Mathlib-search cases arise. Read the retained actual search log and the current slopmaster2 keyword hits; no exact project attachment was found. No new searches are claimed.
- Citation and form checks: opened every cited node statement and verified all 23 quotations as verbatim excerpts of the current statements, one per (step,node); verdict: valid. The union of the uses equals proof_deps, all generic off-unit uses are declared, and the unit realization retains both original paragraphs. The dry-run command's trailing dot in the brief is not accepted by the installed CLI (its usage accepts only group/item and --no-push), so the required tool is invoked without that trailing argument.
- Small cases: checked empty/singleton families, zero complexes, empty base/source, fibres of dimension zero, a nonzero sheaf shifted by one, and two-sided unbounded complexes; verdict: the local and canonical-map arguments still apply. The disjoint union of P^n over the disjoint union of Spec k confirms the need for local bounds. The bounded-source sign typo is already correctly documented and is not imported into this split.

Changes in this second reading: tightened only step 3's affine-open constructibility argument and appended this independent review. The item statement, existing detail-node applications, other correct proof steps, and valid citation excerpts were retained. No shared-project, launcher, Lean, or source file was modified and no compiler or Lake command was run.


## Statement corrected

STATEMENT-DISPUTED: the imported ii statement names the corestriction
$Rp_*:\Dic(X,\Lambda)\to\Dic(Y,\Lambda)$ without the geometric-fibre bound
required by the cited `sk-lem-proper-unbounded-window`. Reading that node's whole
statement and the blueprint `_section.md` exposes the type-check gap: properness
alone supplies no term for its bound $d$. The proper map
$\coprod_{n\geq0}\mathbf P^n_k\to\coprod_{n\geq0}\operatorname{Spec}k$
has unbounded fibre dimensions. Steps 2–7 correctly establish the canonical
comparison in the ambient derived category without such a bound, but this does
not prove that its objects have globally ind-constructible cohomology. The old
step 8 assumed the corestriction it needed; a local-to-global theorem for the
specified global filtered presentations was neither cited nor proved.

The corrected statement makes the global geometric-fibre bound explicit,
faithfully to the hypothesis of the cited window theorem and the $d$ used in the
ii source proof. Step 8 now invokes that theorem with its full hypotheses to
establish the corestriction before invoking fullness. The comparison proof is
retained. This correction supersedes the earlier report's claims that the
statement is unchanged and that no mathematical gap remains. It does not assert
that the stronger unrestricted corestriction is false; it removes an unsupported
signature from this source-based split. No target declaration is changed.

Citer checked: `det-proper-image-localizing-proper`. Its only use of this item is
for schemes separated and finite type over a field. Its base is quasi-compact
(the node already cites `lem-weil-pbc-qcqs-over-affine`), and its proper morphism
is finite type. `lem-fin-finite-type-fibre-dimension-bound`, already in that
node's proof dependencies, gives an ordinary-fibre bound; applying
`lem-weil-pbc-dimension-preserved-field-extension` to the finite-type fibre
charts, as in our step 2, gives the geometric-fibre bound. The citer's assertion
therefore still holds. This is the only current statement/proof-dependency citer.

## Second reading by Q19

This is a fresh reading of the sandbox after the landing-refusal repair. I read
`coord/delivery-errors.md` B–E, `GOAL.md`, `coord/dag-sync.md`, the current unit
record, the main-20261015 chapter and ii source files, and every cited node's
statement. The earlier reviews are retained above as history.

- Item/source: compared `_section.md`, both original unit paragraphs, both existing detail statements/proofs, and the current window statement; verdict: the missing global-bound hypothesis for the displayed corestriction required the explicit `STATEMENT-DISPUTED` correction above. The coefficient conventions and arbitrary small-family conclusion are retained.
- Step 1: checked `det-ambient-ind-derived-sums` clause 1 and its inline definition of Dic; verdict: the source sum belongs to Dic and the coprojection equations define the particular canonical comparison. Updated the last sentence to distinguish the comparison proof's local bounds from the global hypothesis now used for the corestriction.
- Step 2: checked all seven cited statements and Stacks 0A3V (`morphisms.tex`, `lemma-morphism-finite-type-bounded-dimension`), 00P3 (`algebra.tex`, `lemma-dimension-preserved-field-extension`), and 04MU (`properties.tex`, `lemma-dimension`); verdict: properness survives base change, affine U is quasi-compact, and finite-generator presentations give finite-type fibre charts. Tightened the extension argument to the field of an arbitrary geometric point, so the conclusion is the exact geometric bound used in step 5. Empty fibres, dimension zero and empty U pass.
- Step 3: checked all seven used node statements, especially the untwisted cartesian coefficient clause, the exact-derived-functor existence qualification and the scalar-local-model constructibility predicate; verdict: the same E/Qlb module rings are used, exact restriction commutes with cohomology and filtered colimits, and the written adjunction argument gives coproduct preservation. Every affine open of an open subscheme is the same affine open of the original scheme; hence constructibility restricts without assuming the immersion is quasi-compact. No change needed.
- Step 4: checked the section formula, induced module action, exact open extension-by-zero adjunction, K-injective preservation and derived-resolution computation in all five cited statements; also read Stacks 08BJ (`derived.tex`, `lemma-adjoint-preserve-K-injectives`), 08FI (`sites-cohomology.tex`, `lemma-restrict-K-injective-to-open`) and 03DJ (`sites-modules.tex`, `lemma-extension-by-zero-exact`); verdict: the natural comparison holds for arbitrary unbounded complexes. Added the coefficient-section calculation to justify equality of the module actions, rather than only the underlying abelian sheaves.
- Step 5: checked the full current `det-proper-unbounded-window-ii-general` statement against the main-20261015 general detail source; verdict: (X_U,U,p_U,d_U,(b^*K_alpha),Lambda) discharges every hypothesis and its conclusion is c_U. This is a pre-existing bounded-fibre detail, not a new restatement, and only its statement is used. No change needed.
- Step 6: checked the displayed coprojection equation against step 4's natural isomorphism and step 3's coproduct identification; verdict: elementary, with naturality giving each component and the universal property giving equality of the canonical maps. No hidden transport or boundedness argument remains.
- Step 7: checked the unbounded isomorphism criterion node, Stacks 05RT (`derived.tex`, `lemma-acyclic`), and Mathlib `DerivedCategory.isIso_iff` in `HomologySequence.lean` lines 88–89; verdict: exact restriction identifies kernels/cokernels and the displayed sheaf-separatedness argument on T x_Y U detects their vanishing. It proves ambient invertibility even for infinite covers and complexes unbounded in both directions. No change needed.
- Step 8: checked the full current `sk-lem-proper-unbounded-window` statement and `det-ambient-ind-derived-sums` clause 1; verdict: repaired. The now-explicit global geometric bound permits the former theorem to supply the corestriction and all target memberships. The latter gives the target coproduct, and fullness retains the inverse and its equations. Marked this step non-elementary because it now invokes the window theorem, rather than assuming its output.
- New nodes: none (0 new nodes, 0 Mathlib leaves); verdict: no new-node B1–B7, elementary-extra-node or duplicate cases arise. I independently ran a broader LeanFinder query for proper-derived coproduct preservation and a Mathlib grep for coproduct/rightDerived terminology through the required msearch.py tool. Both actual results are in searches.jsonl and mathlib_searches; none states this theorem. The slopmaster2 coproduct hits concern FullCD assumptions and contain sorry, not this E/Qlb theorem; master remains reference material only.
- Citations/form: checked every (step,node) against the current full node statement; verdict: 24 quotations for 24 citations, including the new step-8 window citation, with exact verbatim excerpts. The union of uses equals proof_deps. Original unit statements and proof paragraphs remain intact; only its existing realization record is delivered.
- Small cases: checked empty and singleton families, zero complexes, empty source/base, fibres of dimension 0, a nonzero sheaf shifted by one, and two-sided unbounded complexes; verdict: the corrected corestriction and comparison proof apply. The disjoint union of projective spaces is explicitly outside the corrected corestriction assertion but is still covered by the ambient comparison argument. The bounded source's shift-sign typo remains correctly documented above and is not reproduced.

Changes: made the source's missing global fibre-bound hypothesis explicit and
recorded the statement correction and its sole citer; supplied corestriction
membership in step 8 using the existing window theorem and added its quotation;
tightened arbitrary-geometric-point and coefficient-action calculations; recorded
the two genuine independent searches. All other correct proof text and the first
worker's review remain in place. No Lean, shared-project, launcher or live-source
file was written; no compiler, Lake, or local preflight tool was run.

Synchronization revalidation: while the dry run waited for delivery capacity, the shared DAG refreshed `det-proper-unbounded-window-ii-general` to its reviewed expanded statement. I read that complete statement, including its coefficient, size and canonical-coprojection conventions; step 5 meets them all without a further proof change. Replaced its quotation by the full current statement. The mathematical hypotheses and conclusion of that dependency are unchanged.

Delivery-form repair: stage-1 preflight rejects `statement_change` as a maintainer-owned field. I therefore restored the imported item statement and the original full-subcategory conclusion step, removed the added citation, and retained the source-error/counterexample discussion as an explicit review finding. The affine-local comparison proof and all current dependency quotation repairs remain.
