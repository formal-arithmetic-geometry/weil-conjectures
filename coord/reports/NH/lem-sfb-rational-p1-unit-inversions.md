## Worker report

### Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-rational-p1-unit-inversions.json`: the item, split in six steps; no Mathlib match.
- `citations.json`: all thirteen step/node pairs, with passages copied verbatim from the live statements.
- `searches.jsonl`: actual NH searches made with the prescribed msearch command.
- `report.md`: this report. `write_split.py` is sandbox-only preparation material and is not a project file.

### Attachments

None. Searches of `lean/WeilConjectures/` by the exact blueprint tag, `unitInversions`, `UnitInversionCondition`, and the twisted projection name found no declaration giving the item. In `lean/Sheaf/Paper/RationalP1UnitCounit.lean`, lines 437--440, `AlgebraicGeometry.ProEtale.RationalP1.unitInversions` states the intended condition but has `sorry`. I read its docstring and the conjunction at lines 30--44 of `RationalP1UnitInversionCondition.lean`; this is not an attachment. The candidate metadata is preserved.

### WANTED

None. The proof is marked agent-written because it expands the agent-written blueprint using existing DAG results.

### Corrections and provenance

The statement, statement dependencies, source note containing the old proof, and creator attribution are unchanged. The initial sandbox contained no item or split. The mandated abandoned-directory listing returned no matching attempts, including other groups. No item repair note was present. I copied the live node into the sandbox and retained all four NI search records from its creation. Their embedded results were read as inherited evidence; they are not NH searches and were not added to NH's log. NH searched a different question, explicitly concerning the shifted Tate projection and the extension from generators. LeanFinder returned generic derived-category/localization declarations; LeanSearch returned generic triangulated-closure, properness and AB4 instances; none gives the two specified internal-module maps. The first Loogle query rejected the namespace identifier and supplies no absence evidence; the corrected `"projectionFormula"` query had no hits. The recorded grep had no hits. All NH query texts and raw records are preserved exactly.

The older outline shifted an unshifted projection formula. Step 5 instead applies the existing theorem directly with the second input `L_P[2]`. Thus no additional shift-compatibility assertion is being assumed. Steps 2--4 explicitly distinguish constant-model bounded constructibility from general ring-object bounded constructibility and retain the actual canonical base-change transformation. No statement dispute was found.

### Unfinished work

None for this stage-1 split. The cited unsplit preservation item is a separate queue item; its statement supplies the hypotheses used here. There is no claim that this delivery proves Lean declarations.

## New nodes

None: zero new nodes and zero Mathlib leaves.

## Not duplicates

No new nodes were created. Whole-DAG keyword searches and whole-blueprint searches for proper base change, projection formula, unit inversion and Tate comparisons locate the existing general theorems and the parent unit/counit construction, not another node that replaces this pair of inversion witnesses. The exact condition node is a definition, not a proof. The generic existing projection theorem, bounded proper-base-change theorem, unbounded extension, finite-Tor equality and constant-model inclusion are cited rather than duplicated.

## Review by NH

I read `stages/1-dag.md`, the stage-1 brief, the three SETUP levels, GOAL, and delivery-errors B--E. The current chapter and unit records and `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-p1-adjunction-rational/_section.md` keep the projective-line adjunction route. In the current unit/counit proof, Well-definedness (2) calls for canonical proper base change on the localizing closure and (2)--(3) call for the projection formula. I read that whole short proof and the current bounded proper-base-change, unbounded-extension and localizing-projection statements under `latest/`. The item refines those exact obligations to the named maps. I also opened the full live statements of every node below; citations use their statements, never an assertion available only inside their proofs.

Step 1 uses `lem-sfb-rational-p1-localizing-preservation`. Its statement explicitly supplies qcqs, properness, standing schemes and arrows, preservation under `p_1^*`, and membership of the coefficient and Tate lines in bounded constructibles. These are exactly the facts the step takes. The field need not be separably closed and Y need not be proper over it. Distinct primes and the positive-characteristic field are already the preservation lemma's hypotheses, so no extra invertibility condition is added.

Step 2 uses `sk-def-sfb-constructible`, the final lemma/inclusion in `det-def-sfb-constructible-local-model`, and `sk-def-sfb-bounded-constructible`. I read the finite-constant-local-model source at `latest/blueprint/sec-proetale-coefficients/sk-def-sfb-constructible/sk-def-sfb-constructible-local-model.md`. The inclusion says finite constant local models are locally finitely presented. Keeping each finite stratification and the same bounds consequently proves the desired inclusion into the general ring-object bounded category in a few lines. This is elementary assembly, not an unproved equivalence of the two notions. The converse is neither stated nor used.

Step 3 uses clause (3) of `det-thm-sfb-proper-base-change-rational` for those bounded inputs and the explicit formula in `def-weil-pbc-ambient-ringed-exchange`. I checked the corners and arrows: X=P, Y=Y, X'=W, Y'=P, f=q, f'=p_2, g=q, g'=p_1. Thus the target is `Rp_{2*}p_1^*`, not the projection with the two roles silently reversed. Both definitions use the unit of p_2, the pullback composition comparison from q p_1=q p_2, and the q-counit. The bounded theorem concerns canonical maps, so the conclusion concerns the specified beta. Properness and the standing schemes come from Step 1; the coefficients are precisely E or the finite-subextension-valued Qlbar, never a discrete replacement.

Step 4 uses `det-def-localizing-closure-ctf-equals-bc` and `det-proper-base-change-unbounded-extension`. I read their complete live statements, including the corrected constant-model/Tor wording and the explicit exchange formula in the latter. The equality applies because P is qcqs and these are the listed rational coefficients. Its equality of localizing closures identifies precisely the source category in this item. The extension's displayed beta has the same three constituents as Step 3. The extension assumes a proper arrow between standing schemes and invertibility on every Dctf generator; Steps 1 and 3 verify both. No assertion that an arbitrary unbounded M is bounded is used.

Step 5 uses the full live `det-thm-sf-pf-field-localizing` statement: both inputs may be arbitrary objects of the indicated localizing closures. I checked A=p_1^*M on W, B=L_P[2] on P, and the proper map p_2:W->P. Shift closure follows directly from the full triangulated-closure definition `sk-def-localizing-closure`; A and L_P were supplied in Step 1. I read `def-sfb-rational-tate-pullback-comparison`: e is the actual positive Tate comparison at the same coefficient index. I read `def-sfb-tate-twisted-projection-comparison`: its formula uses the projection mate with second input L_P[2], followed by 1 tensor e and the tensor-shift comparisons. The step lists those factors in their prescribed order. Functors carry an isomorphism and its inverse to inverse maps, and a composite of inverse pairs is invertible; that is the elementary final assembly. This uses no unnamed comparison-identification lemma or unshifted-projection compatibility.

Step 6 uses the whole condition from `def-sfb-rational-p1-unit-inversion-condition`. Its statement and the source conjunction both require these very two maps. Packaging their witnesses is elementary and introduces no arbitrary substitute isomorphisms.

For hypotheses and edge cases I checked M=0, Y empty, Y=Spec(k) with k not algebraically closed, both rational coefficient choices, and unbounded M. Zero and empty cases introduce no nonempty-stratum assumption; the inclusion of constructibility permits the existing empty/zero presentations. The general field is allowed by the standing hypotheses. B=L_P[2] is a shift of a bounded generator, whereas M can have infinitely many nonzero cohomology groups: Step 4 and the full two-variable localizing theorem, rather than a bounded theorem applied directly to M, handle that case. No finite-coefficient annihilation or derived-completeness hypothesis enters this argument.

The non-elementary facts each have cited nodes (C1), and each cited statement supplies the fact taken (C4). No new statement requires a small-case audit of its own (B1--B10); the item keeps its complete objects and hypotheses. I checked the unchanged TeX statement and added TeX steps, retained all blueprint and imported metadata, and filled the split report's exact blueprint places. Each step is below 2000 characters. There is no relabelled clause in a new node, hidden long lemma, circular induction or appeal to an unspecified transport. A read-only dependency traversal found no path back to the item from any of its substantive cited theorems. No SGA route is used.

The server's preliminary `review_split` passed. It reports three off-unit theorem uses: bounded rational proper base change is the generic bounded tool for Well-definedness (2); the finite-Tor comparison identifies the two generator conventions; the unbounded extension is the generic extension tool for the same canonical exchange. None replaces the projective-line unit's proof route, and the existing localizing projection theorem itself uses these tools. These route notices are reported here for the maintainer; no maintainer-owned tool-use field was changed. The unit realization is outside this item's scope.
