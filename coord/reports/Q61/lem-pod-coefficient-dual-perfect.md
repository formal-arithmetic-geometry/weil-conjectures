# Worker report: lem-pod-coefficient-dual-perfect

## Files written

- `dag/nodes/sec-poincare-duality/lem-pod-coefficient-dual-perfect.json`: statement item, split into eight steps; no exact Mathlib match.
- `citations.json`: 37 step/node entries, each quoting the current cited statement verbatim.
- `searches.jsonl`: actual search-tool records. The item records every query, with the actual outcome.
- `report.md`: this report. `write_split.py` is sandbox-only working material and is not a delivery file.

There are **0 new nodes and 0 new Mathlib leaves**. The proof reuses existing generic results; its elementary splitting and sign calculations remain steps. Neither chapter nor unit records are changed: the parent unit `sk-def-ops` is a definition and has no proof steps to realize.

## Attachments

No exact attachment. I searched `WeilConjectures/` in the read-only slopmaster2 checkout for the item tag, coefficient-dual terminology, and the candidate names. In `WeilConjectures/SixFunctors/ProEtale/Derived/Perfect.lean`, `AlgebraicGeometry.ProEtale.isDualizable_derivedDual` (lines 144--148) proves preservation of **dualizability**, and `AlgebraicGeometry.ProEtale.constructibleFiniteTor_derivedDual` (lines 656--683) proves the constructible conclusion for `[Finite Λ]` ordinary module sheaves. These are useful partial results, but together they do not state the item at the completed integral, scalar-localized rational and common finite-field stages. Moreover the local-perfectness/dualizability identification `AlgebraicGeometry.ProEtale.DerivedCategory.isDualizable_iff_isLocallyPerfect` (lines 446--449) is explicitly `sorry`. I read the corresponding entries in both compressed full and 7d675a26 sorry maps; the two candidate dual theorems have `s: false, ts: false`, but their different notions and coefficient domains still prevent attachment. I did not promote a partial docstring tag to an exact proof.

## WANTED

None. The current blueprint and the needed Stacks source files are present. No SGA source was used.

## Faults repaired and scope

The imported proof gives one paragraph. It invokes a degree-zero finite-projective tensor-Hom statement to compute a whole bounded complex without naming the required bounded Hom calculation. It then applies `prop-pod-perfect-local-model`, whose actual statement has finite coefficients and concludes bounded constructible cohomology, as though it supplied finite Tor amplitude at every coefficient stage. That inference is not justified by its statement. The imported hyperlink for `D^b_ctf` also points to `def-weil-finite-torsion-constructibility`, which defines only the finite `D^b_c` category.

I retained the statement's hypotheses and both conclusions, made its four coefficient stages and the correct finite-Tor/perfectness/dual definition dependencies explicit, and replaced that hyperlink with the finite-Tor definition. This is an elucidation, not a disputed or weakened statement. In particular no properness, extra six-functor-datum axiom, or new ambient exceptional-adjoint assumption was added. The existing fixed conventions themselves remain unchanged.

The complete local proof follows the actual current `main-20261015` item proof, with Stacks Tag **08JJ**, `sites-cohomology-lemma-dual-perfect-complex`, supplying its generic local calculation. Tags **08JB**, `lemma-restriction-RHom-to-U`, and **08JI**, `lemma-Rhom-complex-of-direct-summands-finite-free`, make the restriction and bounded-Hom steps precise. The rational finite-filtration expansion follows the same argument and the specified scalar-localization operations; it does not assume a rational retract lifts integrally. The common-stage argument uses a finite field of definition. Constructibility and finite Tor amplitude are separately supplied by the already split concrete preservation theorem, so a uniform global bound is never inferred merely from locally varying bounds.

I deliberately did not apply `prop-sf-dualizable` or `lem-sf-hom-finite-projective` as statements here: their current statements introduce a six-functor datum with extra axioms. Its local proof is useful mathematical material, but those extra hypotheses should not be silently introduced into this item. Instead every generic fact used by the expanded argument is separately cited, with its own actual hypotheses.

## Existing nodes and Mathlib searches

Whole-DAG searches included coefficient duals, perfect duals, finite-projective complexes, the generic Hom model, restriction, scalar localization and triangle comparison. `tools/blueprint_refs.py search` was run for `coefficient dual`, `perfect`, and `coefficient duality`, and `ancestor` identifies the item itself as blueprint ancestor. The search found broader or partial statements (`prop-sf-dualizable`, `prop-sf-dualizable-hom`, `thm-sf-dual-perfect`, `sk-def-perfect`), not another exact four-stage statement with both clauses and the same hypotheses. `blueprint.same_as` is therefore `[]`. Existing generic nodes were reused throughout; no new duplicate was made.

All Mathlib searches were run through `msearch.py Q61 lem-pod-coefficient-dual-perfect`, and their literal queries are in the item and the log. Two different semantic phrasings were tried, as well as LeanSearch, two Loogle queries and two source greps. The second semantic search found `Module.dual_projective`; I read `Mathlib/LinearAlgebra/Dual/Lemmas.lean` lines 137--152, including `dual_projective` and `dual_finite`. These concern ordinary modules and do not assert the derived sheaf/coefficient-stage theorem. I also read `Mathlib/Algebra/Homology/HomotopyCategory/KProjective.lean` lines 100--124: `CochainComplex.isKProjective_of_projective` assumes global categorical projectivity of terms and is not applicable just from local sheaf finite projectivity. The other hits concern t-structures, scalar dual bases, perfect pairings or ring perfection. No Mathlib result states the item or a one-line specialization of it. The Loogle query mentioning `CategoryTheory.IsDualizable` returned an unknown-identifier diagnostic, recorded as such, not as evidence about the project's declaration. Every queried service returned a response in this run.

## Not duplicates

No new nodes. In particular the generic bounded-free ringed-site Hom calculation, the degree-zero full-faithfulness lemma and the finite-tail triangle lemmas already exist and are cited rather than recreated. The ordinary finite-projective dual Mathlib fact likewise already has a DAG node; the elementary sheaf retraction calculation here needs no new one.

## Review by Q61

I read `stages/1-dag.md`, the worker brief, all of delivery-errors B--E, the three-level restrictions in SETUP, GOAL and dag-sync, the chapter and `sk-def-ops` unit records, and the current `main-20261015` item statement/proof. The unit is definitional, so the local argument preserves its operations/dual conventions and does not replace any unit proof route. I also read the current `prop-sf-dualizable` proof as an audit comparison, and checked the Stacks text for Tags 08JJ, 08JI and 08JB directly in `sites-cohomology.tex`. For the rational induction I read `derived.tex` Tags 0152 (`lemma-derived-canonical-delta-functor`), 014A (`lemma-third-isomorphism-triangle`) and 06XS (`lemma-negative-exts`, degree-zero clause). The ordinary sheaf-Hom formula was checked in `sites-modules.tex`, section 04TT and Lemma 03EM. There are no new-node sources to check.

**Step 1.** I opened the full statements of `def-pod-coefficient-dual-on-x`, `def-weil-derived-pullback-tensor-hom`, `lem-weil-constant-coefficient-objects-constructible`, `def-weil-finite-tor-amplitude`, and `thm-sf-ctf-stability`. The unit theorem states both constructibility and the finite reduction of the completed unit, rather than merely naming it. The Tor definition requires one interval independent of the integral reduction index, and the units all have the explicit interval `[0,0]`. Stability (ii) actually asserts internal-Hom preservation on the finite pro-etale finite-Tor domains; (vii) states the integral equality and internal-Hom preservation and then passes this to both field stages. I use those preservation clauses, not an unjustified sharper bound. The fixed `X` is separated finite type over the algebraic closure of the finite field, and the coefficient prime is different from the geometric characteristic. The current source stability statement/proof was read in the main-20261015 `sk-thm-sf-kunneth-verdier` folder. This is the repaired justification of the final clause that the imported local-model citation did not supply.

**Step 2.** I checked `def-pod-perfect-complex-on-x` against its reviewed site-perfectness dependency, including the completed integral unit and locally varying bounds. `lem-pur-site-restriction-module-adjunction-exact` states exact restriction on the slice, and `lem-weil-pbc-ringed-internal-hom-exact-restriction` explicitly states the Hom restriction isomorphism for arbitrary derived objects. Thus neither a definition of a site nor a notion of Hom is being cited as a theorem about restriction. The source's ringed site is taken small in the fixed universe, as are the module sites in the cited generic nodes.

**Step 3.** The only cited construction is `def-pur-sheaf-hom`, whose statement defines sections as module maps on slices. Dualizing the actual maps `i_r,p_r` gives the retraction in the correct order: `i_r^* p_r^*=1`. Finite tuples identify the middle sheaf with `R^m`; this works for `m=0`. This is an elementary written calculation and is not a new theorem node or a claim of global projectivity of a sheaf.

**Step 4.** I opened `lem-weil-pbc-ringed-site-bounded-free-rhom-model`: it states exactly the Hom-complex representation under bounded-above/finite-summand hypotheses on the first complex and a bounded-below hypothesis on the second. Here `P` is bounded and the second complex is `R[0]`, so every hypothesis is supplied. `def-pur-hom-complex` states the differential, giving `(-1)^(j+1)` and support `[-b,-a]`; `def-weil-site-perfect-complex` states exactly the resulting local condition. This repairs the gap between a degree-zero tensor-Hom lemma and the whole complex.

**Step 5.** I read the scalar-localization definition (same objects, localized Hom modules, no Karoubi envelope), exact localization, the full generic restriction/triangle statement, the K-injective Hom definition, and the degree-zero full-faithfulness statement. The generic scalar-localization definition is also cited for the ambient module-derived slice categories; I do not identify every local term with a globally constructible object. The latter is a Mathlib leaf and explicitly identifies maps of degree-zero modules with derived maps. Thus clearing denominators of the splitting maps yields actual module maps to which the natural comparison applies. No equation `pi=1` is assumed integrally: that equation is used only after scalar localization. The inverse of the retract of an invertible comparison is written out, so this is not an unexplained transport of an isomorphism. Applying the contravariant rational Hom to the displayed retraction supplies an actual finite-sum retraction of the dual term.

**Step 6.** I opened `lem-pc-stupid-tail-hom-short-exact`; it supplies a morphism of the two actual Hom short exact sequences for every coefficient-complex map. Applied to `R[0] -> I`, it gives precisely the comparison needed here. `lem-weil-pbc-complex-ses-triangle` states naturality of the connecting morphism, not just existence of some cone. `lem-weil-linear-scalar-localization-triangulated` preserves those triangles, and `lem-sf-triangle-morphism-iso` applies to this morphism with two invertible components. The descending induction is specified from the zero tail, with the single-term comparison supplied by step 5. I checked the boundary block `(-1)^r phi d_P^r` from the Hom differential; this avoids the common error of asserting connecting-map compatibility without a map of triangles. Only finitely many tails occur. The conclusion is an actual bounded reversed-dual model, not a claim about arbitrary infinite totalizations.

**Step 7.** I read the common-stage definition and its Hom formula, the site-perfectness condition requiring a perfect finite-field representative, exact scalar extension, and `lem-fix-operation-reduction`. These state the field-of-definition, exactness, and internal-Hom/unit comparisons being used, respectively. The finite projective presentations are preserved because a functor preserves composition and identities and the scalar-extension functor is additive, so the equation `pi=1` survives. The comparison with the next field's coefficient dual is cited to the operation comparison theorem, not silently inferred from preservation of retractions.

**Step 8.** The two cited definitions identify `H` with the coefficient dual and define perfectness on objects of the finite-Tor category. Membership was proved first, so use of the perfectness definition here is correctly typed. This final step is elementary assembly of the preceding conclusions.

I checked small cases: the zero complex and rank-zero summands give zero duals; a single coefficient unit gives itself; a complex with its sole term in degree `r` has dual term in degree `-r`; a two-term differential is transposed with the stated sign and still squares to zero. Over a nonreduced finite coefficient ring, finite-projective terms stay summands of free modules; an arbitrary finite stalk is never substituted for projectivity or finite Tor amplitude. For a rational splitting with a denominator, the argument uses the splitting only in the localization, so it does not require an integral splitting. At the common stage enlarging the field preserves the splitting equations. Local bounds may vary, and their global uniformity is not assumed: the actual geometric preservation theorem handles constructibility and finite Tor amplitude separately.

I checked the dependency closure of the substantial candidate tools, including `thm-sf-ctf-stability` and the ringed-site calculations; none reaches this item. All proof uses are in `proof_deps`, every step has a Boolean elementary marker and a source, and each of its 37 citations has a verbatim quote. Generic off-unit theorem uses are declared with their precise purpose in `split_report.tool_uses`; the definitions and Mathlib leaves are reused as such. There are no new unsplit statements hiding the item's clauses, no duplicated definitions, no unauthorized file changes, and no Lean writing or compiler execution.

## Unfinished work

No mathematical subtask remains for this one-level split. A fresh second reader must review and deliver this sandbox after the required dry-run gate; this worker does not push.

## Second reading by Q61

**Item statement.** Checked against the current `main-20261015` and archived blueprint statements, [def-pod-conventions], and the four coefficient-stage definitions; verdict: faithful, well-typed, and neither weakened nor strengthened.

**Step 1.** Checked [lem-weil-constant-coefficient-objects-constructible], [def-weil-finite-tor-amplitude], and clauses (ii) and (vii) of [thm-sf-ctf-stability]; verdict: the unit has the required uniform finite Tor interval and internal Hom preserves the stated constructible finite-Tor domains at all four stages.

**Step 2.** Checked [def-pod-perfect-complex-on-x], [def-weil-site-perfect-complex], [lem-pur-site-restriction-module-adjunction-exact], [lem-weil-pbc-ringed-internal-hom-exact-restriction], and Stacks Tags 08JB and 08JJ; verdict: local slice models and restriction are stated with the needed hypotheses, including the completed integral unit.

**Step 3.** Checked the sheaf-Hom definition and the direct-summand maps on finite tuples, including rank zero; verdict: the displayed contravariant retraction is correct and elementary.

**Step 4.** Checked [lem-weil-pbc-ringed-site-bounded-free-rhom-model], [def-pur-hom-complex], and Stacks Tag 08JI; verdict: the bounded Hom complex, reversed degrees, sign, and finite support are justified.

**Step 5.** Checked [def-weil-rationalization-karoubi], [def-weil-linear-scalar-localization], [lem-weil-pbc-derived-single-fully-faithful], and the finite-free/retract argument of Stacks Tag 08JJ; verdict: denominators are cleared only for localized morphisms, the comparison is natural, and no integral splitting or idempotent completion is assumed.

**Step 6.** Checked [lem-pc-stupid-tail-hom-short-exact], [lem-weil-pbc-complex-ses-triangle], [lem-weil-linear-scalar-localization-triangulated], [lem-sf-triangle-morphism-iso], and the signed Hom differential; verdict: the finite descending-tail induction supplies the triangle morphism and connecting-map compatibility explicitly.

**Step 7.** Checked [def-weil-algebraically-closed-coefficients], [lem-weil-scalar-extension-exact-triangulated], and [lem-fix-operation-reduction]; verdict: finite field of definition, scalar extension, and coefficient-dual comparison are all stated and preserve the splitting equations.

**Step 8.** Checked [def-pod-perfect-complex-on-x] and [def-pod-coefficient-dual-on-x]; verdict: the preceding constructibility and local-model conclusions assemble exactly to the two item conclusions.

**New nodes.** There are zero new nodes and zero Mathlib leaves; there were therefore no additional node statements or source records to audit. Existing generic nodes were checked for duplicate use and their cited statements match the steps.

**Small cases.** The zero complex, rank-zero summands, a one-term unit, a one-term shift, a two-term signed differential, and localized splittings with denominators all satisfy the displayed construction; no edge-case counterexample was found.

**Changes.** None. The split is mathematically sound and already has complete citation and search records; no file required repair.

## Validation

The required handoff gate is `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q61 lem-pod-coefficient-dual-perfect --no-push`. The worker issues READY only when that command prints OK. Its server preflight includes `check_dag` and `review_split`; those tools are never run locally. A standalone server `review_split` request was also submitted before the report was written. A read-only local audit verified all 37 verbatim quotes, the proof-use union, and absence of a dependency path back to the item. No push is authorized for this first-reader handoff.
