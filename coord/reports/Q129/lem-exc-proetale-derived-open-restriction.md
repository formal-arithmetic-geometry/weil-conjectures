# Q129 — lem-exc-proetale-derived-open-restriction

## Files written

- dag/nodes/sec-smooth-purity/lem-exc-proetale-derived-open-restriction.json: statement, split into five proof steps; no Mathlib match for the full item.
- citations.json: fourteen verbatim statement quotations, one for each step/node citation.
- report.md: this report.

Zero new nodes and zero Mathlib leaves. The sandbox initially contained no node or earlier split/report. Existing Q87 search records on the repository item were retained; the five new searches and their actual results are in searches.jsonl and appended to the item. No Lean was written or compiled.

## Attachments

None. Searched the full WeilConjectures tree for the blueprint id and for restriction terminology, then read SixFunctors/ProEtale/BaseChange/WeaklyEtale.lean and LowerShriek/OpenImmersion/Defs.lean. AlgebraicGeometry.ProEtale.isIso_baseChangeMap_of_isPullback proves an underived weakly-etale comparison for category-valued sheaves. It does not give the unbounded derived statement, K-injective preservation, or the extension-by-zero clause. Thus it is not an exact attachment. No master sorry declaration is treated as finished.

## WANTED

None: all sources used are present in literature/stacks-project/.

## Corrections and scope

The imported statement is correct as written: no mathematical hypothesis or conclusion has been changed. Added explicit references to the K-injective definition and the already-existing open-unit node. Filled its empty proof and proof-dependency list, preserving its chapter, unit, creation data, original source and blueprint ancestry.

The retained repaired ancestor DAG prop-exc-base-change-proper, step 3, contains the open-restriction obligation. The current main-20261015 blueprint proof instead presents a dual-base-change sketch and does not itself state this general unbounded pro-etale comparison. The source attribution therefore remains an agent-extracted argument supported by the cited Stacks results, rather than attributing a pro-etale theorem to an etale source. The unit is sk-prop-sf-existence and this node is not its key statement; no unit record is changed.

The old blueprint lem-weil-pbc-derived-open-restriction concerns D^+ on the etale site, not unbounded pro-etale coefficients. The existing lem-sc-derived-k-injective-restrict-open is about ringed spaces. Neither is a replacement for the item. The general right-adjoint/K-injective lemma already exists as lem-weil-pbc-right-adjoint-preserves-kinjective and is reused. No fact was duplicated as a new node or extracted as a renamed clause.

## Searches and Mathlib verdict

Ran the required msearch.py commands with Q129 and this item: LeanFinder in two phrasings (unbounded pro-etale pushforward/open restriction and derived image/localization/K-injectives), Loogle for "KInjective", "map", grep for open/base-change/derived-restriction in CategoryTheory, and LeanSearch for derived direct image/open restriction. All returned successfully. Read the hits: Scheme.Modules.pushforward_obj_obj, restrictAdjunction and restrictFunctorAdjCounitIso in Mathlib/AlgebraicGeometry/Modules/Sheaf.lean concern modules over the structure sheaf on Zariski opens; CochainComplex.IsKInjective.Qh_map_bijective in Algebra/Homology/DerivedCategory/KInjective.lean is only a generic derived Hom computation; Presheaf.isLocallyInjective_whisker and related hits concern local injectivity of presheaf maps, not K-injective complexes. These are not one-line specializations yielding the full item. The grep returned zero hits. No unavailable service was labelled absent.

Searched the DAG by tags 08BJ and 09BN and by K-injective/open-restriction language, and ran blueprint_refs.py ancestor and searches for open restriction, K-injective, open immersion and direct image. The five proof steps use existing statements only. same_as is empty because no imported blueprint node gives this full unbounded pro-etale assertion.

## Not duplicates

No new nodes. In particular, no new localization, exact-adjoint, K-injective-computation, or open-unit lemma was introduced.

## Review by Q129

I read the item, its chapter and sk-prop-sf-existence unit, the current main-20261015 prop-exc-base-change-proper proof, and the retained repaired ancestor DAG. I checked the sources in proetale.tex (lemma-morphism-big-small, Definition 09AE, Lemma 09BN), sites-modules.tex (03DJ and restrict-back), derived.tex (08BJ, 070I, 070K, 070Y), sites-cohomology.tex (08FI), and injectives.tex (079P). There are no new-node sources to audit. The proof is marked agent-written because it combines these results into the precise small-site statement, rather than following an existing theorem with identical wording.

For step 1 I opened lem-weil-proetale-weakly-etale-localization: its clauses identify the slice site, the restricted constant ring, and sectionwise restriction. The statement of def-weil-pbc-proetale-operations explicitly gives the section formula for direct image. The statement of def-pc-fibre-product gives the Cartesian universal property, so the two objects V×_T Q and U×_W Q are canonically identified over V. I wrote out the equality of restriction maps, module actions and maps of F. This is a direct three-line section calculation from those statements, not a hidden base-change lemma. No stalk conservativity, properness, finite presentation or quasi-compactness enters.

For step 2 I opened both extension-by-zero lemmas: one gives exactly k_! left adjoint to restriction, and the other gives exactness for finite commutative coefficients and arbitrary opens. These are the hypotheses of the existing abstract right-adjoint-preserves-K-injective statement. I checked the variance: its u is k^* from modules on V to modules on U; its v is k_! in the reverse direction. Stacks 08BJ and the ringed-site version 08FI support this application. This proves the necessary preservation claim without introducing a node restating that clause of the item.

For step 3 I read prop-pur-kinjective-resolutions-exist, which supplies functorial unbounded resolutions for module sheaves on a small ringed site. The explicit small-skeleton convention of def-weil-pbc-proetale-site meets its size hypothesis. The operations node states exact inverse image and the uncompleted K-injective construction of right derived image. The generic total-derived node says that EVERY K-injective computes the right derived functor; this matters because k^*I is not the specifically chosen resolution on U. I checked the exact-functor hypothesis on the homotopy category: termwise additive direct image preserves cone triangles and shifts. Thus the displayed comparison is a degreewise isomorphism, with its prescribed sectionwise normalization, on precisely the representatives that compute both sides.

For step 4 I read the full statement of lem-weil-pbc-kinjective-hom-derived. It supplies representatives of all derived morphisms into J, uniqueness up to homotopy, and the homotopy-equivalence assertion for replacement. I wrote the commuting square as equality of the same section maps and wrote how the equation f-g=dh+hd is preserved; this proves naturality and resolution independence rather than asserting them without an argument.

For step 5 I read lem-exc-proetale-open-unit, which states that the actual adjunction unit M→k^*k_!M is invertible. Stacks 09BN imposes no quasi-compactness. Exactness of k_! and k^* makes these underived operations act termwise on the derived category; the inverse of the unit is used in the correct direction. I checked that we resolve k_!M on V and never assume extension by zero preserves K-injectives. Composing rho with Rr_* of the inverse unit gives exactly the item's lambda, naturally.

I checked B1–B10: no new statement-only nodes need formatting or definition repairs; all references and searches are actual, and no exact Lean attachment was missed among the located candidates. For C1–C8, every non-elementary input is an existing cited statement, every citation has a verbatim quote, the elementary section calculation is written out, and generic tools from other units are declared in split_report.tool_uses for maintainer review. These tools do not replace the exceptional-adjoint unit route. For D1–D5, the steps contain the argument and add no renamed conclusions. For E1–E7, all sources and category/variance hypotheses were checked; no source error affects the argument. I tested empty W (both derived targets zero), W=T (the identity comparison), p=id (ordinary restriction), zero coefficients/zero complex, and complexes unbounded in both directions. Each reduces to the same calculation, with no induction, convergence, product-exactness or finite-CD assumption. Every proof step is below 2000 characters; none hides a long standard comparison lemma.

## Unfinished work

None in this stage-1 split. The reused unsplit abstract tool remains its own queued obligation; its proof is not moved into this item. Validation and delivery are performed by the mandated server-side dry run and push, not by local checker or git commands.
