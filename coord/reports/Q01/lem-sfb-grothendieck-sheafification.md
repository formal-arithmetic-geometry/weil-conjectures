## Worker report

Q01, 2026-10-21. Item: lem-sfb-grothendieck-sheafification. Stage 1 only; the shared repository and Lean source were read without editing, and no compiler, Lake, build or agent was started.

## Files written

- dag/nodes/sec-proetale-coefficients/lem-sfb-grothendieck-sheafification.json: existing statement unchanged; five-step split.
- lem-sfb-transfinite-plus-sheaf-convergence: statement; no Mathlib match for the specified transfinite construction with nonconcrete Grothendieck coefficients; unsplit.
- lem-sfb-transfinite-plus-sheaf-orthogonality: statement; no Mathlib match for orthogonality of the specified transfinite unit without already assuming sheafification; unsplit.
- lem-sfb-transfinite-plus-finite-limits: statement; no Mathlib match for this transfinite sheaf-valued construction without concrete forgetful-functor assumptions; unsplit.
- lem-sfb-abelian-sheaves-left-exact-reflector: statement; Mathlib leaf, CategoryTheory.sheafIsAbelian at Mathlib/CategoryTheory/Sites/Abelian.lean:40-42, using HasSheafify.mk' at Sites/Sheafification.lean:57-63 to package the supplied reflector.
- citations.json: an exact quotation of each statement used at each of the five numbered steps.

The three unsplit helpers carry statements only, with no proof steps or proof dependencies. Their plus construction, transition maps and transfinite iteration are spelled out, and every object, universe and bound is introduced in each statement independently. Supporting source declarations are identified below for the maintainer's attachment audit; I have not claimed transitive closure from reading a proof body.

## Attachments

No attachment of the item is claimed. CategoryTheory.GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian at lean/WeilConjectures/CategoryTheory/GrothendieckAbelian/HasSheafify.lean:61-65 proves the left-adjoint existence and finite-limit preservation clauses. HasSheafify does not include the item's final assertion that the sheaf category is abelian. That clause is supplied by the separate Mathlib instance; the brief excludes a partial attachment. The old candidate's line range 54-65 begins at its docstring; the current theorem starts at line 61.

The existing attachment CategoryTheory.IsGrothendieckAbelian.isLocallyPresentable belongs to lem-coef-grothendieck-locally-presentable and is reused; its current DAG audit is closed. Supporting candidates for independent maintainer checking are:

- CategoryTheory.GrothendieckTopology.isSheaf_transfinitePlus_obj_of_isSeparator, TransfinitePlusSheaf.lean:107-111, for lem-sfb-transfinite-plus-sheaf-convergence.
- CategoryTheory.GrothendieckTopology.W_toTransfinitePlus_app, TransfinitePlus.lean:173-178, with the definition of W, for lem-sfb-transfinite-plus-sheaf-orthogonality. Naturality is that of precomposition with the natural transformation toTransfinitePlus.
- CategoryTheory.GrothendieckTopology.preservesFiniteLimits_transfinitePlusSheaf, TransfinitePlusSheaf.lean:153-157, specialized with hG.isDetector, for lem-sfb-transfinite-plus-finite-limits.

## Literature and searches

WANTED: none. The current blueprint's lem-sfb-finite-upper-star-exact.proof.md, first paragraph, asserts left exact sheafification for Grothendieck abelian coefficients. I read Stacks Tag 00WJ, sites.tex, lemma-sheafification-exact, including its proof: it treats sets, so it is a prototype and is not falsely cited as the arbitrary-coefficient theorem. The general-coefficient proof is expanded from the existing project sources HasSheafify.lean, TransfinitePlus.lean and TransfinitePlusSheaf.lean. The named project's construction is the concrete mathematical construction followed here; the main split's proof_origin is agent, since this is an expansion of project and blueprint material. No SGA source is used.

For abelianness I read Stacks Tag 03A3, homology.tex, lemma-adjoint-get-abelian, and Mathlib's exact sheaf specialization. Unlike sheafification existence, this implication does not assume Grothendieck coefficients. For the other helpers there is no claimed Stacks tag for the transfinite, nonconcrete statement; their primary sources are the precise project declarations, rather than an inaccurate citation of the set-valued Stacks lemma.

Every new node was searched with msearch.py using LeanFinder, Loogle, grep and LeanSearch. All services answered in this run. Full answers are preserved in the sandbox's *-leanfinder.txt, *-loogle.txt, *-grep.txt and *-leansearch.txt files, with searches.jsonl as the tool-written record. Each negative helper has a second semantic phrasing actually run and read. The matches for plusLift/plusLift_unique concern one plus step; W_toSheafify presupposes a reflector. ConcreteSheafification.isSheaf_plus_plus and Sites/LeftExact's plus preservation carry concrete forgetful-functor hypotheses, which this item does not have. Generic transfinite iteration does not supply those missing hypotheses. The abelianness node records the exact positive match and source lines read. Existing item searches were retained, with the current actual searches appended.

I searched the whole DAG for the item tag and notions, the project declaration names, transfinitePlus, W_toTransfinitePlus, preservesFiniteLimits_transfinitePlus, sheafIsAbelian, abelianOfAdjunction, Tag 03A3 and adjoint-get-abelian. Whole-blueprint searches used blueprint_refs.py search with sheafification, transfinite, transfinite plus, 03A3 and sheaves abelian (the broad plus search was also inspected). No existing node states any of the four helper statements. The already existing locally-presentable, object-rank and common-regular-bound nodes are cited. blueprint_refs.py ancestor confirms lem-sfb-finite-upper-star-exact; each helper has via = [lem-sfb-grothendieck-sheafification] and an exact first-paragraph place.

## Not duplicates

lem-sfb-transfinite-plus-sheaf-convergence vs lem-sfb-grothendieck-sheafification: convergence of a specified ordinal iteration at a fixed generator/site bound is the intermediate sheafness test; it asserts neither an adjunction nor left exactness nor abelianness.

lem-sfb-transfinite-plus-sheaf-orthogonality vs lem-sfb-grothendieck-sheafification: its conclusion concerns maps from a specified iteration into existing sheaves for every regular cardinal; it does not assert the iteration is a sheaf, nor the existence of a sheaf-valued left adjoint.

lem-sfb-transfinite-plus-finite-limits vs lem-sfb-grothendieck-sheafification: it identifies finite-limit preservation for the specified transfinite construction with fixed additional generator/cardinal data; no universal mapping property or abelianness is asserted. Convergence, universal mapping and exactness are independent construction properties, not renamed existential clauses.

lem-sfb-abelian-sheaves-left-exact-reflector vs lem-sfb-grothendieck-sheafification: the former assumes a given left exact reflector and only requires an abelian coefficient category; the item must construct that reflector from Grothendieck hypotheses. The implication is an exact Mathlib leaf.

lem-sfb-abelian-sheaves-left-exact-reflector vs def-pur-abelian-sheaf-kernel: that existing node describes sectionwise kernels only for abelian-group-valued sheaves. It does not assert the conditional abelianness theorem for arbitrary abelian coefficients.

## Problems corrected or retained

No statement dispute was found. The item remains verbatim; no hypothesis is added and no conclusion is removed. The prototype citation 00WJ is explicitly distinguished from the nonconcrete generalization. A project theorem covering only two clauses is not treated as a complete attachment. No chapter or unit route or binding was changed; this auxiliary node is not the unit's key statement.

## Review by Q01

I read the current unit and chapter records, the current blueprint proof's first paragraph, Stacks 00WJ and 03A3 in their actual .tex sources, the exact project declarations listed above and the relevant Mathlib definitions. The three-level route is respected: this node expands the sheafification factor of the unit's pullback construction, rather than replacing its Kan-extension route.

Step 1 uses def-sp-grothendieck-abelian for a generator and the coefficient assumptions, lem-coef-grothendieck-locally-presentable for local presentability, lem-coef-object-presentability-rank for presentability of this particular generator, and lem-coef-small-family-regular-bound for a bound on the two small sets. I opened all four statements. The object-rank lemma assumes precisely the family formulation supplied by the locally-presentable node. The regular-bound lemma permits a two-element family, so the disjoint union simultaneously bounds the site's total morphism set and the initial ordinal of the rank. The only enlargement argument is elementary: every diagram with fewer than kappa_0 morphisms has fewer than kappa morphisms. No unbounded diagram category or change of coefficient universe occurs.

Step 2 uses precisely the convergence helper's conclusion that Q_kappa(P) satisfies the Hom(T,-) sheaf condition. I checked isSheaf_transfinitePlus_obj_of_isSeparator at lines 107-111 and the section hypotheses preceding it. A generator is the separator, the Hom universe equals the site's universe, and the cardinal bound is on Arrow C, i.e. all morphisms, not merely objects. The plus formula uses covering sieves ordered oppositely, so refinements induce restriction maps from larger to smaller matching families. The transfinite maps start at the identity and take actual colimits at nonzero limit stages. The helper's statement includes these data; this step does not borrow them from an unstated proof. All indexing collections lie in V, including the power set of arrows used for the covering-sieve poset. That poset need not have cardinal less than kappa; the convergence theorem bounds each matching diagram using Arrow C, not the number of covering sieves.

Step 3 uses the orthogonality helper for a natural Hom bijection and def-weil-pbc-sheafification only for its universal-property definition. Reading TransfinitePlus.lean:173-178 and the definition of J.W confirms that the property is precomposition bijectivity into every sheaf, not a conclusion about the unit being pointwise invertible. Naturality follows by composing with the natural unit, and fullness identifies the source Hom set with sheaf morphisms. This helper assumes neither convergence nor HasWeakSheafify: it can be applied before the desired reflector is available. The universal property therefore is not circular.

Step 4 uses the finite-limits helper's statement about the corestriction, not just its underlying presheaf endofunctor. I checked TransfinitePlusSheaf.lean:153-157, its section hypotheses, TransfinitePlus.lean:149-167, and the project's nonconcrete LeftExact.lean:150-157. AB5 and the same small-colimit size are supplied by the original Grothendieck assumption; no concrete forgetful functor is silently assumed. The fixed G and kappa used in steps 1-2 are exactly the inputs of that helper, so the functor is the one already constructed. No new uniqueness-of-reflector comparison is hidden here.

Step 5 uses def-sp-grothendieck-abelian for the abelian hypothesis and the conditional abelianness helper. I checked Mathlib Sites/Abelian.lean:30-42 and Sites/Sheafification.lean:45-63: HasSheafify packages both a left adjoint and finite-limit preservation; HasSheafify.mk' accepts the functor of steps 2-4; sheafIsAbelian then requires no further condition. The actual category of coefficients and Hom-tested definition of a sheaf agree on both sides. The helper's primary Stacks source is 03A3, not the set-valued 00WJ.

For each new node I checked B1-B7: independent objects and hypotheses, inline definitions for regularity, presentability, matching objects and transfinite iteration, definition dependencies, normal TeX escaping, accurate source declarations, and empty proof arrays for the three unsplit helpers. Small cases checked were the empty base category (vacuous sheaf condition and unique functors), the zero abelian category and zero generator (the category is trivial and convergence still holds), the coarsest topology (the plus maps are identities up to their canonical isomorphisms), and arbitrary empty covers (matching objects are terminal, not omitted). Kappa is required infinite regular, so a zero or finite iteration is never being used as the convergence stage. The orthogonality helper deliberately has no size bound on kappa relative to C and does not falsely assert convergence in that case. The conditional Mathlib leaf does not assume Grothendieckness, existence of a generator, or an already proved instance from this item.

Against C1-C4, every non-elementary use in each main step is a cited statement with a verbatim quote in citations.json; none uses an argument hidden in another node's proof. Against D1-D4, the main proof carries the rank choice, corestriction, Hom identification and application of the abelian reflection theorem, while its helpers separate the actual transfinite construction's convergence, orthogonality and limit behavior. It is not a one-line application of a replacement node stating the item. No new helper depends on the item. Against E, all size, generator and preservation hypotheses are checked above; in particular neither P++ convergence nor preservation by Hom(G,-) of all filtered colimits is asserted. The longest main step is 814 characters, so there is no step over the 2000-character long-step threshold.

No second worker was requested by this direct-delivery brief. This is my own content review and signature; the maintainer's independent review remains required. No work remains unfinished beyond the intentionally statement-only helper nodes and the normal independent attachment/merge audit.

## Validation

The first required server dry run rejected one metadata omission: the positive Mathlib match needed a numeric line field in addition to its textual source range. I rechecked Sites/Abelian.lean:40 and added mathlib_match.line = 40. The second server dry run exited successfully: OK (not pushed) deliver/Q01/lem-sfb-grothendieck-sheafification at 1954a1f40a1, preflight passed. This invocation finished before the push invocation. A sandbox JSON/quote audit also confirmed the unchanged item statement, five valid node files, exact citation substrings, and statement-only new helpers. No local check_dag.py, review_split.py or preflight_delivery.py is run.
