# Stage-1 report: lem-trf-coinduction-bounded-injective-model

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-coinduction-bounded-injective-model.json`: item, statement; split in five steps, not a Mathlib leaf. The original statement, statement dependencies, source, created record and blueprint ancestry are retained. Original Q85 searches are retained, and seven actual Q93 searches are appended.
- `citations.json`: five entries, one for each use in the numbered proof steps, each checked as an exact substring of the cited statement.
- `report.md`: this report.
- `searches.jsonl`: log maintained by the required msearch command.

New nodes: 0. New Mathlib leaves: 0. The proof uses existing Mathlib leaves for the three non-elementary inputs instead of creating duplicate nodes.

## Attachments

None. Searched `lean/WeilConjectures/` for the blueprint item tag and coinduction/coextendScalars, and for bounded injective models. The existing sheaf coinduction declarations and coefficient restriction constructions do not state this ordinary-module bounded-model theorem with every clause. Mathlib's ordinary coextension functor is an input, not a project attachment.

## WANTED

None: all sources used are present locally.

## Corrections and scope

The item was unsplit, with an empty proof. No statement correction or STATEMENT-DISPUTED is needed. Stacks Tag 0AX0 assumes a finite map of Noetherian rings for its full dualizing-complex conclusion, but its first proof paragraph about a bounded Hom model uses only the bounded injective resolution and Tag 08XR; the present item is precisely that paragraph, not the rest of the dualizing theorem. Tags 08XR and 0A70 are valid for arbitrary ring maps. No finiteness, flatness or scalar-action-isomorphism hypothesis is imported into the proof.

Read GOAL.md, the three levels in SETUP.md, the item chapter and unit records, and the latest blueprint chapter, unit and ancestor `lem-trf-local-term-locality.md`. This algebraic auxiliary input remains under the existing ancestor/via chain of the nearby-cycle branch. No unit or chapter record is changed. `blueprint_refs.py ancestor` agrees with the existing ancestry. Whole-blueprint searches for `coinduction` and `bounded below injective` give no equivalent statement of the entire item; same_as stays empty.

The global DAG search found existing general lemmas `lem-exc-rg-right-adjoint-preserves-injectives`, `lem-weil-pbc-bounded-below-injectives-kinjective` and `lem-weil-pbc-kinjective-hom-derived`, as well as `def-trf-derived-coinduction`. None depends transitively on this item (checked by reading the dependency graph). The first three are Mathlib leaves. The last is a definition and its statement explicitly describes the K-injective coinduction construction, so it is legitimate here without an off-unit theorem tool declaration.

## Mathlib search results

Read all seven Q93 search responses recorded in searches.jsonl. LeanSearch returns `ModuleCat.coextendScalars`, its object and map descriptions and `ModuleCat.restrictCoextendScalarsAdj`. LeanFinder returns `CochainComplex.isKInjective_of_injective` and resolution/Ext infrastructure. The second phrasing returns exact-functor maps on Ext, finite-degree right-derived functors and derived-category infrastructure. Loogle's combined coextension/injectivity query returns no hits; its K-injective query gives the bounded-below injective theorem. The second grep has only an unrelated coinductive-computation hit.

Read `Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean` at the action, coextension object/map and adjunction formulas, `Mathlib/Algebra/Homology/HomotopyCategory/KInjective.lean` at `CochainComplex.isKInjective_of_injective` (line 133), and `Mathlib/Algebra/Homology/DerivedCategory/KInjective.lean` at `CochainComplex.IsKInjective.Qh_map_bijective` (line 41) and `quasiIso_iff` (line 52). These supply the ingredients but no search hit states all clauses of the item in one theorem or a one-line specialization. No services were unavailable in this session.

## Not duplicates

No new nodes, hence no new/existing pairs. In particular no node is created for the ordinary adjunction, preservation of injectives, bounded-below K-injectivity, or K-injective comparison. The elementary module-action, support and Hom-differential calculations remain proof steps.

## Review by Q93

I read `literature/stacks-project/dualizing.tex` at Tag 08XR (lemma-hom-injective and proof), the construction immediately before Tag 0A70 (lemma-right-adjoint), and the first proof paragraph of Tag 0AX0 (lemma-dualizing-finite). I also read `derived.tex` at Tags 070I (lemma-K-injective) and 070J (lemma-bounded-below-injectives-K-injective), and `homology.tex` at Tag 015Z (lemma-adjoint-preserve-injectives), including its adjunction-based extension argument. There are no new-node sources to audit.

Step 1 uses no external theorem: the B-action, B-linearity of postcomposition and of the differential, square-zero identity and vanishing outside [a,b] are checked explicitly. In particular no exactness of Hom_A(B,-) is assumed.

Step 2 uses exactly the statement of `lem-exc-rg-right-adjoint-preserves-injectives`: a right adjoint of a monomorphism-preserving functor carries injectives to injectives. I opened its statement. The step verifies its hypotheses by writing both evaluation/transpose formulas, their inverse identity and naturality, and observing that restriction leaves the underlying injective module map unchanged. Its categories are C=B-Mod and D=A-Mod, so the output is B-injectivity of each Hom_A(B,I^q), not A-injectivity and not a claim that restriction preserves injectives.

Step 3 uses exactly the statement of `lem-weil-pbc-bounded-below-injectives-kinjective`. I opened it and checked that it permits every abelian category and an arbitrary integer lower bound. The lower bound here is a and every term is injective by hypothesis. No Grothendieck-category or enough-injectives assumption is needed for this application.

Step 4 uses the statement of `def-trf-derived-coinduction` only for its specified K-injective representative and B-action construction. I opened that statement and checked that its rings and unbounded ordinary module categories agree after renaming R to A. The non-elementary comparison input is the Hom bijection in `lem-weil-pbc-kinjective-hom-derived`, whose statement I also opened. I and T are both K-injective, so that bijection applies with each as target. The step constructs the two lifted homotopy classes, deduces inverse identities by injectivity of the bijection, and writes the postcomposed homotopy equation. This makes the inverse B-linear before localization. Uniqueness and composition of lifts give canonicity; no unproved compatibility is hidden in the word canonical.

Step 5 uses the last sentence of `def-pur-derived-internal-hom`, which permits any K-injective representative and gives its canonical comparison. I opened the full statement and its explicit product Hom differential. With source B[0] only the p=0 factor survives, and the source differential vanishes. Thus forgetting the action gives the usual Hom complex and the very same postcomposition comparison used in Step 4. This proves the requested normalization in D(A) from the actual map, rather than inferring a B-derived comparison from an A-derived isomorphism.

I checked B-E of delivery-errors point by point. There are no new statement-only nodes, no data or proof sketches hidden in a new statement, no new notions without definitions, and no source hypotheses missing. Each non-elementary input is a cited node, each citation quotes the statement rather than the proof, and proof_deps equals the union of uses. No item clause is restated as a new lemma. All proof steps are below 2000 characters, so none hides a long subsidiary lemma. No forbidden source route is used.

For edge cases, f=id_A gives the evaluation-at-1 identification Hom_A(A,I)=I; B=0 and I=0 give the zero complex and zero derived object; a=b gives a one-term injective complex in any integer degree, including negative degrees; and Z to Z/2 tests that no flatness is required. The adjunction extension argument works unchanged in each case. The differential formula has no extra sign because the source is concentrated in degree zero. The original isomorphism QI to L is retained as part of the comparison data, so no unique absolute isomorphism is claimed without that choice.

## Unfinished work

None in the stage-1 split. No Lean files were written and no compiler, Lake or build command was run. The independent maintainer review remains the normal next project step after delivery.
