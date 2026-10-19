# Q120 — lem-weil-pbc-localization-inverse-image-coherence

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-localization-inverse-image-coherence.json`: statement, split; eleven proof steps, reusing existing dependencies. The statement and its five statement dependencies are unchanged. The item is not a Mathlib leaf.
- `citations.json`: 32 entries, one for every step/dependency pair, copied verbatim from the cited statements.
- `searches.jsonl`: five new executed searches, retaining their actual results; the item's previous Q57 search records remain in the node. This report and the sandbox-only generation script are auxiliary files.

New nodes: 0. New Mathlib leaves: 0. No unit or chapter file changed.

## Attachments

None. I searched the entire read-only slopmaster2 `WeilConjectures/` tree for the exact blueprint tag, for localization/inverse-image combinations, and for geometric/localization combinations. No declaration states this item. The ordinary algebra in `WeilConjectures/RingTheory/TensorLocalizationAway.lean` concerns tensor products with localized polynomial rings; the derived rationalization files concern localization of linear categories, and the etale derived Localization file concerns support triangles. None supplies this sheaf scalar-localization assertion and all its coherence clauses. The recorded item has no attached Lean declaration. Upstream master was not treated as finished evidence.

## WANTED

None. All sources used are in the repository.

## What needed repair

The item was statement-only. Its extracted source reference to 03EL and 03CZ does not itself prove exactness or the specified identity, composition, coefficient-identification and unbounded derived equations. I supplied those arguments without changing the statement. The proof uses the universal property of actual sheafified fractions; it does not replace the localization with an unspecified isomorphic object.

I found a source-label error in an existing dependency: `lem-weil-pbc-localization-tensor` calls 00DE “tensor-product-localization”. In the checked Stacks tag table, 00DE is `algebra-lemma-hom-from-tensor-product`; 00DL is `algebra-lemma-tensor-product-localization`, and the module comparison actually used here is 00DK, `algebra-lemma-tensor-localization`. I read the latter proof in algebra.tex and cite 00DK in this item's step 1. The dependency's mathematical statement supplies exactly the module comparison used; I did not edit its file.

The shared local DAG also contains an unrelated invalid JSON file, `dag/nodes/sec-six-functors/lem-coef-terminal-local-kan-corepresentability.json` (Extra data at line 261, column 2), observed twice during whole-DAG searches. I left it untouched and continued using the permitted server checks, which judge the server delivery overlay.

## What could not be finished

Nothing. The mathematical split is complete; server validation is recorded below.

## Not duplicates

No new nodes were created. Whole-DAG searches by titles, localization, inverse image, sheafification, tensor products, exact functors, and Stacks tags 03EL and 03CZ located existing ingredients. Blueprint ancestor search returns `thm-weil-pbc-finite-extension`. Whole-blueprint searches for “localization inverse image”, “localization inverse”, “localization scalar”, and “localization section” return no equivalent blueprint node. Broader localization and inverse-image searches locate coefficient rationalization, support localization and site-specific pullbacks; these do not state the current arbitrary-geometric-morphism assertion. The item's `same_as` remains `[]`, and its existing ancestry and specific place are retained.

## Mathlib searches

I ran every following search with the required Q120 msearch command; their exact queries, times and result digests are in `searches.jsonl`, and their query texts and verdicts are appended to the item:

1. LeanFinder: “For a geometric morphism of sheaf topoi the exact inverse image of modules commutes with localization at a global ring section naturally and coherently with composition”. It returned site-induced pullback composition, units and free-module comparisons.
2. Loogle: `"Sheaf", "localization"`. It returned sheafification as a categorical localization, structure-sheaf localizations and TopCat localization presheaves.
3. LeanSearch: “Inverse image of a sheaf of modules localized at powers of a global section is the localization of its inverse image”. It returned affine basic-open and stalk localizations.
4. Mathlib grep: `(localiz.*(inverseImage|pullback)|(inverseImage|pullback).*localiz)`. Its sheaf hit is sheafification as a categorical localization; the other hits concern localizer morphisms, derived localization and affine scheme geometry.
5. LeanFinder, second phrasing: “Pullback of ring sheaves and module sheaves commutes with inverting an element by the universal property of localization”. It returned free-module/unit pullback and site-induced composition comparisons.

I read the sheaf-localization file and the pullback-composition definitions in Mathlib/Algebra/Category/ModuleCat/Sheaf. The former inverts sheafification equivalences, not a scalar; the latter assumes a continuous functor of specified sites and does not supply scalar localization. No hit states the whole item, including arbitrary geometric morphisms and the unbounded derived coherence equations. All five services/searches completed successfully; none is recorded as unavailable.

## Review by Q120

I read the stage-1 brief, the full B–E error checklist, the three blueprint levels in SETUP, the proper-base-change chapter and unit, GOAL and dag-sync. I read the current main-20261015 finite-extension statement and proof: this lemma serves its rationalization and final coherence sentence through the recorded condensed-E realization ancestry. It changes neither the chapter route nor the unit's proper-base-change reduction. I read sites-modules.tex at 03CY, 03D2/03D3, 03D7, 03DA/03DB, 03EK/0GMW/03EL and 04JC; sites.tex at 00YV; algebra.tex at 00CP, 07JZ, 00CS and 00DK; and derived.tex at 015F. No source outside the allowed route is used, and no SGA source is used. There are no new-node sources to review.

For each citation I opened the actual node statement. I deliberately did not cite the etale-only or topological-space-only inverse-image exactness nodes for a general geometric morphism. Likewise I used the general ringed-site sheafification theorem, not its Zariski-scheme or constant-coefficient specializations. Here is what each step takes and why its hypotheses apply:

1. The localization definition is the sheafification of actual sectionwise ring localizations. The sheafification–tensor statement gives precisely the comparison between sheafified tensor factors and the tensor presheaf. The ordinary tensor-localization node gives its module clause with the formula `(r/s^e) tensor n -> rn/s^e`. The underlying-set sheafification node and module-sheafification definition identify the underlying sheaves and the units. All concern arbitrary sites/rings; neither quasi-coherence nor a scheme hypothesis is introduced. This is a direct specialization of the cited comparisons, so it is elementary. I declare the general sheafification–tensor theorem as a tool use from another unit; no lemma of this unit supplies that comparison.
2. The ordinary ring-localization node gives existence, uniqueness and the exact fraction formula. The ring-sheafification universal property and its underlying-set comparison extend it. Restriction compatibility follows from that same uniqueness, not from any unquoted theorem. This step proves the sheaf mapping property explicitly instead of making it a new node.
3. The module-localization definition states the fraction equivalence relation. I used that relation to verify the extension formula, writing the power that cancels, and then used exactly the module-sheafification adjunction from its definition. Thus the initial property and localized linearity are elementary consequences with the argument present, not an uncited module universal-property theorem.
4. The group/ring-object adjunction node explicitly covers arbitrary finite-product-preserving adjunctions, and the algebraic-sheaf equivalence node identifies its objects and morphisms with sheaves of rings. Finite limits of the given inverse image supply finite products. I checked the invertibility equivalence on global sections in both directions: inverse sections correspond through the adjunction because multiplication and one correspond. The two universal maps have identity composites by the previously proved uniqueness. No existence of points or a site-functor presentation is needed.
5. The geometric-module-transport statement supplies both the module adjunction and the scalar-action formula through the adjunction unit. I take its coefficient map to be the identity of the inverse-image ring; it is a commutative ring-sheaf map with no extra flatness premise. That formula identifies the action of t on the direct image with direct image of the action of t prime. Thus the middle extension bijection has its needed invertibility hypothesis. The inverse pair of comparison maps is constructed, its localization-unit equation is written, and its localized-ring linearity follows from step 3.
6. I verified naturality by the two unit restrictions and the uniqueness just established. For fractions I apply inverse image to the multiplication equation, using the transported-action assertion of the cited module node and the multiplication transport in the cited ring node. Representatives may be arrows from sheafified representables; I do not identify arbitrary inverse image with restriction. The normalization therefore has a mathematical argument even when there are no enough-points hypotheses.
7. The module transport supplies the underlying functor and transported zero/addition. Kernels are finite-limit equalizers; the module limit and forgetful node states the sectionwise limit and exactness facts used. The adjunction plus the left-adjoint-colimit node preserves the finite cokernel diagrams. Those diagrams are small, so no smallness hypothesis is lost. This is a few-line exactness deduction from the hypotheses and those statements.
8. The ordinary localization-exactness node applies to the sectionwise sequence defining a kernel, which really is exact on sections. The general ringed-site sheafification node states exactness, so it gives the kernel after sheafification. For cokernels the general ringed-topoi module adjunction applies to the identity geometric morphism with the localization coefficient map; its actual tensor pullback is the scalar functor in the item. Left adjoints preserve those cokernels. The exact forgetful node checks both coefficient interpretations. I avoided the false claim that arbitrary short exact sequences of sheaves are exact on every section group.
9. The composite-adjunction definition provides the composite and identity units, and the conjugate-isomorphism statement gives the unique unit-normalized comparison. I checked both displayed routes after precomposition with the pulled localization unit: they equal the same final unit. The initial property established in step 5 then forces equality. Ring comparisons satisfy the analogous restriction condition. Thus the coherence is an equation of natural transformations, not just objectwise existence of unspecified isomorphisms.
10. The localization universal-property node supplies the induced map for c and for its inverse. Its fraction formula verifies the scalar-section correspondence. On modules the coefficients are reinterpreted by c inverse, so the invertible scalar and localization units agree. The same unit-uniqueness calculation proves the coefficient-identification square, without imposing an extra coefficient category.
11. The exact-functor factorization node explicitly concerns unbounded cochain complexes and preservation of quasi-isomorphisms. The exact-functor-derived-functor node identifies the induced functor with both derived functors. The localization-universal-property node explicitly supplies lifting, uniqueness, identity/composition preservation and faithfulness for natural transformations. Those are precisely the clauses needed to descend the degreewise chain isomorphism and its equations. I do not use bounded-below resolutions to justify an unbounded assertion.

I tested the edge cases R=0, M=0, t=1, t=0, nilpotent t, t a zero divisor, and the identity morphism. Localization is permitted to be the zero ring/module; all fraction maps and uniqueness arguments remain valid. No cancellation of t in the original ring or module is used: cancellation occurs only on a target on which t is explicitly invertible. For t=1 the unit comparisons reduce to identity; for t=0 or nilpotent t all localized modules are zero. For an isomorphism of coefficient rings I checked both inverse maps, and for f and g I checked the order g inverse after f inverse and both localization-unit equations. I also checked an arbitrary unbounded complex: naturality commutes with every differential, and exactness handles all quasi-isomorphisms without a common lower bound.

Against B–E: every node cited exists and its statement is the quoted source of the use; no new nodes are self-restatements, elementary facts, or duplicates; no proof was hidden inside a new statement. The statement remains self-contained and uses its existing notion nodes. Mathematical hypotheses were checked as above, and all non-elementary work is either a cited statement or the explicit argument within this item's steps. All eleven steps are below 2000 characters (maximum 1470); I reread them for hidden comparison or identification claims, and the unit and fraction arguments are written explicitly. The source-label issue was corrected in this item's citations and reported without editing another worker's node. No Lean, compiler, Lake, live-project write, launcher write, or manual git operation was used.

## Validation

- Server `review_split`: PASS, 0 new nodes, proof written by an agent.
- Server `check_dag`: OK, no finding introduced by the sandbox or on its nodes.
- Full `deliver.py --no-push` exited 0 and printed OK (not pushed), with preflight passed at dry-run commit e79123efdb. A final dry run follows this validation-note update, before direct delivery as authorized in the brief.
