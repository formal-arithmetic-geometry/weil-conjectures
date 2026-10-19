# Stage-1 report: lem-coef-algebroid-equivalence-nerve

## Files written

- `dag/nodes/sec-six-functors/lem-coef-algebroid-equivalence-nerve.json`: item, split into 14 steps; statement unchanged; not a Mathlib leaf.
- `dag/nodes/sec-six-functors/lem-coef-segal-space-inner-anodyne-locality.json`: new statement-only prerequisite, unsplit; no Mathlib match.
- `citations.json`: 26 verbatim quotations from the statements used by the item's steps.

No unit or chapter record is changed. The item is not the unit's key statement. `prepare.py` and `cite.py` are sandbox preparation scripts, not project changes.

## Attachments

None. I searched the read-only slopmaster2 `WeilConjectures/` tree for the item's blueprint tag, algebroid/equivalence terminology, equivalence nerves, Segal spaces and inner-anodyne/Segal terminology. No exact project declaration supplies the item or the new prerequisite. The upstream master is not used as finished-proof evidence.

## WANTED

WANTED: Gepner–Haugseng, *Enriched infinity-categories via nonsymmetric infinity-operads*, arXiv:1312.3178v4, Sections 4.3–4.4 and 5.1–5.3, for the item. Read the primary online HTML https://arxiv.org/html/1312.3178v4; no archival copy is present in the repository literature directory.

WANTED: Haugseng, *On the tensor product of enriched infinity-categories*, arXiv:2311.13362v1, Definitions 6.1–6.3, Proposition 6.4 and Corollaries 6.5–6.6, for lem-coef-segal-space-inner-anodyne-locality. Read the primary online HTML https://arxiv.org/html/2311.13362v1; no archival copy is present in literature/.

WANTED: Rezk, *A model for the homotopy theory of homotopy theory*, arXiv:math/9811037, Sections 5–6, Remark 10.2 and Section 11, for the item's inverse-evaluation step and the locality prerequisite. Read the primary online HTML https://arxiv.org/html/math/9811037; no archival copy is present in literature/.

These are infinity-categorical assertions, not results with Stacks tags. No SGA source was used. The proof remains marked agent-origin because it expands the inherited blueprint route using online, unarchived references. I have not downloaded or changed repository literature.

## Corrections and route

The inherited node already had a substantial proof and old searches, but its current status is unsplit. I preserved its statement, source, creation record, blueprint ancestry, import/audit metadata and earlier searches. Its two non-elementary steps longer than 2000 characters contained supporting material that deserved separate treatment. The new locality node states Haugseng Corollary 6.6 at terminal coefficients; the item itself still proves its groupoid property by coarse-nerve attachments and induction. This is not a new node for a clause of the item.

The long coefficient argument had reconstructed a monoidal adjunction and then its assembly on algebroids. The current DAG already states the needed monoidal Yoneda-extension theorem (`lem-coef-operadic-day-convolution`) and relative-adjoint assembly theorem (`lem-coef-cocartesian-relative-right-adjoint`). I use these existing statements instead of creating duplicates. The Cartesian-fibration argument is a direct application of the existing straightening and mapping-fiber theorems to the restriction functor in the definition. Neither `lem-coef-enrichment-change-adjunction` nor `lem-coef-algebroid-object-space-fibration` can be cited here: their dependency closures contain this item. The replacements do not. All 14 final steps are under 2000 characters; the change is substantive extraction/reuse, not subdivision to conceal long arguments.

The source blueprint paragraph is the finite-coefficient mapping-complex adjunction in `prop-coef-integral-exceptional-adjoint.proof.md`, read in `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/`. I also read the chapter and unit records. This item provides infrastructure underneath the inherited completion/tensor/localization ancestry; it does not replace a unit-level or chapter-level argument. All cited nodes and the new node belong to `sk-prop-sf-biduality-general`; no off-unit tool declaration is needed. There is no statement dispute or target change.

## Not duplicates

lem-coef-segal-space-inner-anodyne-locality vs lem-coef-labelled-spine-prism-horn-calculus: the existing statement gives labelled combinatorial filtrations and a boundary–horn pushout product. It does not state that mapping into every homotopy Segal space inverts inner-anodyne maps.

lem-coef-segal-space-inner-anodyne-locality vs lem-coef-segal-external-local-equivalences: the existing statement gives external-product stability for maps already known to be Segal equivalences. Its proof uses locality, but its statement does not give locality for inner-anodyne maps; I do not cite that proof as a theorem.

lem-coef-segal-space-inner-anodyne-locality vs lem-coef-simple-inner-anodyne-base-change: the existing statement transports inner-anodyne classes through simple presheaf base changes. It does not identify them as Segal equivalences.

lem-coef-segal-space-inner-anodyne-locality vs lem-coef-rezk-local-model: the existing mapping-space detection theorem tests complete Reedy fibrant Segal spaces. The new statement tests arbitrary homotopy Segal objects, without completeness.

lem-coef-segal-space-inner-anodyne-locality vs lem-coef-rezk-explicit-completion: the existing statement constructs a completion and proves its Dwyer–Kan properties. It does not give the required derived mapping-space locality into the original, possibly noncomplete object.

lem-coef-segal-space-inner-anodyne-locality vs lem-coef-complete-segal-dk-levelwise: the existing statement detects levelwise equivalences between complete Segal spaces from Dwyer–Kan conditions. It neither tests inner-anodyne simplicial-set maps nor applies to noncomplete targets.

lem-coef-segal-space-inner-anodyne-locality vs lem-coef-complete-segal-quasicategory-comparison: the existing statement compares complete Segal spaces with quasicategories; the new locality assertion is for all Segal spaces before completion.

lem-coef-segal-space-inner-anodyne-locality vs lem-coef-quasicategory-invertible-interval: that statement evaluates the walking isomorphism in a quasicategory. It does not assert locality of a space-valued simplicial diagram for arbitrary inner-anodyne maps.

lem-coef-segal-space-inner-anodyne-locality vs lem-cbc-spine-inner-anodyne: that statement identifies spine inclusions as inner anodyne; it does not identify homotopy Segal spaces as local for all inner-anodyne maps.

lem-coef-segal-space-inner-anodyne-locality vs lem-coef-coarse-nerve-gluing: that statement identifies a particular coarse-nerve attachment as inner anodyne, which still needs the new independent locality assertion before applying mapping spaces.

lem-coef-segal-space-inner-anodyne-locality vs lem-coef-segal-inverse-evaluation: inverse evaluation identifies maps from the walking isomorphism with invertible arrows; it does not state arbitrary inner-anodyne locality.

Before creating the node I searched the entire DAG, not only this unit, by inner-anodyne/Segal terminology and the literature identifiers, searched full statement text, and ran `blueprint_refs.py search` for algebroid, inner anodyne, Segal, equivalence nerve and the source identifiers. The blueprint searches found no matching imported statement. Its ancestry is taken from `blueprint_refs.py ancestor`; `same_as` is empty. The same-tag candidates with genuinely adjacent statements are distinguished above.

## Review by Q49

I read the current item and all its cited node statements with the sources open. For the item, Gepner–Haugseng Lemma 4.3.19 and Example 4.3.20 give the coefficient reduction; Proposition 5.1.11, Theorem 5.2.5 and Corollary 5.2.7 give its groupoid route. Proposition 5.1.17 and Rezk Theorem 6.2 supply evaluation on invertible arrows; Gepner–Haugseng Lemmas 5.3.4–5.3.5 and Proposition 5.3.6 give the essential-surjectivity and fiberwise-detection route. I read Haugseng Corollary 6.6 and its proof for the sole new node: induction starts with the two-dimensional horn equal to the spine, uses the lower-dimensional spine-to-horn filtration at each successive dimension, and then weak saturation. Thus this prerequisite is independent of equivalence nerves and is a genuine lemma with its own hypotheses. I retained no proof or proof sketch inside its statement.

The citation-by-citation checks are as follows; `citations.json` copies the exact portions of the statements used.

1. The complete-algebroid definition gives the coarse finite-object algebroids, their cosimplicial maps and the definition of completeness. Only reversal by precomposition is used here; degree-zero evaluation is proved in step 5.
2. The Segal-localization model explicitly says that spaces are presentably monoidal at terminal coefficients. The Day-convolution statement explicitly gives a strong monoidal Yoneda extension and its lax monoidal right adjoint. The terminal category is small; the selected functor lands in the monoidal unit; the given V is presentably monoidal, hence cocomplete and locally small in the relevant universes. This supplies coherence as well as the underlying functors.
3. I checked that the total-category definition is the coherent restriction Grothendieck construction. Straightening is applied only after enlarging universes to make its base and all fibers small in its application universe. The opposite of its cocartesian construction gives the Cartesian lifts. The pointwise-transport statement expressly contains the K=point mapping-fiber formula; no equivalence-nerve or completion conclusion is smuggled in.
4. The many-object-operad statement explicitly supplies ordinary-operadic replacement and the restriction equivalence. Operadic change of enrichment supplies fiber adjunctions, algebra units and counits, and coherence under restriction in X. R_* preserves the Cartesian lifts because restriction commutes with postcomposition; its opposite therefore meets the cocartesian preservation hypothesis of the relative-right-adjoint statement. The specified fiber right adjoints there are the opposites of T_X. The resulting units, counits and triangle homotopies are precisely the restriction-natural algebra transformations, so the assembled left functor is T_*. Strong monoidality then identifies each T_*E_A with E_A. This is an adjunction on total coherent mapping spaces, not just on components.
5. The model statement identifies object spaces and mapping presheaves. The Segal-presheaf definition, at the terminal category and with no coefficient localization, is exactly the homotopy Segal condition. The free-diagram statement gives Map([0]!*,W)=W_0. I checked that dG_singleton is [0]!*, because the set of maps [n]→[0] has one element. This is the required evaluation map, so it supplies both degree zero and the completeness criterion.
6. Coarse-nerve gluing states exactly the one-vertex inclusion, with A nonempty, a in A and b outside A. The new locality statement applies to the possibly noncomplete Segal space W_C. The presheaf-limit statement gives pointwise colimits and turns contravariant mapping spaces of a colimit into a limit. I wrote out why the discrete pushout is a homotopy pushout using the two injective set decompositions, so there is no unsupported identification of ordinary and homotopy colimits.
7. This is the explicit elementary induction on the number of new vertices from step 6. The singleton base, pivot choices, ordered-subset restrictions and canonical nature of the resulting comparison are all stated. No new groupoid-property node merely restates the conclusion.
8. Inverse evaluation says exactly Map(dE,W)=W_inv over the endpoint space and explicitly permits noncomplete W. Taking its homotopy fiber retains endpoint paths. The algebroid definition provides units and composition; the comparison in step 5 therefore identifies these with object equivalences, including the contractible extension choices, rather than just a bijection of components.
9. Full faithfulness in the definition means equivalence of every enriched mapping object. Applying Map(1,-) gives equivalences of spaces. I checked the inverse-lifting argument in both endomorphism spaces: it reflects both inverse equations on components, so restricting to invertible components really is an equivalence of spaces.
10. Geometric descent explicitly states effectivity and surjectivity of G_0→|G| for groupoid objects. With step 7 this identifies paths in I(D) with the required homotopy fibers. The complete-algebroid definition uses surjectivity on components to define essential surjectivity. Thus both directions are proved, including the lift from a component of I(C) to an object of C.
11. I checked the exact descent square: its vertical maps are diagonals A→A² and B→B², and its pullback comparison is A→A×_B A. The descent statement permits the cover U(C)²→A², which is surjective on components by effectivity. Step 9 supplies exactly its fiber equivalences. Essential surjectivity makes every homotopy fiber nonempty. A nonempty space with equivalence diagonal contracts by restricting the two projection homotopies at a chosen point. The contractible-fiber criterion expressly uses homotopy fibers and includes empty spaces.
12. The complete-algebroid definition gives the factorization over the object-space map. Colorwise conservativity explicitly applies to small generalized nonsymmetric operads, including Delta_X^op; its V hypothesis is satisfied. The other factor is the Cartesian lift of step 3. The opposite straightening mapping-square criterion makes its induced mapping-space map an equivalence over an equivalence of bases. The quasi-inverse is then obtained by testing at D and C as written. This argument does not assume completeness.
13. The definition provides enriched composition and its unit constraints. With the reverse arrow and inverse homotopies of step 8, associativity identifies the composites on the actual V-valued mapping objects with the identity, on both sides. I checked that this is stronger than merely applying Map(1,-); no conservativity of Map(1,-) is assumed.
14. The maps used throughout are evaluation, restriction, postcomposition and canonical pullback comparisons. These commute with coherent algebroid maps. The proof-only choices of an ordering or an inverse do not change the defined maps, so the naturality clause is justified for their full mapping spaces.

For the B–E review I also checked the new statement's independent objects, all universe and size conventions, its explicit definitions of dK, inner anodyne and the homotopy Segal condition, the single-backslash TeX encoding and its statement-only unsplit shape. Both semantic phrasings, Loogle, grep and LeanSearch were actually run through msearch.py and recorded verbatim; no service outage was interpreted as absence. Returned StrictSegal and Quasicategory declarations concern set-valued diagrams or existence of fillers and cannot be specialized in one line to the space-valued locality statement. The item also has fresh searches alongside the preserved inherited ones. No new Mathlib leaf is claimed.

Small cases checked: the empty Segal space (a map into it exists only from an empty diagram; an inner-anodyne map cannot add vertices); the constant point; discrete nerves of ordinary categories, where Segal composites are unique; and the noncomplete one-object nerve of a group, to ensure completeness was not accidentally assumed. For the item I checked empty object spaces, a singleton coarse set, A={a} in the gluing lemma (the inclusion is an identity), A={a,c}, the singleton intersection in the groupoid condition, a fully faithful map with empty source (essential surjectivity then forces an empty target), and monoid/group examples for reflection of invertibility. In step 11 an empty target gives an empty source and the homotopy-fiber test is vacuous, as required. All current proof dependencies have been searched for a path back to this item; none is used when such a path exists.

## What remains

The new locality lemma is intentionally statement-only and becomes a stage-1 item. Nothing required for this one-level split is knowingly omitted. Final server dry-run results and the pushed commit are recorded below when available.
