# Stage-1 worker report: lem-kun-colim-gbl-gen

## Files written

- `dag/nodes/sec-smooth-purity/lem-kun-colim-gbl-gen.json`: statement, split; Mathlib searches found no exact theorem or one-line specialization. No new nodes; no new Mathlib leaves.
- `citations.json`: exact statement excerpts for all nine citations across the five proof steps.
- `prepare.py`: sandbox-only script preparing the item and checking all quotation substrings; not a delivery file.

## Attachments

None. Searching `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, global generation, `GeneratingSections`, and quotient-of-coproduct wording found Serre's theorem A, generation under pullback/pushforward, and generic generating-section constructions, but no declaration stating this item. In particular `Scheme.Modules.exists_generatingSections_tensor_twist` concerns twists on projective schemes; it is not the arbitrary-site colimit assertion. The upstream-master checkout was used only as read-only reference material, never as finished-proof evidence.

## WANTED:

None. The shared checkout omits the untracked blueprint and Stacks trees. I read their local reference copies under `/home/ubuntu/work-bp/sheaf/literature/`: the item's master blueprint file and its unit `_section.md`; Stacks `sites-modules.tex`, Tag 03CO, `lemma-limits-colimits-abelian-sheaves`; and `categories.tex`, Tags 002F (`definition-colimit`) and 003B (`definition-mono-epi`). No download was made.

## What was wrong in the imported node

The original conclusion is true for an arbitrary site, and I preserved that generality, the coefficient category of abelian sheaves, and the filtered-colimit assertion. The imported statement's global-generation notion was underspecified: its cited definition `def-kun-global-generated` only introduces a scheme and its small etale site. The updated statement writes the same evaluation definition on a general site, with global sections as compatible families, equivalently maps from the constant integer sheaf. This does not require a terminal object in the site. On an etale site it is exactly the original definition, as step 1 verifies from the constant-sheaf and sheafification universal properties.

The imported statement dependencies mentioned geometric stalks but omitted the global-generation definition and the colimit notion. The updated dependencies name the general site and abelian sheaves, constant sheaf, epimorphism, original etale definition for the explicit comparison, and the small filtered diagram/colimit. Imported metadata, including flags and `uses_not_cited`, are preserved. The imported `blueprint.from` remains null, as required for a blueprint node; `same_as` is now the searched empty list.

## Source error

STATEMENT-DISPUTED: the unqualified phrase “globally generated ... on a site” is not directly typed by `def-kun-global-generated`, whose objects are on `T_Et` for a scheme `T`. The correction is to spell out the identical evaluation formula at the claimed general-site level, rather than add a scheme hypothesis.

More substantially, the imported proof writes `T_Et` and geometric stalks while its hypothesis provides only a site `C`. This is a type mismatch: for example, the site on the discrete category with two objects and only identity coverings is allowed by the statement and has no terminal site object `T` from which `T_Et` or the proof's scheme-geometric points could be formed. The source does not supply a scheme or a jointly conservative family of points. I replaced the node-level stalk argument by a categorical argument. There is no counterexample to the corrected, explicitly defined claim: the new argument even works for arbitrary small colimits, although the statement retains the original filtered hypothesis. The unit itself has no proof steps and neither its statement nor any chapter route is changed.

## What could not be finished

Nothing remains mathematically open in this one-level split. The independent second reading and actual delivery remain the next worker's task.

## Not duplicates

No new nodes were created. Whole-blueprint searches for “filtered colimit globally generated”, “globally generated”, and “global generation”, and DAG keyword searches identified only the existing global-generation definition, the stalkwise criterion, the closed-support theorem, the separably-closed-field theorem, and Serre-A results. None is another copy of this colimit assertion. The existing `lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact` supplies the general-site existence of small colimits and is reused; its exactness clause is not needed. Its source Tag 03CO is not used to invent a new lemma.

## Review by Q08

I read the blueprint source `sec-smooth-purity/sk-prop-sf-kunneth-ordinary/lem-kun-colim-gbl-gen.md` and the unit `_section.md` in the reference literature tree, and the shared chapter/unit JSON records. The blueprint has exactly the arbitrary-site filtered-colimit statement and one geometric-stalk proof paragraph; the unit has no numbered proof steps. I checked the five replacement steps against the actual statements of every cited DAG node, as follows.

Step 1 cites `def-weil-pbc-constant-sheaf`, which defines the constant integer sheaf as sheafification of the constant presheaf, and `def-weil-pbc-sheafification`, whose unique factorization property supplies the map into `G`. A compatible family `s_U` gives the presheaf maps `n ↦ n s_U`, and conversely the images of `1` recover that family. This is an elementary argument from those definitions; it uses no preservation-of-colimits theorem. With a terminal site object, restriction identifies a compatible family with its value there. `def-kun-global-generated` is used only for its actual etale evaluation definition, with coefficient ring Z. I do not apply its scheme-specific statement to a general site.

Step 2 cites `lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact` only for its verbatim assertion that every small diagram in `Ab(C)` has a colimit. I read Stacks Tag 03CO, `lemma-limits-colimits-abelian-sheaves`, especially (1) and (4), and its sheafification proof. A site is small by `def-weil-pbc-sites-and-cohomology`; Hom sets and the chosen small category `I` are set-sized. Thus this existence assertion applies both to the diagram and to the discrete diagrams forming the evaluation coproducts. The construction of evaluation from its summand maps is exactly the colimit universal property in `def-weil-pbc-category-colimit` (Stacks 002F), not a further lemma.

Step 3 cites `def-weil-pbc-category-colimit`. Its unique map from a cocone constructs `h_i`, and its uniqueness clause proves the displayed equation after checking it on every summand: both sides equal `c_i ∘ s`. This three-line universal-property argument is marked elementary. It neither assumes the cocone maps `F_i → F` are epi nor assumes global sections commute with filtered colimits.

Step 4 cites `def-galois-epi-final` for exactly its right-cancellation definition of epimorphism (read also Stacks 003B). Precomposing `a e_F = b e_F` with `h_i` and substituting step 3 produces equality after `e_{F_i}`; the given global generation of each `F_i` makes this map epi, so cancellation proves `a c_i = b c_i`. This is elementary and uses the hypothesis at the correct stage.

Step 5 cites `def-weil-pbc-category-colimit` for uniqueness of factorization of the same cocone, yielding `a=b`, and `def-galois-epi-final` to identify that conclusion with `Epi e_F`. These nodes say precisely what is used. No non-elementary stalk detection, exactness, image argument, or hidden point-existence theorem occurs. The only non-elementary proof ingredient is the already-existing Mathlib-leaf colimit-existence statement in step 2; no new statement merely relabels the item.

For B1–B10, there are no new node records to validate. The item is a statement with an explicit definition of its formerly implicit notion, TeX uses single backslashes after JSON decoding, all source tags were checked against the Stacks tag table, and no Mathlib-leaf claim is made. I read the actual search candidates `SheafOfModules.GeneratingSections` and `.map` in `Algebra/Category/ModuleCat/Sheaf/Generators.lean`, the free coproduct/Hom equivalence in `Sheaf/Free.lean`, separator-coproduct lemmas in `CategoryTheory/Generator/Basic.lean`, and presheaf `IsGeneratedBy` in `CategoryTheory/Subfunctor/Finite.lean`. They provide different notions or infrastructure, not this theorem. Searches are copied from `searches.jsonl` with their exact query text and actual outcomes. LeanSearch returned HTTP Internal Server Error and is recorded unavailable. The first grep incorrectly specified the subdirectory `Mathlib/`, selecting a nonexistent nested `Mathlib/Mathlib`; its record explicitly marks that scope invalid, and subsequent correctly scoped grep searches in the root, `CategoryTheory`, and `Algebra` replace it. Both semantic phrasings and the corrected hits were read before concluding no exact match.

For C1–C8 and D1–D5, each citation has a verbatim statement excerpt in `citations.json`; no proof text of a dependency is used as an extra statement. All non-elementary ingredients are cited. The definitions and the one Mathlib leaf are generic tools, so the replacement does not import another unit's proof route. The item is not the unit's key statement, so no realized-field edit is required. The proof carries the argument rather than moving it into new nodes.

For E1–E7, I checked arbitrary sites without a terminal object or selected points, sites with empty coverings, zero sheaves, the empty site, and a one-object identity diagram. The compatible-family description and constant-sheaf universal property still hold, and the cancellation proof remains valid. For an empty site all sheaves are the zero object; evaluation is epi. The indexing category remains small and filtered, hence nonempty, as in the source; the proof simply does not need the latter property. No finite generation, torsion, nonzero coefficient ring, compactness, or scheme hypothesis is introduced. During self-review I rejected a draft restriction to an etale site and replaced it with this general-site proof; the final statement keeps the source's full scope.

## Validation

The required `deliver.py Q08 lem-kun-colim-gbl-gen --no-push` dry run printed `OK (not pushed)` with preflight passed. The sandbox contains only the item as a delivery node, with zero new nodes and zero new Mathlib leaves. No push, Lean writing, compiler, Lake command, or live-project mutation was performed.

## Second reading by Q08

I reread the item source `lem-kun-colim-gbl-gen` and the cited Stacks sources (03CO, 002F, and 003B), then checked every hypothesis and clause of the corrected arbitrary-site statement. The source's original phrase “globally generated” is scheme-specific through `def-kun-global-generated`; the explicit constant-sheaf evaluation definition records the intended general-site meaning and is marked `STATEMENT-DISPUTED` above. The zero sheaf, empty site, one-object identity site, field coefficient case, and one-object filtered diagram all satisfy the corrected statement.

- Step 1: checked against `def-weil-pbc-constant-sheaf`, `def-weil-pbc-sheafification`, and `def-kun-global-generated`; the compatible-family/Hom correspondence and final-object comparison are elementary and use exactly those definitions.
- Step 2: checked against `lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact` and `def-weil-pbc-category-colimit`; it uses only the cited small-colimit existence clause and the discrete-colimit construction of coproducts, with no hidden exactness or stalk assumption.
- Step 3: checked against the full colimit universal property in `def-weil-pbc-category-colimit`; the summand calculation explicitly proves `e_F h_i=c_i e_{F_i}`.
- Step 4: checked against the right-cancellation definition in `def-galois-epi-final`; precomposition with `h_i` and the stage epimorphism gives the displayed equality for every `i`.
- Step 5: checked against the uniqueness clause of `def-weil-pbc-category-colimit` and the epimorphism definition; agreement after every cocone map gives `a=b`, exactly the required conclusion.

There are no new nodes, so no new-node statement requires a separate B1–B7 verdict. I checked all six existing dependency statements used by the proof and verified each citation quote in `citations.json`; whole-DAG duplicate searches and the recorded LeanFinder, Loogle, grep, and unavailable LeanSearch searches were reread. I changed only this second-reading section: the split already had the corrected statement, explicit five-step proof, source-error notice, and valid citation/search records. The dry-run command is being rerun after this report append.
