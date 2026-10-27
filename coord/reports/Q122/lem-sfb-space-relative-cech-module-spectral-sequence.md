# Q122: lem-sfb-space-relative-cech-module-spectral-sequence

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-relative-cech-module-spectral-sequence.json`: statement, now split into seven proof steps; no Mathlib match.
- No new nodes and no new Mathlib leaves. All supporting lemmas already exist in the DAG.
- `citations.json`: one verified verbatim statement quotation for each step/dependency pair.
- `searches.jsonl`: actual msearch query records; retained all inherited searches in the item and added the searches of this dispatch.

## Attachments

None. Searched the project source for the item tag, relative Cech terminology, and spectral-sequence terminology. The two `CategoryTheory.Sheaf.exists_cechToDerivedSpectralSequence` declarations, including the `of_enoughInjectives` form, concern abelian cohomology over one site object and an E2 Cech page. They do not state a relative spectral sequence in structure-sheaf modules, with this E1, so they are not attachments. The project Cech declarations cannot establish the whole item merely because their individual theorem bodies have no sorry.

## WANTED

None: all source material used is present in the literature directory.

## Problems found and corrected

The item statement is unchanged; no STATEMENT-DISPUTED claim is needed. Its source place named 03LX as a localization identification, whereas that is module higher-direct-image etale base change. The correct explicit site and ringed-site localization equations are 04LY and 04LZ; the source place now identifies both and their labels.

The initial node was statement-only, with no proof to retain. The resumed sandbox had only brief markers and no item, report, search log, or delivery receipt; no matching deliver process was active. Copied the current live item, retaining its inherited searches and creation/blueprint metadata. No repair note exists for the item.

An attractive existing node, `lem-sfb-cech-injective-image-augmentation`, assumes Cartesian coefficients and exact module inverse image for f. These hypotheses are unavailable for an arbitrary morphism of spaces with structure-sheaf coefficients. I did not apply it or its column-model companion. Instead the proof evaluates each row on V etale over Y, where it is the Cech section complex of an injective on the enlarged site of X. This uses 03FC directly and needs no flatness of f. The exact inverse images used on columns are only the etale localizations u_p.

The live unit record and latest blueprint use different historical paths for this unit; I read the latest blueprint under `literature/blueprint/latest/`, including the direct-image proof (3), and preserved the inherited ancestry. `blueprint_refs.py ancestor` reports `None`; the inherited `blueprint.from.node = null` remains null. No ancestor was invented, and the place and split-report blueprint entry explain the supporting cohomology argument. This is not the key node of the unit, so no realization fields were edited.

## Unfinished work

None for this one-level stage-1 split. The existing dependencies remain their own items where not already proved. No Lean was written and no compiler, Lake command, or build was run.

## Not duplicates

No new nodes were created. DAG and whole-blueprint searches found existing ringed-site Cech acyclicity, slice adjunction, injective comparison, row-to-total augmentation, and first-quadrant spectral-sequence nodes, all reused. The absolute abelian node `lem-sc-cech-spectral` differs from the relative module-valued item. The stronger relative Cech-totalization nodes were read but their exact-f-pullback hypotheses prevent using them here.

## Review by Q122

I read Stacks `stacks-sheaves.tex` Tag 072E, label `lemma-cech-to-cohomology-relative-modules`, and the preceding relative abelian proof to which it refers. The proof proceeds by an injective resolution, exact augmented Cech rows, and the two spectral sequences of one double complex; the split retains that argument on small etale sites. I checked the suggested Cech route just before 0720 in `spaces-cohomology.tex`. The atlas-to-localized-site transition was checked against `spaces-properties.tex` 03G1 and equations 04LY/04LZ, and the direct-image sections against 03M8 in `spaces-morphisms.tex`. I also read 03FC in `sites-cohomology.tex`, 04IE and extension-by-zero exactness in `sites-modules.tex`, 079Q and 079H in `injectives.tex`, 0130/0132/0133 in `homology.tex`, and the 013P/013S resolution comparison statements and proofs in `derived.tex`. There are no new-node sources to review.

For every cited node I opened its statement, rather than relying on its title or proof. The following explains exactly what each step takes.

1. `lem-trf-space-enlarged-etale-ringed-site-model` supplies the ringed equivalence and localization identification. `lem-trf-space-fibre-products-etale-covers` supplies the nerve fibre products and base-changed cover. `lem-trf-space-chartwise-etale-permanence` supplies compositions/base changes of etale maps and the face maps over X. `lem-trf-space-chart-limit-enlarged-sections` identifies the particular chart-limit direct images in the statement with enlarged-site sections, including scalar actions and restriction maps. In particular W need not be a scheme; that is exactly why the enlarged site is used. Representability of the atlas gives the schemes U_p inductively. Transport of exactness and injectivity through an equivalence is the universal-property argument written in the step.

2. `lem-weil-pbc-ring-sheaves-grothendieck` concerns an arbitrary ring sheaf, not a constant coefficient ring, so it applies to the structure sheaf. `lem-sp-grothendieck-enough-injectives` and clause (1) of `lem-weil-pbc-left-exact-injective-resolution-degree-zero` give a nonnegative injective resolution. `lem-weil-pbc-ringed-sheaf-slice-adjunction` states exact restriction and an exact additive left adjoint; `lem-sp-right-adjoint-preserves-injectives` therefore applies in the direction u_{p!} left adjoint to u_p^*. This proves that each restricted complex is an actual injective resolution. `def-trf-space-etale-module-functors` supplies the specified adjunction; the step spells out why its direct image preserves kernels and is additive. It does not treat exactness of f^* as a consequence of a definition.

3. `lem-trf-space-chart-limit-enlarged-sections` and the enlarged-site model supply B(V) as I(W_p), naturally and with the correct ring action. `def-sp-double-complex-total` defines the commuting-double-complex convention and total sign. This is the one elementary step: deleting two factors gives the two equal compositions which occur with opposite signs in d_h squared, and naturality of the resolution differential gives commutation. No separate lemma asserting the whole double-complex construction was introduced.

4. `lem-weil-pbc-ringed-site-injective-module-cech-acyclic` states positive Cech vanishing for an injective module on any such ringed site, not just a scheme or a constant ring. Its common-universe hypotheses were checked using `def-weil-size-convention`; the singleton covering index and all site/coefficients can be placed in the prescribed larger universe. The degree-zero kernel comes from the actual equalizer axiom in `def-weil-pbc-sites-and-cohomology`, not from positive vanishing alone. `lem-trf-space-chart-limit-enlarged-sections` identifies all terms and arrows; `def-weil-sheaf-of-modules-category` states sectionwise kernels and sheafified sectionwise cokernels. This makes sectionwise row exactness imply sheaf row exactness, even though general sheaf epimorphisms need not be surjective on sections.

5. `lem-sc-first-quadrant-column-augmentation` explicitly allows the augmentation into (0,q) and tests the rows as columns after flipping; all of its assumptions are established in steps 3 and 4. I checked the orientation rather than applying a column statement to rows without explanation. `def-sp-double-complex-total` gives the +1 vertical sign on that augmentation column; `def-sp-left-exact-additive` defines derived functors by the cohomology of the image injective resolution. Thus the abutment is R^nf_*M and is identified by the actual augmentation map.

6. `thm-sp-double-complex-spectral-sequences` states the E1 vertical-cohomology formula, d1 induced by the horizontal differential, finite image filtrations, stabilization, and functoriality; it really supplies all the asserted clauses. `def-sp-left-exact-additive` identifies each vertical cohomology with the desired R^q(fu_p)_*. No global sections or underlying abelian derived functor is substituted for a module derived functor. The signed total convention agrees with the cited first spectral sequence.

7. `lem-weil-pbc-injective-resolution-lift-exists` gives lifts; `lem-weil-pbc-lift-to-injective-unique-up-to-homotopy` applies because the resolution augmentation is a quasi-isomorphism and its target is bounded below and injective. The double-complex theorem gives maps and finite filtrations. `lem-sp-filtered-homotopy-spectral-sequence` is used for later pages and filtered abutments only: equality on E1 is separately shown by applying each vertical homotopy to cycles. I checked the total homotopy sign (-1)^p, the cancelling horizontal terms, and its filtration preservation. Comparisons over identities yield resolution independence, and comparison of composite lifts gives functoriality. No assertion of naturality under arbitrary geometric base change is added.

I tested the statement on M=0, on n=0, and on the identity atlas. For the identity atlas the unnormalized Cech horizontal complex has differential alternating between 0 and the identity and hence has only its degree-zero cohomology, as required; it is not incorrectly replaced by a complex with every differential zero. A surjective atlas with empty source forces X empty, so the statement reduces to zero. In each degree the total has only n+1 summands, with no finite-cover, separation, qcqs, or Noetherian requirement. A nonflat morphism f presents no issue because tensor pullback along f was never used as an exact functor.

All seven steps are shorter than 2000 characters; none hides a separately invoked comparison lemma or a restated clause of the item. I checked delivery-errors B through E: complete unchanged statement; actual source tags; no unrecorded searches, new elementary nodes, duplicate nodes, clause-as-node splits, implicit flatness, or unsupported citations. Every step/dependency pair has a quotation checked as a literal substring of the live cited statement. Off-unit generic tools are explained individually in `split_report.tool_uses`; these do not replace the unit's route.

The Mathlib searches were run only through msearch.py and their actual logs were read. Two semantic phrasings, Loogle, LeanSearch, and CategoryTheory/Algebra source grep give schemes, Mayer-Vietoris complexes, ordinary Cech complexes, and spectral-object infrastructure. I read the Mathlib Cech file: it defines a Cech complex, not the relative higher-image spectral sequence. None of these hits states the item or specializes to it in one line. The inherited searches remain intact, and the new records retain the exact query texts and returned log data.

Before writing this report, the server-only `review_split` and `check_dag` checks passed on the initial seven-step version. I then made the etale permanence citation and direct-image left-exactness argument explicit and regenerated the citations. The required full dry run and push follow this signed review.
