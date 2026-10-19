1. Files written:
- `dag/nodes/sec-picard-framework/def-pc-restricted-resolution-sections.json` (rebased to the current live node statement and kept as a split-stage item with the closed declaration attachment).
- `citations.json` (empty because this is a definition with no proof steps).

2. Attachments:
- `AlgebraicGeometry.Scheme.Modules.RestrictedResolutionSections` belongs to `def-weil-pbc-flat-base-change-open-choices` (declaration in `lean/Sheaf/AlgebraicGeometry/FlatBaseChangeOpenChoices.lean:68`). The declaration is closed (`sorry_after=[]`) in the reviewed FlatBaseChangeOpenChoices source.

3. WANTED: none.

4. Problems and corrections:
The previous landing was based on a stale side statement and a merged status. The current live DAG node is `unsplit` and has a revised statement: it omits the bracketed dependency annotation on the injective resolution and says “an induced isomorphism between its global-sections complex and the section complex of I over U.” I copied that statement, source place, and exact two-entry `stmt_deps` from the live node, set the worker-owned status back to `split`, and cleared the stale merged target. No new node is created because the existing FlatBaseChangeOpenChoices declaration already bundles this structure.

## Review by NZ

I reread the current live node and matched the sandbox statement, source, and dependencies character for character. I also reread the bundled source declaration at `Sheaf/AlgebraicGeometry/FlatBaseChangeOpenChoices.lean:68–82`: its fields provide the restricted injective resolution, augmentation-preserving comparison, and degreewise section-complex comparison described by the rebased statement. The declaration has no sorry in the reviewed source audit. The two cited definition dependencies are exactly the module-sheaf category and injective-resolution notions used by the statement; the prior flat-base-change bundle is an attachment source rather than a statement dependency after the live revision.

There are no proof steps and therefore no step citations: this is definition data already supplied by the closed structure declaration. I checked the edge cases represented by the structure (arbitrary open, including empty open, and zero resolution terms) and introduced no extra hypotheses. The repair specifically addresses the landing return by rebasing the statement and restoring `split` status; the dry run below verifies the resulting overlay.

5. What I could not finish: none.

## Second reading by NZ

- Item statement: checked cohomology.tex Tag 01E1, lemma-cohomology-of-open, lines 495–524, and Tag 01E4, lemma-describe-higher-direct-images, lines 591–635. These give restriction of injective resolutions and section-complex evaluation, not a named Stacks bundle; the node is the explicit bookkeeping definition. No extra hypothesis on the scheme or open is required. Verdict: retain the statement.
- Existing declaration comparison: read /home/ubuntu/weil-newtargets-review/lean/Sheaf/AlgebraicGeometry/FlatBaseChangeOpenChoices.lean:68–82. Its resolution, comparison, augmentation, sections and components fields match the five clauses of the item. The last field specifies in degree n the comparison on top sections followed by restrictAppIso and the image-top equality. Verdict: exact definition-data match; not an existence proof.
- Statement dependencies: read def-weil-sheaf-of-modules-category (sectionwise module structures and compatible restriction maps), def-sp-injective-resolutions (injective resolution), and def-pc-scheme. Verdict: the first two supply their stated notions; add the missing scheme dependency already cited in the text.
- Proof steps: none, as appropriate for a definition of data. Read lem-pc-restricted-resolution-sections-exist: Nonempty of this structure is a separate assertion. Verdict: do not import its proof into the definition; citations.json correctly remains [].
- New nodes: none. Read def-weil-pbc-flat-base-change-open-choices: its restricted-resolution identification clause already describes this data, and its lean.declarations explicitly includes RestrictedResolutionSections. Verdict: no duplicate child, no new Mathlib leaf and no new-node searches required.
- Edge cases: U empty (including X empty), U=X, F=0, and degrees 0 and 1 impose no forbidden nonemptiness or nonzero condition. The augmentation condition is degree 0; the section-component equation is for every natural n and includes 0 and 1. Verdict: consistent data definition in all cases.

Changes and reasons:
- Added def-pc-scheme to stmt_deps, since the statement explicitly cites it.
- Added the exact Stacks labels to source.place; the previous tag-only attribution omitted them.
- Replaced the stale split_report.summary claiming a merge and removal: the delivered node remains split and is not removed.
- Removed the sandbox's unsupported slopmaster2 closed audit and stale merged_into field. The supplied /home/ubuntu/weil-src-slopmaster2 checkout has no RestrictedResolutionSections declaration; the definition can be read in the separate review snapshot, but that does not establish slopmaster2 closure. The first worker's closure assertion above is superseded by this finding; no audit closure is claimed by this delivery.
- Retained the first worker's sections, the mathematical statement, and empty proof/citations. No Lean was written or compiled.

Validation: the delivery script rejects a trailing positional dot by printing usage; invoke its documented two-positional-argument form. The initial dry run passed; rerun after the repairs below.
