## What changed

Replaced the sorry in `higherDirectImage_section_clearDenominators` with a complete
Lean proof from two independent intermediate theorems and the already proved
`higherDirectImagePresheaf`. The signature and existing docstring are unchanged.
The proof chooses the library injective resolution, uses its canonical comparison,
lifts a section through the affine comparison, clears its raw denominator using
`IsLocalizedModule.Away.surj`, and transports the equality by naturality and linearity.
All three modules compile through lcompile.py without warnings. No existing interface,
definition, target, or module held by another group was changed.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.Modules.higherDirectImage_section_clearDenominators`
(node `lem-pc-higher-direct-image-section-denominators`). Its proof has no sorry.

Added and left:
- `AlgebraicGeometry.Scheme.Modules.sectionCohomologyPresheaf_isLocalized_away`
  (`lem-pc-section-cohomology-principal-localization`): the raw presheaf localization
  step, independent of higher-image sheafification.
- `AlgebraicGeometry.Scheme.Modules.affineLocalization_sheafification_unit_isIso`
  (`lem-pc-affine-localization-sheafification`): a general assertion for any module
  presheaf satisfying affine principal localization, independent of cohomology.

This is a decomposition: one upper hole closed and two lower holes added, not a
sorry-free proof of the transitive import closure. Each remaining proof is exactly
`:= by sorry` in its own public theorem and module. Their docstrings give full
source-based arguments. No data is chosen from either holed theorem: both conclusions
are propositions, and the resolution is the existing library construction.

## No longer needed

No imports or modules pruned. The old direct proof-dependency edges
`def-pc-morphism-conventions`, `pqf-def-coherent`, `lem-sc-invert-s-cohomology`,
`lem-weil-pbc-spec-module-tilde-sections`, and `lem-weil-pbc-sheaf-on-basis-extends`
are no longer direct steps in the item's proof. Morphism conventions and quasi-coherence
remain in its signature; localization, tilde, and basis extension remain in the split
lemmas' argument. They are replaced by the two new direct dependencies, rather than
claimed unnecessary in the transitive argument.
The original public Basic import remains necessary for the statement. The
original raw localization, tilde sections, and basis extension dependencies remain
needed through the two new steps; the higher-image-presheaf dependency is used directly.
No module is claimed pruned. No existing import was removed from the assigned module.
The downstream quasi-coherence theorem is deliberately not used: it already uses this
module, so it would form an import cycle.

## Where the brief, the DAG or earlier work was wrong

The original module had only its statement import, although the node recorded proof
steps requiring other modules. `invertS_cohomology` supplies an additive fraction
comparison for twisted open module cohomology, not a directly usable linear localization
of the pushed-resolution presheaf. `higherDirectImagePresheaf` proves a sheafification
comparison and naturality, but does not prove that sheafification preserves affine
values. Those are distinct bridges, now exposed as the two intermediate statements.
The original plan remains valid; no disputed statement was found.

Edge cases checked in the mathematical statements: degree zero, empty affine opens,
zero coefficients, a=0, and units a. The general sheafification statement needs
localization on every affine open, not just one, since sheafification is local.
Both theorem interfaces compile with autoImplicit=false. Sources were read from the
Stacks pages (09MR, 01HV, 009H); LeanSearch was unavailable and this is recorded without
an absence verdict. Existing basis-extension and tilde interfaces were read; neither
alone is the general affine-unit statement.

## New nodes

`lem-pc-section-cohomology-principal-localization` in
`lean/Sheaf/AlgebraicGeometry/SectionCohomologyPrincipalLocalization.lean` records the
linear tensor-unit specialization and resolution/evaluation bridge. Its proof imports
`InvertSCOhomology`, while its signature imports the raw presheaf construction.

`lem-pc-affine-localization-sheafification` in
`lean/Sheaf/AlgebraicGeometry/AffineLocalizationSheafification.lean` records preservation
of affine values by sheafification under localization hypotheses. Its proof plan uses
the existing tilde and sheaf-on-basis extension modules. Both nodes stay in the original
chapter and unit; no realized unit statement or step is bypassed. No change record is
needed because no existing interface changed.

## Second reading by C3

1. PASS: compared the delivered existing module with the read-only repository using
   diff, then compared its section variables, docstring, and theorem signature byte
   for byte. Only three plain proof imports and the theorem body changed. No existing
   definition, signature, visibility, or target changed; no change record is needed.
2. PASS as a decomposition: compiled all three modules in import order with lcompile.py
   (3.0 s, 3.7 s, 16.8 s), without warnings. A scratch import module with explicit
   #print axioms for all three theorems compiled and showed only propext,
   Classical.choice, Quot.sound, and sorryAx. Exactly two whole named theorem proofs
   remain sorry, as listed above. There are no forbidden declarations or hollow data
   definitions. The upper proof uses the canonical resolution comparison, adjunction
   unit, component bijectivity, Away.surj, naturality, and scalar linearity; it is not
   an application of a renamed copy of the original statement.
3. PASS: read both new statements, their full docstrings, nodes, and cited Stacks
   arguments (09MR, 01HV, 009H). Raw localization is the tensor-unit specialization
   of cohomology localization with the evaluation/resolution and scalar-action bridge.
   Affine unit invertibility is a general basis/sheafification assertion independent
   of cohomology. Checked degree zero, zero coefficients, empty affine opens, a=0,
   and units. In particular Away at zero forces the target module to vanish, including
   the empty-cover case; the all-affine localization assumption is needed to make the
   basis argument work locally. Neither is a restatement of denominator surjectivity.
   Independent searches used Loogle IsLocalizedModule.Away, LeanFinder for agreement
   of sheafification on a gluing basis, msearch grep, and rg in both library roots and
   Mathlib. Read Mathlib tilde.toOpen and its Away instance, the existing basis-extension
   theorem, invertS_cohomology, higherDirectImagePresheaf, and
   module_sheafification_iso_of_affine_restriction. The last requires a supplied
   affine-basis isomorphism to a sheaf and returns an unspecified isomorphism after
   sheafification; it does not supply the needed canonical unit assertion. No direct
   duplicate or shorter complete proof was found. Neither open bridge could be closed
   by a few-minute application of these interfaces.
4. PASS: the top proof uses the existing higherDirectImagePresheaf comparison and
   Mathlib fraction surjectivity. All proof-only imports are plain imports; public
   imports in the new files supply their signatures. No original import is removed.
   The old direct DAG edges have been explicitly accounted for under No longer needed.
   Both splits implement the existing node's localization and basis-extension route.
   The unit sk-thm-picard-coherence has pre-existing empty realized lists; these were
   read and left intact. No realized unit statement or step is bypassed, and this
   review does not claim to repair that pre-existing realization gap.
5. PASS: the existing node changes only proof, proof_deps, and proof_origin. The proof
   dependency lists equal the union of the proof steps' uses. The two new nodes match
   their Lean signatures, contain sources, searches, creation records, blueprint
   ancestry, chapter/unit, and lean records, and have status split. The revised upper
   node describes exactly the localization, component-isomorphism, and equality
   transport used in Lean.

Second reading changed dependency accounting and added this review and independent
search records. No Lean proof or statement required repair. One upper hole closed,
two lower holes added: net -1 hole closed in this delivery, a decomposition, with no
claim of a proved transitive closure or pruned module.
