## What changed

Replaced the proof of
`AlgebraicGeometry.Scheme.Modules.affineOpen_sectionFraction_localization` without
changing its statement or visibility. Added proof-only imports of
`Sheaf.AlgebraicGeometry.NonvanishingLocusRestrict` and the new
`Sheaf.AlgebraicGeometry.TensorPowerSectionOpenRestriction`.

The proof applies the existing `affine_section_localization` to the restricted
modules on `U.toScheme`. Invertibility follows by the restriction/pullback
isomorphism; quasi-coherence follows by Mathlib's restriction instance. The
proved `nonvanishingLocus_restrict` identifies the resulting open with the
preimage of `S`, whose image is `U ⊓ S`.

Three private, completely proved helpers handle the quotient algebra. Scalar
stability of the fraction generators makes their additive closure a submodule,
so it equals the underlying additive subgroup of their module span. A direct-sum
additive equivalence transports the generators in both directions and descends
by `QuotientAddGroup.congr`. Its generator formula then lets the final proof
compose the quotient, affine-localization, and section equivalences and apply
the coefficient comparison.

Updated the item's DAG proof to follow these Lean steps. One new module isolates
tensor-power section compatibility under restriction; it contains no localization
or quotient statement. It applies to arbitrary modules and arbitrary opens,
without affine, invertibility, quasi-coherence, or nonvanishing assumptions.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.affineOpen_sectionFraction_localization`
(node `lem-sc-affine-open-section-fraction-localization`). There are no remaining
sorries in the item's module. The three private helpers
`span_toAddSubgroup_eq_closure`, `sectionFractionRelations_additive`, and
`fraction_equiv_of_numerator_equiv` are proved.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.exists_tensorPowSection_open_restriction`
(node `lem-sc-tensor-power-section-open-restriction`), in
`Sheaf.AlgebraicGeometry.TensorPowerSectionOpenRestriction`.
Its proof is exactly `by sorry`, with its source and a complete argument in its
docstring and node. It states only the numerator and coefficient restriction
comparison, not the existence of a localization equivalence. In particular, the
quotient descent, the affine localization theorem, and the nonvanishing-open
identification remain outside this hole and are actually combined in Lean.

This is a decomposition: one original hole closed and one lower hole added;
net hole reduction is zero, not a claim of an unconditional proof. The existing
affine localization declaration is used, not duplicated. Both modules compile
with `lcompile.py --all`.

## No longer needed

None. No existing imports, nodes, or modules were pruned: the proof still uses
the original affine-localization route and the open fraction presentation.
The new comparison module imports only `ClearDenominators`, which supplies its
statement's section and tensor-power operations; it does not import a fraction
presentation that its statement does not mention.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original proof plan does not expose the
coherent comparison of tensor powers and section-power multiplication along
restriction as a usable declaration. Mathlib supplies `restrictAppIso` and
restriction/pullback comparisons, but these alone do not directly provide its
numerator-transition and coefficient identities. The existing
`exists_restriction_tensor_comparison` gives the binary tensor comparison on
pure tensor sections and is a suitable starting point for the remaining node;
it does not state the required iterated compatibility.

The original node's `created.item` is a module name, so
`blueprint_refs.py ancestor lem-sc-affine-open-section-fraction-localization`
prints `None`. The explicit existing `blueprint.from.node` is
`lem-sc-pic-proper-ntorsion`, an imported blueprint node, and this ancestry is
preserved for the new node. No target statement, definition, or unit route was
changed. The unit record `sk-thm-curveestimate` realizes its statement via
`thm-sc-proper-cohomology`; this reduction changes only the lower restriction
argument.

The sandbox checkout lacks the Stacks source files listed in the node. Read the
official Stacks pages for Tags 01PW, 09MR, and 01CD instead. The sources confirm
the affine restriction step and functorial tensor comparison. Searches were run
through `msearch.py`: LeanSearch returned HTTP 500 (recorded as unavailable),
Loogle found `restrictAppIso` and its naturality lemmas, and Mathlib grep found
`restrictUnitIso`, but no complete iterated section compatibility theorem.
Blueprint searches for restriction/tensor and tensor powers found no duplicate.

Edge cases checked mathematically for the new statement: `n = 0` is the unit
comparison; `s = 0` still gives natural transition maps; zero modules and empty
opens give zero section groups and the same comparison. No cancellation by s,
generator hypothesis, or assumption on the topology is needed. General sections
of a sheaf tensor product are not assumed to be pure tensors; coherence of
sheaf morphisms is verified by the tensor universal property.

## New nodes

`lem-sc-tensor-power-section-open-restriction`, in
`dag/nodes/sec-curve-estimates/lem-sc-tensor-power-section-open-restriction.json`,
records the strictly lower restriction comparison. Its Lean module is
`Sheaf.AlgebraicGeometry.TensorPowerSectionOpenRestriction`, with the single
public theorem `exists_tensorPowSection_open_restriction`. Its proof iterates
the existing binary tensor restriction comparison, checks unit and associator
compatibility by the tensor universal property, and applies section naturality.
The general restriction tensor comparison is used as a tool: it is already
proved and is not a substitute for any step of the curve-estimate unit. No
change record or forced adaptation is needed; all existing interfaces stay
identical.

## Second reading by T4

1. Interfaces: PASS. Compared the complete item module with the repository using
   `diff -u`. Its existing theorem signature, visibility, docstring, module header,
   options and public imports are byte-for-byte unchanged. Only three private proved
   helpers, the replacement proof, and two plain proof-only imports are added.
   The new module has one new theorem and no definitions or arbitrary witness choice.
   No target, existing definition, statement, or other group's file is changed.
2. Proof and trust: PASS as a decomposition. Both delivered files compiled with
   `lcompile.py --all`. Read each helper and the localization proof: scalar stability
   justifies additive closure versus module span, the numerator equivalence maps the
   relation generators in both directions, and the descended quotient equivalence
   is composed with the existing affine localization and section restriction.
   Scratch copies with `#print axioms` show only `propext`, `Classical.choice`, and
   `Quot.sound` for all three helpers. The original theorem and the new comparison
   theorem additionally use `sorryAx`, as expected from the reported open statement
   and upstream holes. The sole textual sorry is the named new theorem. No prohibited
   declarations, proof bypass, hollow definition, or data chosen from a holed mere
   existence theorem occurs.
3. Split statement: PASS. Read its whole signature, docstring and node and compared
   its coefficient equation against `rightUnitor_inv_comp_whiskerLeft_app` and the
   affine localization formula. The canonical open-restriction tensor isomorphism
   iterates to all degrees and respects the unit, addition associator and section
   powers, so both transition and coefficient compatibilities are true. The cases
   n=0, b=0, s=0, zero modules, U empty, V empty and U=top require no cancellation,
   choice of a generator, affineness or invertibility. This is a strictly lower
   compatibility lemma: it gives neither fractions nor localization, and cannot
   alone replace the original conclusion. Independently searched with msearch
   Loogle (`"tensorPow", "restrict"`), grep (restriction/monoidal/tensor words),
   and LeanFinder (iterated tensor restriction and natural multiplication), and rg
   on both library roots and the upstream module sources. No duplicate of the full
   comparison was found. Read `exists_restriction_tensor_comparison`: it is proved
   but supplies only binary tensor compatibility. The coherent iteration and its
   two displayed naturality identities are not a few-minute application of it;
   the single named lower hole is retained. Checked the cited sources directly:
   [01CD](https://stacks.math.columbia.edu/tag/01CD),
   [01PW](https://stacks.math.columbia.edu/tag/01PW), and
   [09MR](https://stacks.math.columbia.edu/tag/09MR).
4. Route and pruning: PASS. The proof actually uses the existing affine localization
   route and the open fraction definitions. Both newly added imports are plain
   imports used only by the proof. The new module's public ClearDenominators import
   supplies the operations in its signature. No old import is unused and all three
   old proof_deps remain used, so `No longer needed: None` is complete. Inspected
   `dag/units/sk-thm-curveestimate.json`: its realized statement remains
   `thm-sc-proper-cohomology`; this lower compatibility argument replaces no unit
   statement or step and changes no unit realization.
5. DAG agreement: PASS. The existing node's four new proof steps describe the
   restricted modules, explicit quotient descent, nonvanishing identification,
   and final composition as written. Its proof_deps are their union. The new node
   contains its provenance, source, searches, creation record, unchanged unit and
   chapter ancestry, complete mathematical proof and matching verbatim Lean
   statement. Its open proof is honestly reported, and no localization restatement
   is hidden under a new name.

Second reading changed only this report and added independent search records and
scratch verification files. No repair of the delivered Lean or DAG was needed.
The accounting remains one original hole closed and one lower hole added: a
one-for-one decomposition, net zero holes removed.
