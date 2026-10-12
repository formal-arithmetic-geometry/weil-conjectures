## What changed

The unchanged theorem `AlgebraicGeometry.Scheme.coherent_support_power_ideal_kills` now has
a complete Lean proof from existing support/zero-locus declarations and one new affine-cover
zero criterion. Coherence supplies quasi-coherence and finite type through the already proved
`Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType`. The proof constructs a finite affine
cover, translates support containment to radical containment, uses Mathlib's
`Ideal.exists_pow_le_of_le_radical_of_fg`, and constructs a common exponent by `Finset.sup`.
The reverse implication uses the actual witness `a^t` in the annihilator's radical, including
exponent zero. The original docstring and theorem signature are preserved.

Added `Sheaf.AlgebraicGeometry.IdealPowerProductZeroAffineCover` for the remaining comparison
between vanishing of the product sheaf and annihilators on an affine cover. This is independent
of support, coherence, Noetherianity, finite covers, and existence of an exponent. It is
strictly the original proof's steps 3 and 4, not the original theorem restated. Its proof plan
uses the existing tensor, image, ideal-power section and tilde/Gamma statements.

The parent DAG proof and proof dependencies are updated to match the compiled argument.
All proof dependencies are ordinary imports. The two original public imports are retained to
preserve the existing interface seen by importers. Second reading removed the unused public
`Mathlib.AlgebraicGeometry.Modules.Tilde` import from the new module; tilde belongs only to
its deferred proof, not its statement.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.coherent_support_power_ideal_kills`
(node `lem-weil-pbc-coherent-support-power-ideal-kills`), one original hole.

Added and left: `AlgebraicGeometry.Scheme.idealPowerProduct_isZero_iff_affine_cover`
(node `lem-weil-pbc-ideal-power-product-zero-affine-cover`), one hole with proof exactly
`:= by sorry`. No hole remains in the item's module. This is a decomposition, with net
hole count zero, not a claim that the full theorem is independent of sorry.

The pre-existing support and ideal zero-set statements used by the proof remain dependencies;
they are not proved in this delivery. Local compilation of both modules passes.

## No longer needed

Second reading also removed the unused `Mathlib.AlgebraicGeometry.Modules.Tilde` public
import from the new split-off module.

Removed direct proof imports `Sheaf.AlgebraicGeometry.Coherent` (supplied by the existing
public imports and the coherence criterion),
`Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine` (the proof uses finite type directly),
and `Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections` (used only below
the extracted affine-cover criterion and imported there).

Pruned from the parent's direct proof dependency list:
`def-weil-affine-spectrum`, `pqf-def-coherent`,
`lem-weil-pbc-quasi-coherent-finite-type-affine`, `def-weil-finitely-generated-module`,
`lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`,
`def-weil-pbc-coherent-formal-module`,
`lem-weil-pbc-module-restriction-open-immersion-colimits`,
`lem-weil-pbc-affine-tilde-gamma-adjunction`, `def-weil-sheaf-of-modules-category`,
and `lem-weil-pbc-finite-module-support-annihilator`.
Some remain transitively needed below the support and zero-detection comparisons; this is
not a claim that these modules leave the targets' complete import closure.
The existing public `CoherentFormalModule` and `QuasiCoherentIdealZeroSetAffine` imports
are kept; no public interface change is part of this delivery.

## Where the brief, the DAG or earlier work was wrong

The planned ideal-times section statement does not directly say that the powered product
vanishes iff its affine section ideals lie in annihilators: it describes positive power
section ranges and products for `IdealSheafData`, whereas `idealSheafPower` returns a module
and an inclusion. The extracted criterion isolates the required induction/comparison,
including t=0, and sheaf gluing without altering any existing definition or statement.
No mathematical error in the parent statement or unit route was found.

The generic coherence criterion is an already proved tool from unit
`sk-prop-av-pqf-finite`; it is used only to obtain quasi-coherence and finite type, without
replacing any step of the proper-base-change unit. Its module was checked not to reach
this item, so the added proof import does not create a cycle.

LeanSearch returned Internal Server Error; this is recorded as unavailable, without an
absence verdict. Loogle/LeanFinder and local source searches were performed. The repository
copy of `literature/stacks-project/coherent.tex` was absent on this machine; the primary
Stacks pages 01Y9 and 00L6 were read online to verify the parent route.

## New nodes

`lem-weil-pbc-ideal-power-product-zero-affine-cover`: original steps 3 and 4, formulated for
any scheme, any quasi-coherent module, any affine cover, and any fixed natural exponent.
The cover need not be finite. The empty scheme with empty cover gives a zero sheaf and a
vacuous right-hand side; for t=0 the condition is that every section module is zero; for
F=0 every exponent works; for the unit ideal the criterion detects F=0; for the zero ideal
and positive t both sides hold. These checks exclude the usual zero-exponent and empty-cover
mistakes. Whole-blueprint searches found no duplicate. No change record is needed because
no existing statement, definition, or public import was changed.

## Second reading by P2

1. PASS: Compared both delivered modules with the repository (the affine-cover module
   is new). The parent declaration signature and entire docstring are byte-identical.
   No existing definition or statement changes; the parent JSON changes only `proof`,
   `proof_deps`, and `proof_origin`. No change record is required.
2. PASS: Both files compile through lcompile.py. The parent has no remaining sorry;
   the sole new sorry is exactly the named affine-cover theorem listed above. No axiom,
   unsafe, opaque, implemented_by, extern, hollow definition or arbitrary witness data
   is added. Axiom probes show only propext, Classical.choice, Quot.sound and sorryAx.
   The exponent choice is local proof data obtained from the proved Mathlib existence
   theorem, not a new object defined using an arbitrary unproved existence theorem.
3. PASS: The affine-cover criterion is strictly the local product/annihilator comparison
   and zero detection, for one fixed exponent. It adds neither support containment nor
   existence of a power, Noetherianity or coherence, so it is not a renamed parent.
   Checked t=0 (annihilator equals top iff the section module is zero), t=1, F=0,
   K=0 with positive exponent, K=top, and the empty scheme/empty cover. Its source,
   full proof docstring and new DAG node are present. Independent LeanFinder, Loogle
   and Mathlib grep searches with different queries, plus local library searches,
   found no duplicate criterion. Existing isZero_of_iSup_eq_top and
   isZero_of_forall_affineOpens cover the gluing subargument, not the missing powered
   product comparison. The latter requires induction and compatibility of tensor
   multiplication and images; it is not a few-minute application of the existing
   positive-power range statement, which accepts IdealSheafData rather than the
   recursively constructed module/inclusion pair.
4. PASS: Read the parent from its conclusion through the cover, support formulas,
   radical containment and finite supremum. The reverse implication handles exponent
   zero via the actual radical witness a^t; ideal powers decrease as the exponent
   increases. All ten removed original proof_deps appear in No longer needed.
   Read dag/units/sk-thm-p1.json: no realized statement or step is bypassed or replaced.
   Removed the new module's unused public Tilde import. The other public imports
   supply the signature; remaining ordinary imports record its deferred proof route.
5. PASS: Checked the parent proof steps against its Lean proof and the new node's
   statement against the verbatim Lean signature. proof_deps is the union of uses
   in each node; the new record has source, origin, search evidence, created, blueprint,
   chapter, unit and lean fields. The parent explicitly reports one closed hole and
   one added hole, hence decomposition with net zero.

Changed: pruned the unused public Tilde import from IdealPowerProductZeroAffineCover;
updated the report with that pruning and this independent review. No proof, statement,
definition or node needed correction.
