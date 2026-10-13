## What changed

In Sheaf.AlgebraicGeometry.IdealPowerEvaluationEventuallyZero, replaced the sole
sorry by a compiling finite-affine-cover proof. On each affine member obtain an
exponent, take their finite maximum with n, prove the prescribed transition maps
compose by cancelling the monic power inclusion, propagate local vanishing to the
common exponent, and use sheaf-morphism uniqueness to conclude globally.
The original declaration's signature and its two public imports are unchanged.
Added proof-only imports of IdealPowerEvaluationAffineEventuallyZero,
FormalPolynomialPowerLifts, GlueSheavesOfModules, and Mathlib's QuasiCompact.
FormalPolynomialPowerLifts is used only for its already proved
AlgebraicGeometry.formalPolynomial_power_mono. The new open affine module also
imports its recorded proof dependencies: Mathlib Modules.Tilde and
LocalizedModule.Basic, QuasicoherentFiniteTypeAffine,
IdealTimesQuasiCoherentAffineSections, and FormalPolynomialPowerLifts. Its
statement imports are Coherent and IdealModuleProductStalk; AffineScheme is
already public through Coherent and was removed as a redundant direct import. All nodes lie in sk-thm-p1;
none of that unit's realized statements or steps is bypassed.

## Proved and sorry left

Closed: AlgebraicGeometry.Scheme.ideal_power_evaluation_eventually_zero
(lem-weil-pbc-ideal-power-evaluation-eventually-zero), by reduction to its affine
calculation and a complete Lean globalization argument.

Added and left: AlgebraicGeometry.Scheme.ideal_power_evaluation_affine_eventually_zero
(lem-weil-pbc-ideal-power-evaluation-affine-eventually-zero), in the new module
Sheaf.AlgebraicGeometry.IdealPowerEvaluationAffineEventuallyZero. Its proof is exactly
`by sorry`; its docstring gives the affine argument and the source.
No sorry remains in the original module. One hole closed and one added: this is a
decomposition, not a net proof gain. The new conclusion is zero only over a single
affine open, with no CompactSpace assumption on the ambient scheme. It supplies
steps 1–2, not the finite-cover/max-exponent/sheaf-uniqueness step proved here.

Both delivered modules compile through lcompile.py, with no compiler warnings.
The main proof works even for an empty finite cover: max n 0 is available and
sheaf uniqueness applies to the empty cover of an empty scheme. For the local
statement, checked the zero ideal (positive powers zero), unit ideal (evaluation
at 1 detects every linear map), n=0, zero target, and empty affine open. There
is no Noetherian, finite-type-target, or quasi-separatedness assumption.

## No longer needed

No imports removed from the original module and no modules pruned. Removed the
redundant public Mathlib.AlgebraicGeometry.AffineScheme import from the new module. The original six proof dependencies
remain needed in the new affine calculation, except GlueSheavesOfModules, which
is used directly by the global proof. AffineTildeGammaAdjunction,
QuasicoherentFiniteTypeAffine, IdealTimesQuasiCoherentAffineSections,
SpecModuleTildeSections, and ModuleLocalizationAway are no longer direct proof
dependencies of the original node; they remain dependencies of the new local node.
No claim is made that they leave the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The original DAG's affine ideal-powers dependency is stated for IdealSheafData,
whereas this item's inclusion is an arbitrary monic quasi-coherent finite-type
module into the unit module. The local step therefore needs an identification
of that general subobject with the affine ideal model; it cannot be closed by
one application of the recorded affine-sections theorem. No statement was
changed or disputed. LeanSearch returned Internal Server Error and is recorded
as unavailable, not as evidence of absence. LeanFinder, Loogle, and rg found
only lower-level ingredients. The local Stacks source files are absent on this
machine; read the cited source directly at https://stacks.math.columbia.edu/tag/01PM
and https://stacks.math.columbia.edu/tag/01PQ, as the original node also records.

## New nodes

lem-weil-pbc-ideal-power-evaluation-affine-eventually-zero: separates the affine
localization and finitely generated ideal-power calculation from globalization.
The new module states vanishing over one specified affine open without ambient
quasi-compactness. It uses the original source, statement definitions, and affine
proof dependencies, plus the proved monicity helper. Updated the original node's
proof, proof_deps, and proof_origin to describe the actual finite-cover proof.
No change record or forced adaptation was needed.

## Second reading by Q3

1. Interface preservation: PASS. Read the full diff against the repository module.
   The sole existing theorem signature is now byte-for-byte identical before `:=`;
   both existing public imports and its docstring are unchanged. No definition,
   target, existing statement, or other module was altered. No change record is
   needed. Existing node changes are exactly proof, proof_deps, and proof_origin.
2. Proof and axioms: PASS as a decomposition. Independently compiled both files
   through lcompile.py. Scratch copies with #print axioms for both declarations
   showed exactly propext, Classical.choice, Quot.sound, and sorryAx. The only
   delivered sorry is the whole proof of the named affine theorem; no forbidden
   declarations, hollow definitions, or arbitrary data construction were added.
   The global argument uses a finite affine cover, finite supremum (including the
   empty cover), monic cancellation to prove transition composition, functoriality
   to propagate local zeros, and morphism uniqueness on the cover.
3. Split statement: PASS. The affine result removes ambient compactness and
   concludes equality only over one chosen affine open. It supplies the local
   calculation rather than restating global vanishing. Checked the actual power
   construction (identity at zero, original ideal at one, images thereafter),
   and the source injectivity proof at https://stacks.math.columbia.edu/tag/01PM
   and globalization at https://stacks.math.columbia.edu/tag/01PQ. For zero ideal
   choose m >= max(n,1); for unit ideal U is all X and evaluation at one detects
   the map; zero target, zero ring, empty affine open, and n=0 are covered. For
   nonzero finitely generated J, localization kills the images of pure powers;
   a high-degree generating monomial contains a killed pure power, and linearity
   kills its multiples. The arbitrary monic ideal is identified with its section
   image, not assumed to equal an IdealSheafData object definitionally. The
   docstring and new node contain the complete mathematical proof and source.
   Repeated LeanFinder and Loogle searches with different wording and grep of
   Mathlib, upstream AlgebraicGeometry and lean/Sheaf found no matching result.
   Ideal.FG.pow and Ideal.exists_pow_le_of_le_radical_of_fg are useful algebra
   ingredients but do not discharge the sheaf/section/localization comparison.
4. Short route and pruning: PASS. Read formalPolynomial_power_mono (proved by
   induction) and the proved sheaf morphism uniqueness clause. The original
   affine dependency is for IdealSheafData, so closing the remaining local hole
   requires a genuine affine subobject and power comparison, not a short direct
   application. All global imports serve the proof and remain proof-only. The
   open affine module now imports every recorded proof-dependency module. Its
   redundant public AffineScheme import was removed. The report lists all five
   old direct dependencies replaced by the affine node; they remain on its plan.
   Read dag/units/sk-thm-p1.json: no realized statement or step is bypassed or
   changed. No module is claimed pruned from the targets' closure.
5. Nodes and accounting: PASS. The original proof steps and proof_deps describe
   the actual three-step Lean globalization. The new node has statement/proof
   dependencies, source, searches, creation, blueprint origin, chapter/unit, and
   a Lean signature matching the new module verbatim. There is one original
   hole closed and one new hole added, named above: net zero, a decomposition.

Second-reader changes: restored exact signature whitespace; added missing
proof-dependency imports to the open affine module; removed its redundant public
AffineScheme import and an extra blank line; updated import reporting and added
this independent review. The substantive global proof and new statement stand.
