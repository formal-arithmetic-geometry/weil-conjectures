## What changed

Proved `AlgebraicGeometry.Scheme.Modules.coherent_ideal_power_supported_on_closed`
in `Sheaf.AlgebraicGeometry.CoherentIdealPowerSupportedOnClosed`, with its signature
and all public imports unchanged. Added a proof-only import of
`CoherentSupportVanishingIdealNilpotence` (using `import all` for its proved general
private helpers and the declarations its proof imports). The second reading removed
five redundant explicit proof imports, listed below.
Updated the theorem docstring and the existing node's proof, proof dependencies,
and proof origin to the actual route.

The proof chooses a finite affine cover of the complement of C directly in X.
Affine support containment gives a radical-annihilator bound. Finite generation
and the finite supremum give one exponent annihilating every covering section
module. The general affine power and multiplication helpers identify the actual
recursive powers and image products. Injectivity of the image inclusion makes
product sections zero; quasi-coherence and restriction-stalk comparison make all
product stalks outside C zero. No data definition or intermediate statement was
changed, and no other module was adapted. The unit's realized lists are empty;
its statement and proof route are unchanged.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.Scheme.Modules.coherent_ideal_power_supported_on_closed`
(blueprint: `lem-pc-s3-coherent-ideal-power-supported-on-closed`).
Added 0 holes. No `sorry` remains in the delivered module, and no new module is
added. This is a proof from existing declarations, not a decomposition.

Local single-file compilation passed without warnings. The finite supremum and
power-section helpers include exponent zero, so the empty complement and zero
module require no exceptional hypotheses.

## No longer needed

No original import was removed: all four public imports supply the unchanged
statement or its definitions. The second reading removed these redundant proof
imports from the first draft; their declarations remain available through the
`import all` helper module, and their nodes remain in the proof plan where used:

- `Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`
- `Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportClosed`
- `Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections`
- `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`
- `Mathlib.RingTheory.Finiteness.Ideal`

No global closure-pruning count is claimed.
The following old planned direct proof dependencies are no longer needed by this
proof and were removed from its node's `proof_deps`:

- `lem-weil-pbc-noetherian-open-subscheme-noetherian`: no open subscheme is formed.
- `lem-weil-pbc-coherent-module-local-on-open-cover` /
  `Sheaf.AlgebraicGeometry.CoherentModuleLocalOnOpenCover`: F is never restricted.
- `lem-weil-pbc-module-restriction-open-immersion-colimits`: no colimit comparison
  is used; the final stalk comparison is Mathlib's `restrictStalkNatIso`.
- `lem-weil-pbc-quasi-coherent-finite-type-affine` /
  `Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`: its needed support
  consequences are supplied by `FiniteTypeModuleSupportClosed`.
- `lem-weil-pbc-finite-module-support-annihilator`: subsumed by the sheaf affine
  support formula in `FiniteTypeModuleSupportClosed`.
- `lem-weil-pbc-quasi-coherent-ideal-zero-set-affine` /
  `Sheaf.AlgebraicGeometry.QuasiCoherentIdealZeroSetAffine`: use Mathlib's
  `coe_support_inter` and `fromSpec_image_zeroLocus` directly.
- `lem-weil-pbc-ideal-module-product-stalk`: no product-stalk calculation is used;
  its module remains a required public import for the actual product and powers.
- `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections` /
  `Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`:
  reuse the cycle-free generalized affine helpers instead.

The alternative global modules `CoherentSupportPowerIdealKills` and
`IdealPowerProductRestrictionZero` were not imported. Some bypassed dependencies
remain transitively imported by existing tool modules, so these entries describe
pruning of this proof plan, not removal from the whole target closure.

## Where the brief, the DAG or earlier work was wrong

The direct planned `IdealTimesQuasiCoherentAffineSections` import creates a cycle:
it imports `WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion`, which
reaches `Cohomology.DirectImage`, `Cohomology.DirectImage.FiniteFreeComplex`,
`FinitePresentationIntegralFiltration`, `FinitePresentationSupportReductionFiltration`,
`CoherentReducibleSupportExactSequence`, and this item. The tempting
`CoherentSupportPowerIdealKills` and `IdealPowerProductRestrictionZero` routes
reach the same package and close the same cycle. `import_direction.py may`
confirmed both rejections. The cycle-free route uses the already-proved general
helpers `ideal_qc`, `powers_affine_sections`, `multiplication_range`, and
`affine_source_zero_of_sections` from `CoherentSupportVanishingIdealNilpotence`.
That node already records these helpers and their general signatures.

The mathematical statement is unchanged and no statement is disputed.
The cited Stacks Tags 01YD and 01Y9 were read on their official pages because the
local literature texts are not installed on this machine.

## Second reading by R3

1. PASS: diffed the sole delivered Lean module against the repository version.
   The existing theorem signature is byte for byte identical, including all
   hypotheses and both conclusions; its visibility and four public imports are
   unchanged. There are no delivered definitions, new declarations, adapted
   modules, or change records.
2. PASS: independently compiled the original draft without errors or warnings.
   Compiled a scratch copy after removing the five redundant proof imports and
   appended `#print axioms
   AlgebraicGeometry.Scheme.Modules.coherent_ideal_power_supported_on_closed`:
   only `propext`, `Classical.choice`, and `Quot.sound` occur, with no `sorryAx`.
   There are no remaining holes, forbidden declarations, or hollow definitions.
   Read the existing recursive power and image-product constructions and all four
   reused private affine helpers: they concern those actual constructions.
3. PASS: no statement is split off and no new node is added. Checked the radical
   containment direction and decreasing powers, the empty complement (empty
   supremum is zero), C = X, F = 0, the empty scheme, and exponent zero. All are
   covered without additional hypotheses. Choosing the local exponent is inside
   an existential theorem proof; no definition chooses arbitrary data from an
   unproved existence theorem.
4. PASS after import cleanup: read the proof from the target down to its affine
   ingredients. Independent semantic search with the query about a finitely
   generated ideal whose zero locus contains a finite module support found
   Mathlib's module-support formulas, not a sheaf concentration theorem. Searched
   lean/ with support-union, support-containment, ideal-product, and power terms.
   The global ideal-killing theorem and restriction packages do not shorten this
   route without the documented import cycle. The reused helper module's imports
   supply the five removed explicit imports, as verified by compilation. Every
   removed old direct proof dependency appears under No longer needed. Read
   dag/units/sk-thm-picard-coherence.json: its realized statement and step lists
   are empty; the unit statement and route are unchanged. No module becomes
   unreachable through this import cleanup.
5. PASS: compared the delivered existing node against the repository node; only
   proof, proof_deps, and proof_origin changed. Read the dependency declarations
   and the helper module's node, which explicitly records the general private
   helpers. The four proof steps describe the written Lean argument and their
   uses union equals proof_deps. The affine power, multiplication range, zero
   restriction, and restriction-stalk comparison are applied with their required
   quasi-coherence and section-vanishing hypotheses.

Changed only five redundant proof imports and this report. The mathematical
proof body, statement, public interface, and delivered node remain as submitted.
Closed 1 original hole, added 0 holes; this is a proof, not a decomposition.
