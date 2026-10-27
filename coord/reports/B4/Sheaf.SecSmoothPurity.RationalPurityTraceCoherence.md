## What changed

Restored `lean/Sheaf/SecSmoothPurity/RationalPurityTraceCoherence.lean` from its
quarantine archive. Preserved every declaration and the five public imports.
Explicitly enabled both backward transparency checks (overriding the package default)
and added file-local
irreducibility/instance settings. The three trace maps have explicit result types
with the same canonical maps; the support component has an explicit target
scheme and a proof-term elaboration boundary. These changes repair elaboration
without changing the mathematical data or weakening any statement.

Added private imports of `Mathlib.Data.Nat.Prime.Infinite` for the explicit auxiliary
finite-field datum, `Sheaf.Paper.CanonicalTateComparisons` for the exact existing
pullback-unit theorem, and `Sheaf.Paper.PositiveRootTensorProduct`
for normalized tensor multiplication. Retained the private residue-Tor and intrinsic
twist imports used by the proof. A private `import all` of
`Sheaf.Algebra.Homology.FlatSingleDerivedNormalization` exposes its already proved
degree-zero K-flat and flat-term helpers for the good-complex proof.

Reused the existing root-normalized line pullback and pullback-unit lemmas.
The good-complex proof combines local rank one, flatness of powers and the proved
flat-single helpers; it explicitly supplies the existing rank-one proof.
Proved finite-Tor membership by the existing residue-Tor characterization and
single-complex comparison, inverted the normalized tensor multiplication with a
complete uniqueness argument, and proved even-shift addition by integer algebra.
Private transparent abbreviations use the native section-module action with its
ring specified explicitly; they are confined to these theorem proofs. The
sheafification linearity argument fixes the existing site and module universes.
Updated the node's proof/dependencies to record the auxiliary route while retaining
its unfinished substantive trace/composition/descent plan. No new node or hole.
The model trace is written as `F.map gamma.hom` followed by the same adjunction
counit, which equals the original inverse Hom-equivalence by
`Adjunction.homEquiv_symm_apply`. The existing `commonCategory_eq` transports stage
Hom types explicitly; no stage category or scalar extension is replaced.
The change record is `coord/changes/B4-rational-purity-trace-coherence-restoration.md`.

Focused tensor-proof checks use lcompile.py. The required delivery command
compiles the complete restored module at its canonical path, checks axioms and
runs preflight before pushing. Both transparency checks are explicitly true.
Synchronous elaboration avoids concurrent normalization of the large derived
constructions; CanonicalTateComparisons uses the same setting. No compiler limit
is raised and no delivered file is split. The packet retains all 41 public
declarations and five public imports, with no profiling or diagnostic commands.

## Proved and sorry left

Six of the original eight holes are closed, with no added holes:

- `WeilConjectures.RationalPurityCoherence.linePull_existsUnique`: the existing
  `sfOrientationIntegralLineMaps_existsUnique` has precisely this formula.
- `WeilConjectures.RationalPurityCoherence.lineAdd_existsUnique`: invert the existing
  uniquely normalized `positiveRootTensorProduct_existsUnique`; reconstruct its
  two-scalar multiplication formula from the split formula by coefficient
  linearity and tensor balancing to prove uniqueness of the inverse.
- `WeilConjectures.RationalPurityCoherence.lineSingle_good`: rank-one flatness of the
  actual coefficient-twist power and the proved `single_kFlat`/`single_flat_terms`
  helpers of `FlatSingleDerivedNormalization`.
- `WeilConjectures.RationalPurityCoherence.lineSingle_finiteTor`: membership of the
  actual twist, transported by `singleFunctorIsoCompQ`, and `integral_residue_tor`.
  The auxiliary finite-field datum is explicitly constructed using a prime above l;
  no characteristic condition on the scheme or arbitrary unproved witness is used.
- `WeilConjectures.RationalPurityCoherence.linePullAugmentation_isIso`: existing
  `CanonicalTate.integralPullUnit_isIso` on the same normalized augmentation.
- `WeilConjectures.RationalPurityCoherence.evenShift_add`: `Nat.cast_add` and `mul_add`.

The two remaining holes are unchanged named public theorems, all attached to
`prop-pur-rational-purity-trace-coherence`, with their original complete proof
plans retained in the docstrings:

- `WeilConjectures.RationalPurityCoherence.commonSupportComposition_existsUnique`.
- `WeilConjectures.RationalPurityCoherence.rationalPurityTraceCoherence`.

The imported canonical-line and residue-Tor theorems retain their own obligations;
this delivery neither moves nor duplicates those holes. The main coherence package
is not claimed proved.

## No longer needed

No node, unit step or module is withdrawn. The original main proof plan remains
needed for the two open theorems, so none of its declared dependencies is pruned.
The following unused private proof imports are removed from the restored file;
the proof imports it actually uses are retained or added explicitly:

- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`.
- `Sheaf.Paper.FiniteSmoothPullbackExchange`.
- `Sheaf.Paper.IntegralCompactSupportCoefficientComparison`.
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`.
- `Sheaf.Paper.IntrinsicQbarCategory`.
- `Sheaf.Paper.PbcDescentFunctors`.
- `Sheaf.Paper.PbcRationalCategory`.
- `Sheaf.Paper.PbcRationalTransport`.
- `Sheaf.Paper.PbcScalarExtension`.
- `Sheaf.Paper.PurAdicReconstruction`.
- `Sheaf.Paper.PurityCompositionCoherence`.
- `Sheaf.Paper.PurityFiniteSetting`.
- `Sheaf.Paper.QcqsCompactSupportRealization`.
- `Sheaf.Paper.RationalPurityPresentation`.
- `Sheaf.Paper.SmoothTrace`.
- `Sheaf.SixFunctors.RationalOperations`.
- `WeilConjectures.EtaleCohomology.Purity.Smooth.Reduction`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.

These are import removals, not claims that every named module disappears from the
transitive target closure. All public imports are retained verbatim.

## Where the brief, the DAG or earlier work was wrong

The assigned live source is absent because of the documented quarantine, not
because its mathematics was withdrawn. Its archive and DAG attachment are preserved.
The root-pullback and pullback-augmentation auxiliary obligations
already have exact existing declarations. The good-single obligation follows
from proved degree-zero flatness helpers and the existing rank-one theorem;
reproving their constructions locally is unnecessary. The archived permissive elaboration commands also need adjustment
to the current scalar-localization/category interfaces. No false statement or
missing geometric hypothesis was found, and no target statement is changed.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
