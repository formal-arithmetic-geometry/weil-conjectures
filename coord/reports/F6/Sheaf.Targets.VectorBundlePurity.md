## What changed

Proved both original theorems in Sheaf.Targets.VectorBundlePurity, with the original
statements and visibility. The parent constructs finite Tate descent, proves its coefficient
annihilator, bounds the finite Tate coefficient, supplies its D+ representative and uniquely
specified pro-etale realization, and inverts the actual compact-support projection map.

The new module Sheaf.AlgebraicGeometry.VectorIntegrationMate proves that the
actual ordinary unbounded integration adjunct is invertible from the named tensor-counit
comparison. Its unit case follows the
normalized projective/affine adjunction, coordinate-tower induction and bundle-frame
restriction route. For arbitrary K, explicit adjunction and projection naturality factor
the actual map through that unit adjunct and the canonical tensor-counit mate. The latter
is reduced to the separate coefficient-first tensor-counit lemma. Its inverse-braiding
calculation and finite-module specialization are both proved. The
source library supplies the orientation-free smooth tensor map. The source theorem is still sorry upstream; this delivery
proves from that existing declared dependency and does not claim its transitive discharge.

The projection definition delegates its identical signed canonical construction to the
existing compactProjectionMapCoeffFirst wrapper to avoid repeated concrete monoidal-instance
comparisons. See coord/changes/vector-bundle-purity-projection.md. No consumer changes are
needed. Local proof options and irreducibility attributes control expensive elaboration.

## Proved and sorry left

Original holes closed (2 of 2):

- AlgebraicGeometry.Etale.vectorBundlePurityInvertiblePower.
- AlgebraicGeometry.Etale.vectorBundlePurity.

New proved theorem: AlgebraicGeometry.Etale.vectorIntegrationMate_isIso
(lem-amb-vector-integration-mate), proved from the tensor-counit lemma.

New proved theorem: AlgebraicGeometry.Etale.tensor_counit_adjunct_isIso in
Sheaf.AlgebraicGeometry.VectorIntegrationTensorCounit
(lem-amb-vector-integration-tensor-counit). Its statement concerns an arbitrary compactifiable
morphism and the canonical tensor map, independently of Tate descent, vector-bundle
normalization or the unit integration adjunct. The proof establishes the general bifunctor
mate calculation, proves its unit compatibility with explicit sheaf instances, and specializes
to finite module coefficients.

Original holes closed: 2 of 2. Holes added: 0. Holes left in all three delivered modules: 0.
Both new helper lemmas are fully proved; no unfinished statement is split off.
Existing dependencies, including exists_dualizingComplex_iso_and_tensor, retain their own
proof obligations in their original modules.

Edge cases checked: rank zero uses the identity affine adjunction and the tensor unit;
empty bases and empty trivializing covers require no chosen point. The arithmetic argument
also holds for zero coefficient rings. No boundedness or Tor restriction is imposed on K.

## No longer needed

The separate lem-amb-vector-projective-completion / VectorProjectiveCompletion step is
unnecessary: vectorIntegration_geometry and the chosen Nagata compactification supply the
same compact support used in integration and its ambient adjunction.

The arbitrary-K open-projection compatibility calculation is replaced by an explicit
global tensor-naturality factorization. Thus these separately stated steps are not used:
lem-amb-shriek-projection-open-restriction (CompactSupportProjectionOpenRestriction),
lem-amb-shriek-open-exchange-adjoint (EtaleShriekOpenExchangeAdjoint), and
lem-amb-shriek-tensor-composition (ShriekTensorComposition). The proof still uses ordinary
compact-support independence/composition, the normalized affine-space trace and its specified
projective-line adjunction, exact inverse image and cohomology detection.

Removed direct imports from the parent (some remain available transitively through the
published interfaces; this list does not claim that their entire modules leave closure):

- Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
- Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType
- Mathlib.AlgebraicGeometry.Noetherian
- Mathlib.CategoryTheory.Adjunction.Basic
- Sheaf.AlgebraicGeometry.CompactSupportProjectionOpenRestriction
- Sheaf.AlgebraicGeometry.CompactSupportSiteComparisonOpen
- Sheaf.AlgebraicGeometry.CompactifiableOverField
- Sheaf.AlgebraicGeometry.DerivedCategories
- Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
- Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization
- Sheaf.AlgebraicGeometry.EtaleShriekOpenExchangeAdjoint
- Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact (withdrawn upstream; its source
  replacement WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact is retained)
- Sheaf.AlgebraicGeometry.ExactUnboundedExchange
- Sheaf.AlgebraicGeometry.IsIsoIffOfJointlySurjectiveEtaleFamily
- Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
- Sheaf.AlgebraicGeometry.ShriekTensorComposition
- Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
- Sheaf.AlgebraicGeometry.VectorProjectiveCompletion
- Sheaf.CategoryTheory.RingedSliceExtensionTensor
- Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
- WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules
- WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
- WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
- WeilConjectures.SixFunctors.Etale.Derived.Coefficients
- WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
- WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
- WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
- WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
- WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale

The mate also omits unused direct imports for RingedSliceExtensionTensor,
RingedTopoiCanonicalTensorPullbackOfUniverses, CompactSupportProjectionOpenRestriction,
EtaleShriekOpenExchangeAdjoint, ShriekTensorComposition and ProperProjectionFormula.
The canonical exceptional open-base-change theorem is imported from the source library
rather than reproved privately. The parent replaces the direct public LowerShriekLeftAdjoint import with
EtaleExceptionalAdjoint, which publicly reexports LowerShriekLeftAdjoint, and adds
CompactProjectionExchange publicly for the projection definition.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox report and node described an unfinished mate. The retained proof now
proves it through the unit calculation and the now-proved separate tensor-counit lemma.
Earlier assertions of zero remaining holes were premature; the final tensor-counit
specialization has now been proved, and the actual final count is zero.
The resumed audit also repaired the new node’s truncated Lean signature.
The earlier explicit evaluation functor call used an obsolete extra argument; the current
proof uses the evaluation functor at the coefficient object. Existing affine-space and
smooth tensor declarations supply the geometric inputs; the categorical
comparison is proved below them. No target signature changes or new target assumptions
are used.
The general smooth theorem supplies only the canonical tensor factor, while the required
normalized Tate orientation is still proved by the prescribed affine/bundle route.

## New nodes

lem-amb-vector-integration-mate records the now-proved ordinary normalized mate lemma.
Its statement is strictly part of the parent: it does not assert coefficient descent,
arithmetic annihilation, bounded realization, normalization data or pro-etale realization.
The node proof records the actual unit calculation and tensor-naturality factorization,
including reuse of the source smooth tensor theorem as a general tool. Searches in the
retained searches.jsonl cover LeanSearch, LeanFinder, Loogle and grep. Change record:
coord/changes/vector-bundle-purity-projection.md.

lem-amb-vector-integration-tensor-counit is the separate inverse-braiding tensor-counit
comparison described above, in its own module. Its source is the generic braided mate
calculation of SmoothTensorDuality, with the braidings inverted. The statement has been
checked at identity maps, empty schemes and the zero ring; it has no smoothness or
boundedness hypothesis.

Validation: all three final modules compiled in import order, with no errors or warnings:
tensor-counit 25.3 seconds, integration mate 41.7 seconds, parent 54.8 seconds.
The final zero-hole dry run passed: commit 31c6d78d9d, review class CODEX.
The tool deferred axiom probes for the tensor-counit and parent modules after their
60-second timeout; merge repeats those probes. All private helpers are proved.
LeanSearch, LeanFinder, Loogle and source grep are recorded for both new nodes.

The unchanged textual consumer Sheaf.Paper.FiniteRingSectionDeformation was also checked
against the published library and the sandbox overlay. Both checks reached the same
60-second timeout without a compiler diagnostic; no consumer adaptation was made.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
