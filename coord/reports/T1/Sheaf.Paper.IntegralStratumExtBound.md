## What changed

Restored the assigned source from its rework quarantine without changing the public
statement, public imports, name, universes, or DAG attachment. The shared tree restored
it during this session as well. Replaced integral_stratum_ext_bound's proof hole by a
complete Lean combination of a finite-reduction estimate and reduction-limit
reconstruction. The first clause derives finite cohomological dimensions, uses shifted
product extensionality and exactness of the Roos triangle, and computes the +3 bound.
The second clause applies the existing stratum filtration, removes its zero shifts,
then proves uniformity by induction using maxima and contravariant Hom exactness.

The actual positive reductions are the existing integralReductionFunctor, including
degree -1 cohomology for torsion sheaves. Added two statements for genuine remaining
parts of the source argument, each with a complete proof in words and a matching node.
No definition, target statement, existing shared interface, or foreign module changed.

## Proved and sorry left

Closed original hole: AlgebraicGeometry.ProEtale.CondensedRing.integral_stratum_ext_bound.
This is a decomposition, not a completed geometric Ext proof: one upper hole is closed
using two new, strictly narrower theorem holes. The Roos one-degree loss, dimension
finiteness and finite-filtration combination are proved in Lean in the item module.

Added holes, and all sorries left in the delivery:

- AlgebraicGeometry.ProEtale.CondensedRing.integral_constructible_reduction_limit
  in Sheaf.Paper.IntegralConstructibleReductionLimit: identify a constructible sheaf
  with the limit of its actual positive derived reductions; independent of stratum data.
  Node: lem-sf-integral-constructible-reduction-limit.
- AlgebraicGeometry.ProEtale.CondensedRing.integral_stratum_reduction_ext_bound
  in Sheaf.Paper.IntegralStratumReductionExtBound: the finite-level c+s+2 estimate;
  no inverse-limit passage and no general-source filtration conclusion.
  Node: lem-sf-integral-stratum-reduction-ext-bound.

Original item: 1 sorry. Item after change: 0. New theorem holes: 2.
All private helpers have complete proofs; no sorry in a definition or instance.
Validation: lcompile.py --all accepted all three delivery modules with exit code 0.
The service separately enforces the 60-second Lean runtime limit; the displayed
per-file elapsed figures also include setup/cache work.

## No longer needed

The existing public imports are preserved. Removed unused private imports from the
item (their required geometric roles remain in the new finite-reduction/reconstruction
nodes, so this is relocation of proof obligations, not a claim their mathematics is
unnecessary):

- Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
- Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
- Mathlib.CategoryTheory.Monoidal.Closed.Basic
- Mathlib.LinearAlgebra.FreeModule.PID
- Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
- Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
- Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison
- Sheaf.AlgebraicGeometry.ClassicalDerivedEquivalence
- Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison
- Sheaf.AlgebraicGeometry.ModuleCohomologyConventions
- Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
- Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
- Sheaf.AlgebraicGeometry.ProEtaleProductsDerived
- Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
- Sheaf.CategoryTheory.BoundedHeartAmplitude
- Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
- Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect
- Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
- Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
- Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
- Sheaf.Paper.CartesianCoefficients
- Sheaf.Paper.CompletedConstantSheafReduction
- Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
- Sheaf.Paper.FormalClosedSupport
- Sheaf.Paper.IntegralConstructibleHeart
- Sheaf.Paper.IntegralCriterionReductions
- Sheaf.Paper.IntegralModels
- Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
- WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
- WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
- WeilConjectures.CategoryTheory.TruncationTriangle
- WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs

The old individual steps 2--10 are now grouped into the two new nodes, and the item
uses only their interfaces, dimension finiteness, the filtration, and Hom exactness.
The derived-dual formula need not be reconstructed again in the item: the proved
integral_stratum_hom_formula supplies it for the finite-level subargument. In
particular the manual support-adjunction/tensor-duality imports are unnecessary here.
No module is withdrawn, no DAG node is deleted, and no lower theory is claimed
unreachable: dependencies moved below the new nodes remain needed there. No global
module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The item was absent initially: coord/rework.tsv identifies its preserved quarantine
source and a false-trace import-chain reason. That absence did not authorize withdrawal.
The original source, public signature and attachment were restored in the sandbox;
the shared tree subsequently restored the source independently.

The original DAG step 4 rederived a formula that det-lem-int-ext-formula now already
proves, including torsion via the derived dual. That proved formula is reused. The
original derived-limit discussion can be made directly on Hom using shifted product
projections, as in its corrected step 11; no immersion inverse image is commuted with
a limit. The two new interfaces are needed to join existing declarations with their
spectral-coefficient/actual-reduction conventions, not copies of the full theorem.
Edge cases checked: empty scheme, empty or zero stratum, zero sheaf, torsion source and
target, and zero-length filtration. Positive indexing n+1 excludes the zero quotient.
All geometric bounds are natural numbers, so negative Ext degrees introduce no new
vanishing obligation. Target signatures are untouched.

## New nodes

- lem-sf-integral-constructible-reduction-limit, module
  Sheaf.Paper.IntegralConstructibleReductionLimit.
- lem-sf-integral-stratum-reduction-ext-bound, module
  Sheaf.Paper.IntegralStratumReductionExtBound.

Both come from the current blueprint's paragraph (2), remain in the same unit, and
carry natural-language proofs and Lean statements verbatim. Mathlib search by natural
language, type/name query and source regex found generic limit and amplitude APIs,
not either geometric interface. A project-wide node-title and source search found
other coefficient presentations and reconstruction of morphisms, but no matching
statement for these actual reductions of an arbitrary constructible integral sheaf.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
