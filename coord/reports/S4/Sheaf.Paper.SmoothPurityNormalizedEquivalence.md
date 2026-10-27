## What changed

Reduced AlgebraicGeometry.ProEtale.sp_normalized_equivalence to three independent,
strictly smaller comparison steps. The Lean assembly proves exact scalar forgetting,
the shift and triangulated structures, the reverse constructibility implication via
spTower_reconstruction, and the final equivalence of the specified full subcategories.
Validation: all three helper modules compile; the final item compiles cleanly with
the sandbox dependency artifacts. Existing public signatures and the bodies of all five
moved definitions plus SpNormalizedEquivalence compare identical to the source.
No cycle through the item or a new node was found in the overlaid dependency graph.

It uses Adjunction.restrictFullyFaithful, checks that the restricted unit and counit
map to the actual ambient components, reflects their invertibility, and applies
toEquivalence. The two required equalities of functors are definitional.

The completeness conjunct of sfIntegralConstructible is bridged to the public
IntegralOnSlice.IsComplete none predicate by sfDerivedComplete_iff_legacy, using a
concretely constructed auxiliary finite-field datum of characteristic different from ell.

The five completed-tower definitions moved verbatim to SmoothPurityCompletedTowerRoos
and remain publicly available from the original module. This is an interface extraction
needed for the new comparison statements, not a change of construction. See
coord/changes/S4-completed-tower-comparison-interface.md. No consumer edits are needed.

## Proved and sorry left

Original hole closed in the assembly:
- AlgebraicGeometry.ProEtale.sp_normalized_equivalence
  (det-sp-normalized-equivalence).

Three holes added, each the whole proof of a named public theorem in its own module:
- AlgebraicGeometry.ProEtale.spCompletedTotalLimit_roos
  (lem-sp-completed-tower-roos).
- AlgebraicGeometry.ProEtale.spCompletedReduction_limitAdjunction
  (lem-sp-completed-reduction-adjunction).
- AlgebraicGeometry.ProEtale.spCompletedReduction_constructible
  (lem-sp-completed-reduction-constructible).

This is a decomposition, not a net proof gain: one original hole, three added holes,
zero holes in the item, net minus two in the delivered modules. No definition contains
a hole or chooses arbitrary data from an unproved existence theorem.

Proved without new holes: spCompletedStrictTowerLimits, spCompletedStrictTowerColimits,
spCompletedStrictTowerAdditive, spCompletedTotalLimitShift and
spCompletedTotalLimit_triangulated, plus the private completeness comparison and
full-subcategory assembly. The only remaining mathematical arguments are the canonical
adjunction transport and reconstruction maps, forward constructibility comparison,
and transport of the fixed-ring Roos triangle. Each is strictly less than the original
statement; no new lemma asserts the final constructible equivalence.

## No longer needed

Removed proof-only imports from the item:
- Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
- Sheaf.CategoryTheory.SystemLevelLeftExtension
- Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
- Mathlib.Algebra.Homology.HomotopyCategory.KInjective
- Mathlib.CategoryTheory.Limits.Final
- Mathlib.CategoryTheory.IsConnected
- Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
- Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
- Sheaf.Paper.NormalizedDVRTower
- Sheaf.Paper.NormalizedDVREffectivity
- Sheaf.Algebra.Homology.ChangeOfRingsKFlat
- Mathlib.CategoryTheory.Triangulated.Pretriangulated
- Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
- Sheaf.Paper.ProEtaleConstructibleSheaf
- Sheaf.Paper.IntegralResidueTor
- Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
- Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
- Sheaf.Paper.FiniteFieldFiber

All original public imports are retained to preserve the importer interface. No source
library declaration or module is removed. No existing node is withdrawn. The former
proof dependencies remain needed by the new comparison nodes, so they are relocated
in the proof plan rather than declared globally pruned. The original ten-step docstring
is retained as the source plan; the DAG now describes the actual Lean assembly and
locates its unfinished steps in the three new modules.

## Where the brief, the DAG or earlier work was wrong

The node's prose is mathematically usable, but several applications are not direct Lean
applications: the uniformizer strict-system category differs from the ell-power tower
category; the intrinsic integral constructibility predicate differs from the
constantModelBoundedConstructible input of R.constructible; and the fixed-ring Roos
triangle must be transported through the canonical evaluation isomorphisms. These
comparisons are now explicit named tasks rather than hidden glue in the top proof.
No statement is disputed or weakened. The target and unit routes are unchanged.

Edge cases: the arithmetic step includes e=1, positive levels n+1, equal transition
indices, and ramification e>1. The ambient adjunction step has no boundedness, Tor or
Noetherian assumption. Only the forward constructibility step assumes Noetherian T;
the empty scheme is not excluded. Arbitrary D and R retain all their supplied
normalizations; the split does not choose an unrelated reduction or total limit.

Searches: LeanFinder found derived-category fraction and short-exact triangle tools,
not the coefficient comparisons. Loogle and LeanSearch found restrictFullyFaithful and
toEquivalence for the proved final assembly. Mathlib grep found no matching adic tower
comparison. The existing arithmetic interpolation and reconstruction declarations were
read and are used in the proof plans of the new comparison nodes.

## New nodes

lem-sp-completed-tower-roos: exact completed scalar forgetting and the canonical
projection-normalized Roos triangle after evaluation comparison. The module contains
the moved interface, proved exactness/triangulated facts, and one remaining theorem hole.

lem-sp-completed-reduction-adjunction: transport the uniformizer adjunction through
arithmetic subsequence restriction, with invertibility of its actual unit and counit.
It deliberately excludes constructibility and the final equivalence.

lem-sp-completed-reduction-constructible: the forward mapping of the existing integral
constructibility predicate into normalized constructible finite-Tor ell-power towers.
The reverse direction is already assembled from the existing reconstruction theorem.

Change record: coord/changes/S4-completed-tower-comparison-interface.md.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
