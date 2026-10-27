## What changed

Replaced the single hole in `Sheaf.Paper.IntegralStratumReductionExtBound` by a
complete reduction to two separate source steps. The original theorem statement
and its public imports are unchanged. No existing module other than the item is
changed.

`IntegralReductionSupportAmplitude` isolates the first finite-reduction bullet:
the actual reduced target after restricted closed support has classical prime-power
torsion cohomology in [-1,c+1]. It has no source L, derived dual, or sections bound.
`IntegralDualTorsionHeartSections` isolates the other two bullets on a heart object:
dual tensor followed by derived sections has amplitude [0,s+1] on a classical
torsion sheaf. It has no ambient X, closed support, reduction, stratum extension,
or Ext assertion. Its target sheaf can be nonconstructible and have no common
annihilating exponent.

The item combines these inputs with the proved bounded-heart-amplitude theorem,
yielding [-1,c+s+2]. The proved integral stratum Hom formula, shift comparisons,
derived additive coyoneda evaluation for the regular module, the tensor-unit
comparison and tensor-Hom adjunction turn its upper vanishing into the requested
subsingleton Hom. The two private helpers are fully proved categorical arguments.

Edge cases checked in formulating the inputs: torsion N uses derived reduction,
not the ordinary quotient; zero L and N give zero objects; empty strata impose no
nonemptiness condition; c=s=0 gives exactly cutoff 2; no constructibility of the
support direct image is asserted. The unit route is retained: all three finite
reduction bullets are used and no inverse limit is interchanged here.

Validation: all three modules compiled successfully on the server. A profiled
single-file check of the item passed in 18.6 s (8.26 s of tactic execution).
The first batched check reported 53.7 s, 56.4 s and 67.7 s respectively;
the slower item timing was not reproduced by the profiling check. Profiling
options are removed from the delivered file. Delivery preflight checks the final
versions again.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.integral_stratum_reduction_ext_bound`
(node `lem-sf-integral-stratum-reduction-ext-bound`). The item module has zero
remaining holes.

Added two holes, each exactly the body of a named public theorem in its own module:

- `AlgebraicGeometry.ProEtale.CondensedRing.integral_reduction_support_amplitude`
  (node `lem-sf-integral-reduction-support-amplitude`).
- `AlgebraicGeometry.ProEtale.CondensedRing.integral_dual_torsion_heart_sections`
  (node `lem-sf-integral-dual-torsion-heart-sections`).

This is a decomposition, with one upper hole closed and two strictly smaller source
steps left, not a claim of a net reduction in the sorry count. No definition, instance,
private lemma, anonymous declaration or partial proof contains a hole.

## No longer needed

No original public import was removed and no existing module is withdrawn.
The old direct dependence on `lem-pur-rhom-global-sections`
(`Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`) is unnecessary in this
argument: the existing derived additive coyoneda comparison and tensor-Hom
adjunction compute the same group directly in the module-object category. This
avoids a separate transport to sheaves of modules with independent universes.
It makes no assertion that the module is unused elsewhere in the project.

The other geometric and coefficient dependencies of the original plan are retained
in the two new nodes, or used directly (the stratum Hom formula and bounded heart
amplitude). Their absence as direct imports of the item is delegation to those
source steps, not pruning or withdrawal. No UNIT statement or realized step is
bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement or incorrect target signature was found. The original proof
plan was mathematically useful but did not contain a declaration for the actual
restricted-support estimate or for the heart-only dual sections estimate. The
nearby `uniformConstructibleExtTorsion` is insufficient: its source and target are
lisse lattices, and it uses ordinary rather than derived reductions. In particular
it cannot be substituted for torsion constructible inputs.

Searches via msearch LeanFinder, Loogle, LeanSearch and grep found only generic
cohomology and Hom vanishing APIs in Mathlib. The existing project Hom formula,
finite-filtration theorem and derived coyoneda comparison are reused. Search
results and source locations are recorded in the two new nodes.

## New nodes

`lem-sf-integral-reduction-support-amplitude` records the length-one reduction,
finite-coefficient comparison, relative cd estimate and support triangle, stopping
before dual tensor and sections. Its proof dependencies retain the original plan's
coefficient-restriction compatibility and all the torsion hypotheses.

`lem-sf-integral-dual-torsion-heart-sections` records the two-term dual resolution,
classicality after finite reduction and the absolute cd estimate only on a heart
input. The finite filtration extending this estimate to the support complex is
proved in the item, rather than hidden in the new hole.

No change record is needed: no existing signature, definition or public interface
is changed.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
