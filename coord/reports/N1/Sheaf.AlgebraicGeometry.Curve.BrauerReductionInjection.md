## What changed

Proved `AlgebraicGeometry.IsCurve.injective_brauer_pullback_reduction` in
`Sheaf.AlgebraicGeometry.Curve.BrauerReductionInjection`, preserving its signature.
The proof forms the kernel short exact sequence for the comparison
`i^* G_m,C -> G_m,C_red`. Exactness of the degree-two cohomology sequence and
vanishing of the kernel cohomology give injectivity of `Sheaf.H.map`.
Composing with `Etale.cohomologyMap_bijective` gives exactly the stated map.
Reduction is a universal homeomorphism because it is a surjective closed immersion;
the already proved reduction theorem supplies surjectivity and typeclass inference
supplies the integral and universally injective properties.

Added two modules, each isolating a strictly separate part of the source argument:
`Sheaf.AlgebraicGeometry.Curve.ReductionUnitsEpi` states local lifting of units,
for arbitrary schemes; `Sheaf.AlgebraicGeometry.Curve.ReductionUnitsKernelVanishing`
states the nilpotent-filtration vanishing for curves. Neither states a Brauer-group
injection. The first has no curve or cohomology hypotheses or conclusion; the second
concerns a different sheaf, the kernel of the units comparison. Their proof docstrings
include the transport across the reduction equivalence. No definition or existing
statement changed, and all existing public imports remain unchanged.

The new obligations cover the finite-type argument of the original plan. Local unit
lifting actually needs only a nil ideal, so its statement applies to arbitrary schemes.
The vanishing obligation retains the original finite-type, separatedness and dimension
hypotheses. Edge cases checked mathematically: reduced schemes have identity comparison
and zero kernel; empty schemes have zero cohomology; the filtration and affine-cover
argument do not require connectedness or positive dimension. No smoothness, properness
or algebraic-closedness hypothesis has been added.

Local compilation of all three modules succeeds. The parent proof has no remaining
`sorry`; the two new modules each have exactly one public named theorem with `:= by sorry`.

## Proved and sorry left

Proved: `AlgebraicGeometry.IsCurve.injective_brauer_pullback_reduction`
(node `lem-sc-brauer-reduction-injection`), from the two new obligations and the
existing long exact sequence and topological invariance declarations.

Remaining direct sorries, both introduced in separate modules:

- `AlgebraicGeometry.Scheme.epi_upperStarGmSheafToGmSheaf_reduction`
  (`lem-sc-reduction-units-epi`, `ReductionUnitsEpi.lean`).
- `AlgebraicGeometry.IsCurve.subsingleton_H_two_reduction_units_kernel`
  (`lem-sc-reduction-units-kernel-h2`, `ReductionUnitsKernelVanishing.lean`).

The parent is a completed reduction, not an axiom-free final result: its proof still
depends transitively on these obligations. Its combination proof constructs a short
exact sequence, obtains a preimage of any kernel class by exactness, uses subsingleton
vanishing and preservation of zero to kill that class, and composes injections.

## No longer needed

Removed proof-only imports from the parent:

- `Sheaf.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing`
- `Sheaf.AlgebraicGeometry.EtaleAffineQcoherentULift`
- `Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf`
- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`
- `WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Cech`
- `WeilConjectures.SixFunctors.Finite.Exact`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`
  (redundant direct import; its exactness declaration remains used through public imports).

The nodes `lemma-weil-pbc-finite-direct-image-exact` and
`lem-weil-pbc-finite-pushforward-cohomology` are no longer needed for this argument.
`lem-weil-pbc-closed-immersion-finite` remains a dependency: typeclass inference uses
closed-immersion finiteness to obtain integrality in `IsUniversalHomeomorphism`.
The finite-pushforward edge-map identification is replaced by topological invariance
and the canonical comparison already appearing in the unchanged target statement.
Thus `CohomologyClopen` and `Finite.Exact` are not directly imported anywhere in this
delivery. This is a local pruning claim; other targets may still need these modules.

The remaining old parent proof dependencies are no longer direct dependencies of
`lem-sc-brauer-reduction-injection`; they are retained in the proof plan of the new
kernel-vanishing obligation, rather than declared mathematically unnecessary:
`lem-weil-pbc-finite-type-over-noetherian`, `etale-proposition-etale-reduced`,
`def-sc-etale-qcoherent-module`, `lem-sc-etale-affine-qcoherent`,
`lem-sc-cech-spectral`, `pqf-lem-affine-vanishing`, and
`lem-sc-noetherian-cohomology-above-dimension`.
The epi obligation also uses reducedness of etale schemes in its natural-language plan.
The long exact sequence node remains used by the parent; its `Basic` module is
available through the public `Gm` and `TopologicalInvariance` imports.
The public import of `EulerChar` indirectly through `Curve` cannot be pruned here
without an unrelated interface change.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The original proof dependencies do not state
local surjectivity or vanishing for the particular nilpotent-units kernel. They supply
parts of the long geometric argument but do not alone give those conclusions by a
short Lean application. The two new obligations make those missing parts explicit.
The proof now works after inverse image to the reduction topos, so it needs no separate
finite-pushforward edge-map compatibility lemma.

LeanSearch returned Internal Server Error and is recorded as unavailable, not as
absence of a match. LeanFinder, Loogle, Mathlib grep and local library searches found
no direct sheaf comparison or kernel-cohomology theorem. Blueprint searches for
"reduction units kernel", "units lift", and "nilpotent Brauer" found no duplicate node.
The unit record `sk-prop-h2` has empty realization lists on the base. No unit record,
unit statement, or unit proof route was altered; the source's reduction and
nilpotent-units argument is retained.

## New nodes

`lem-sc-reduction-units-epi`: local surjectivity of the units comparison along reduction,
realized by `Sheaf.AlgebraicGeometry.Curve.ReductionUnitsEpi`. Its proof lifts units
modulo a nil ideal on the affine etale basis, then transports the epimorphism through
the exact reduction equivalence. It is independent of the curve vanishing obligation.

`lem-sc-reduction-units-kernel-h2`: degree-two vanishing of the comparison kernel,
realized by `Sheaf.AlgebraicGeometry.Curve.ReductionUnitsKernelVanishing`. Its proof
uses the original nilpotent filtration, quasi-coherent acyclicity and dimension
bound, then transports the kernel and its cohomology to the reduction topos.
Both nodes inherit the item's chapter and unit and refer to the precise source step.
No change record is needed: no existing public signature or definition changed.

## Second reading by N1

1. Compared the entire delivered parent module with the repository version. The
   existing theorem signature is byte-for-byte unchanged, and its docstring and
   definitions are unchanged. The only existing-node fields changed are `proof`,
   `proof_deps`, and `proof_origin`. The two new modules contain new theorem statements,
   not replacements of an existing signature. No target or existing definition changed.
   Verdict: pass.

2. Compiled all three modules in import order with `lcompile.py --all`, then compiled
   scratch copies with `#print axioms` for each delivered theorem. The parent has no
   direct sorry. Each child has one named public theorem whose whole proof is `by sorry`,
   exactly as listed above. No axiom, unsafe, opaque, implemented_by, extern, hollow
   definition, or kernel-check bypass occurs. The scratch axiom results are recorded
   here: all three depend only on propext, Classical.choice, Quot.sound and sorryAx.
   The delivery tool also runs the exhaustive declaration probe.
   Verdict: pass as a reduction with two explicit open obligations, not an axiom-free
   proof of the Brauer injection.

3. Read both new theorem statements, proof docstrings and nodes. The epi assertion needs
   only a nil ideal, not a uniform nilpotence exponent. The H^2 assertion needs the
   separated finite-type dimension-at-most-one curve hypotheses, all present in IsCurve.
   Checked reduced schemes (zero kernel), Spec(k[e]/(e^2)) (square-zero additive kernel),
   empty schemes (zero cohomology), and disconnected curves. The filtration uses j>=1,
   ensuring 2j>=j+1, and the long exact sequence induction needs vanishing of H^2 of
   both adjacent groups. Reduction equivalence preserves kernels and cohomology.
   Neither child merely renames the parent's hypotheses and injectivity conclusion.
   Independent LeanFinder, Loogle and grep searches used different wording. Loogle found
   a local-ring units-surjectivity primitive, but no theorem giving the scheme/sheaf
   comparison; ring nilpotence lemmas likewise do not close its geometric construction.
   Local searches of Sheaf and the upstream library found only unrelated Kummer, Hilbert
   90 and regular-generic-point results. No split-off obligation can be closed by a short
   application of those results. Verdict: pass.

4. Read the combination proof top downward: reduction supplies a universal homeomorphism,
   its cohomology map is bijective, the units comparison is epi, its kernel H^2 is zero,
   and exactness forces injectivity. All public imports of the existing parent are needed
   by its signature (in particular cohomologyMap is defined in TopologicalInvariance).
   Removed the redundant parent Basic import and the new vanishing module's redundant
   public Basic import; Gm already publicly imports that module. The no-longer-needed
   section lists all nine removed old direct proof dependencies, distinguishing the two
   finite-pushforward nodes pruned from this argument from the seven retained in the
   children's geometric plans. The unit sk-prop-h2 has empty realized lists on the base;
   its statement, steps and record are unchanged, and reduction plus the nilpotent-units
   argument retains the original mathematical route. Verdict: pass.

5. Checked new-node fields, source places, Lean names and normalized verbatim signatures,
   chapter/unit inheritance, blueprint provenance and search records. For each node,
   proof_deps is the union of the proof-step uses. The parent plan follows the actual
   Lean construction; closed-immersion finiteness remains used through typeclass inference.
   The child plans describe the genuinely pending geometric work. Added the independent
   searches to both new nodes. Verdict: pass.

Changes in this reading: repaired the epi docstring's missing nilness argument (a
reduced quotient alone does not make its ideal nil: locally, the extended ideal is
generated by nilpotent images, and every element is a finite sum of their multiples);
removed two redundant Basic imports; updated the pruning report; added independent
search records to both new nodes. No Lean proof or theorem signature needed repair.
