## What changed

Proved `AlgebraicGeometry.Etale.sf_directImage_torAmplitude` from the existing
coefficient, constructibility, derived-dimension, projection-formula and residue-test
lemmas. A proved private helper performs the finite-module/finitely-presented-module
conversion and extracts the upper cohomological bound from bounded constructibility.
The final proof combines bounded constructibility with the residue Tor criterion.

Local priorities for `CommRing.toRing`, `SymmetricCategory.toBraidedCategory` and
`sheafBraidedCategory` align the quotient-ring and tensor instance paths with the
generic lemmas and existing residue criterion. This avoids repeated unfolding during
kernel checking. No global instance, definition, public signature or visibility
changes. Temporary profiling settings were removed. The clean proof and the axiom
probe compiled without warnings during the final dry run. The probe reports no
additional axioms or direct holes.

The proof-context change is recorded in
`coord/changes/S9-direct-image-tor-amplitude-proof-context.md`.
Removing either remaining Mathlib module-sheaf import caused the 60-second timeout;
both are retained to preserve the working instance context.
Removing `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage`
fails because it declares `CategoryTheory.Functor.isGE_rightDerivedFunctor_obj`, used
for the lower cohomological bound, so this proof import is necessary.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Etale.sf_directImage_torAmplitude`
(blueprint: thm-sf-direct-image-tor-amplitude).

There are zero remaining `sorry`s in the item module. Added zero holes and split off
zero statements. All new private helpers have complete proofs. Existing dependencies
are used as declared; this delivery does not claim to close their transitive holes.

## No longer needed

Removed these proof-only imports:

- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`: already
  supplied publicly by `UpperLowerStarCoherence`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: the existing public imports
  supply the derived-category notation used here.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`: already supplied
  publicly by the finite constant projection module.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: already supplied by the
  existing upstream direct-image framework.
- `Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact`, node
  `lem-weil-pbc-module-direct-image-left-exact`: its module-encoding comparison
  theorem is unused; the ordinary direct image already has the required instances.
- `Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian`, node
  `lem-weil-pbc-module-sheaves-grothendieck-abelian`: its separate comparison theorem
  is unused; the ordinary sheaf category already has the required instances.

Removed the last two nodes from this node's proof dependencies, proof-step uses and
obsolete tool-use approvals. The unit route and the residue/projection argument stay.
Existing public imports are retained as the module's public interface. Direct imports
of `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous` and
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian` supply the instance context
previously brought in by the left-exactness comparison import. Removing either causes
the compile timeout, so both are retained. The comparison theorem itself is unused.

## Where the brief, the DAG or earlier work was wrong

The upstream synchronization had reset the final proof after restoring reducibility
of the coefficient ring caused a kernel timeout. Local ring and braiding priorities
and a generic finite-module helper suffice; no coefficient-definition repair or
adaptations to consumers are needed. The two separately stated module-encoding
comparison theorems are not needed to obtain instances for ordinary module sheaves.
The residue Tor test is now proved in the current shared sources; the earlier report's
claim that it was still `sorry` is obsolete.

The resumed sandbox's report described import pruning that its Lean file no longer
contained. Restored the recorded import removals and the two replacement Mathlib
imports, then compiled against the current sources. The theorem's signature and
the unit route are unchanged; there are no definition repairs or consumer adaptations.

The resumed dry run found a leftover profiling option; it has been removed. The
clean axiom probe required matching the braiding instance paths already used by
`ResidueTorAmplitudeTest`. Preflight also required the proof-context change record;
it records all direct importers and explains why no consumer adaptation is needed.

## Second reading by S9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
