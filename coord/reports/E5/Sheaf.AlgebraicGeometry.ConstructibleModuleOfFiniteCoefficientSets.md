## What changed

Completed the listed duplicate retirement for
Sheaf.AlgebraicGeometry.ConstructibleModuleOfFiniteCoefficientSets. Its existing public
theorem has exactly the same signature as the complete adopted theorem in
WeilConjectures.AlgebraicGeometry.ConstructibleModuleOfFiniteCoefficientSets.
Moved the sole DAG node's Lean attachment to that existing theorem and withdrew the
duplicate module via deleted.txt. FiniteConstructibleDirectImage changes only its proof import to the adopted module.
ProjectiveLineConstructible now reuses the complete adopted projective-line theorem,
keeping its public signature, public imports and existing docstring verbatim. Its old private
argument is removed; the source proof retains the affine-local embedding/curve route.
Updated that consumer's node to the implementation actually used.
No adopted source file or target is changed. The original stratification and unit route
are preserved by the adopted proof.

Compared public signatures verbatim, read both complete proofs, checked import directions,
searched library names with rg and msearch.py, and ran LeanFinder (only unrelated finite-type
module-sheaf results). The duplicate item and its adopted counterpart both compile. A temporary import-only check of the
adopted public theorem prints exactly propext, Classical.choice, and Quot.sound.
The adapted direct-image consumer compiles in 14.9 seconds. The original projective-line
consumer times out after 60 seconds, as does the version with only an import migration.
Diagnostic profiling with a reduced heartbeat limit exposed expensive typeclass inference
in the duplicated local argument. The source API removes that re-elaboration: the
complete adapted projective-line file compiles in 12.4 seconds. No time limit was raised,
no file was split, and no new proof obligation was introduced. The adopted projective-line
theorem's axiom check likewise lists only propext, Classical.choice, and Quot.sound.
A proof-local backward.isDefEq.respectTransparency option prevents the wrapper's
elaboration from unfolding unrelated definitions. The artifact-producing compile of both
consumer files also succeeds with the normal tool limit. The delivery dry run passed compilation and preflight. Its combined recompilation/axiom
probe timed out for ProjectiveLineConstructible (the delivery tool records that the merge
will run the probe again). A separate import-only check of the compiled delivered consumers
completed in 12.9 seconds and printed exactly propext, Classical.choice and Quot.sound for
both isConstructibleEtaleModuleSheaf_higherDirectImage_projectiveLine and
finite_directImage_constructible_and_higher_vanishing. No axiom or unproved dependency
is hidden by the simplification.

Change record: coord/changes/retire-constructible-module-finite-coefficient-sets-E5.md.

## Proved and sorry left

Zero original holes; zero holes closed; zero holes added; zero split off.
The theorem AlgebraicGeometry.Scheme.isConstructibleSheaf_of_finite_coefficient_underlying_sets
was already proved in both trees. It remains available with identical type through the
adopted source module and has only the three permitted axioms. There is no sorry in the
withdrawn item or either adapted consumer. This is a duplicate retirement, not a new proof
or a decomposition. The actual hole count for this delivery is zero.

## No longer needed

Pruned Sheaf.AlgebraicGeometry.ConstructibleModuleOfFiniteCoefficientSets and its duplicate
private finite-label chart implementation. Removed its proof import from both current
consumers. FiniteConstructibleDirectImage imports the adopted theorem's module;
ProjectiveLineConstructible uses the complete adopted projective-line result instead. The retired module's own
public imports (EtaleSheaves and Ideal.Quotient.Basic) and proof imports
(ConstantSheafSections, EtalePullbackForgetModules, EtaleInverseImageAbelianLiftHom,
ConstructibleSheaf.Pullback, and Point.ConstantSheaf, all under WeilConjectures;
Ideal.Quotient.Basic is under Mathlib) disappear
with its duplicate implementation; the adopted source retains its required imports.
The existing item node now attaches to the proved source declaration. Parent plans still
using it remain supported by that attachment. The projective-line node removes its own
now-unused edge to the item, as its adopted proof works directly with modules.
Its local proof also no longer needs lem-fin-finite-over-projective,
lem-sbc-higher-direct-image-forget-comparison or lem-weil-pbc-finite-local-abelian-forget;
these nodes are not withdrawn. The obsolete top-level tool_uses entry
lem-sbc-higher-direct-image-forget-comparison is removed from that consumer node.

Removed the projective-line private helpers abelianSetPullbackIso,
constructibleAbelian_underlyingSets, module_constructible_of_abelian,
constantModule_curve_constructible, and curve_constructible_affine. Removed its proof
imports FiniteCancellation, TargetLocal, ConstructibleSheaf.FiniteTypePushforward,
ConstructibleSheaf.DenseOpenUnit, ProjectiveCurveFiniteGroup, FiniteOverProjective,
FiniteLocalAbelianForget, HigherDirectImageForgetComparison, ProjectiveSpace.Curve,
Mathlib.AlgebraicGeometry.Morphisms.Integral and Mathlib.GroupTheory.Schreier (paths under
WeilConjectures or Sheaf as in the original file), replacing the whole local proof route
by WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Projective. The retained comparison
import supports the unchanged constructibility convention. The source proof still uses
the unit's prescribed embedding/finite-cover/curve argument; no unit-level step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a remaining sorry, but this item currently has none.
The current retirement inventory explicitly lists it as a zero-hole duplicate repair.
The previous retirement wave deferred it because a consumer was in a pending landing.
Both current consumers are now unclaimed. The inventory's Sheaf FinitePushforwardFiniteStalkModule
consumer is already absent; its adopted source counterpart already uses the source theorem.
There is no rework/quarantine row or open E5 return for this item. The remaining DAG
attachment pointed at the duplicate instead of the adopted theorem; this delivery fixes it.
The DIFFERENT inventory marker concerns private helper hypotheses, not the public theorem.

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
