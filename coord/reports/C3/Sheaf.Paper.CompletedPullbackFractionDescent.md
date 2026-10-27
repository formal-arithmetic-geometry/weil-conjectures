## What changed

Implemented completed pullback fraction descent using the existing normalized coefficient
and realization interfaces. The ordinary pullback receives its constant-ring linearity
from its adjunction with actual direct image. The specified strict comparison transports
that structure to completed pullback. ScalarLocalization.transport constructs the raw
rational functor; module localization supplies the torsion-sensitive fraction laws.
The comparison extension uses the original components and tensor induction.

Public statements, definitions, and public imports are unchanged. Added private proof
imports of PbcScalarRestriction, PbcActualStrictPullback, CompletedTowerPullback,
PbcScalarTriangulation, ContinuousCoefficientBasic, and PbcRationalTransport to expose
the actual adjunction, unit, and scalar interfaces. Updated the item node to describe
this route. The item compiled with lcompile.py in 40.6 seconds.

## Proved and sorry left

Closed the original hole in
AlgebraicGeometry.Scheme.CompletedPullbackFractions.completedPullbackFractionDescent
(blueprint: lem-per-completed-pullback-fraction-descent). All nineteen Descent fields
are constructed and proved. Holes closed: 1 of 1. Holes added: 0. Sorries left in the
item module: 0. No new modules or nodes were added. Existing imported statements are
used according to the stage-3 contract; no dependency proof is duplicated here.

## No longer needed

The proof avoids the K-flat-resolution and general ringed-topos derived-pullback
computations: the published ordinary pullback already has the required adjunction.
It also avoids localization/inverse-image coherence: rationalPull already uses the
normalized continuous coefficient map, and its adjunct preserves constant functions.
Thus lem-pc-kflat-resolution, lem-weil-pbc-ringed-topoi-derived-pullback, and
lem-weil-pbc-localization-inverse-image-coherence are removed from this item's proof route.
Removed proof imports:
Sheaf.Paper.RingedTopoiDerivedPullbackIndependent;
Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients;
Sheaf.CategoryTheory.LocalizationInverseImageCoherence;
Sheaf.CategoryTheory.ScalarLocalizationCoefficientActions;
Sheaf.AlgebraicGeometry.ProEtaleInverseImage;
Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer;
Mathlib.Algebra.Module.LocalizedModule.Basic.
The last three remain available through the interfaces actually used; no duplicate direct
import is needed. Mathlib.RingTheory.Localization.BaseChange remains the algebraic input.
The top-level tool approvals removed are lem-pc-kflat-resolution,
lem-weil-pbc-ringed-topoi-derived-pullback, and
lem-weil-pbc-localization-inverse-image-coherence.
The proof-only edges for def-pur-sheaf-tensor-product,
def-weil-pbc-bounded-constructible-complete, def-weil-pbc-ringed-section-localization,
and def-weil-pbc-scalar-localization-coefficient-actions are also removed from
proof_deps. The first three retain their statement dependencies. The scalar action
used for rational module sheaves is the action carried by the supplied realization
witnesses, rather than the separate scalar-localization-coefficient action interface.
This is pruning of this item's direct route; no global unreachability is claimed.
No upstream declaration or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original planned K-flat scalar calculation is unnecessary given the existing
linear direct-image interface and its adjunction. Likewise the canonical rational
coefficient map permits a direct constant-section argument. These are shorter proof
routes, with the same completion comparison, scalar actions, and fraction relations.
The old quarantine row does not authorize withdrawing the current live source; the
existing module and Lean attachment are retained.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
