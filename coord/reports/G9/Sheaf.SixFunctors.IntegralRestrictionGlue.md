## What changed

Proved integralRestrictionGlue without changing any existing public signature or definition.
The proof combines finite-open boundedness and constant-model cohomology descent, the integral
exceptional inverse image on a finite affine-chart cover, and restriction of the given Brown
adjunction. The restricted Hom equivalence is proved literally equal to the given one.
Three new component modules and nodes contain complete proofs; none adds an open obligation.

The chart argument uses the rational restrictionLocal theorem only for its geometric cover
clause. All functor comparisons and preservation results use integral coefficients: the actual
open adjunction, integral compact-support composition, uniqueness of right adjoints, and the
existing integral affine-space and closed-immersion declarations. The proposition proof
eliminates compactification_over_base directly to obtain its compactification witnesses.
No definition selects arbitrary data from an unproved mere-existence statement, and the
proof does not call the choice-based compactificationOverField definition.

## Proved and sorry left

Closed the one original hole:
AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport.IntegralRestriction.integralRestrictionGlue.

Also proved all three new public component theorems in that namespace:

- bounded_finiteOpenDescent (lem-int-restriction-bounded-descent): finite cohomological bounds
  and open-restriction conservativity, including the empty cover.
- cohomology_finiteOpenDescent (lem-int-restriction-cohomology-descent): an explicit
  disjoint-first-open stratification using fibre products, Cartesian scalar-model pullback,
  and the derived cohomology comparison, including the empty cover.
- integralRestriction_chartCover (lem-int-restriction-chart-cover): finite affine charts,
  integral composition and open adjunctions, followed by affine-space and closed preservation.

Every private helper is proved. Holes added: zero. Holes left in all four delivered modules:
zero. Existing imported declarations may still depend on sorry, as allowed for stage 3.
Validation against the current project: lcompile.py --all compiled all four modules cleanly
in import order, with every file below its 60-second limit. All five existing public
signatures are textually unchanged, and every delivered Lean line satisfies the 100-character limit.

## No longer needed

Removed from the parent the proof imports ProEtaleWeaklyEtaleLocalization,
ProEtaleIntegralCoefficientLimit, LocalizedModuleExactForSystems,
ProEtaleBoundedConstructible, Mathlib.Topology.Constructible, RestrictionLocal,
LocalizingClosureCtfEqualsBc, IntegralTensorInverseImage,
CoefficientBoundedConstructibleProEtale, CondensedConstantConstructibility,
MateOpenRestriction, IntegralLocalizingCompactSupport, IntegralRestrictionClosed,
IntegralRestrictionLine and the source-library Derived.BoundedConstructible module.
These names refer to the corresponding imports of the original item module.
RestrictionLocal, MateOpenRestriction, IntegralRestrictionClosed and IntegralRestrictionLine
are used by the chart component; IntegralLocalizingCompactSupport is publicly imported by
the descent components and is still used. These modules are not claimed to be globally pruned.

The actual proofs need no direct use of the node statements
lem-weil-proetale-weakly-etale-localization,
det-prop-sfb-qlbar-colimit-x-integral-limit,
lem-pur-site-restriction-module-adjunction-exact,
sk-def-sfb-bounded-constructible, sk-def-sfb-dc-setting,
det-def-localizing-closure-ctf-equals-bc or sk-lem-int-tensor.
Canonical source-library Cartesian pullback/cohomology and conservativity APIs replace
the proposed site-limit route. Integral compact-support constructible_pull supplies the
strong constant-model preservation needed here. Withdrawn the parent's old tool_uses;
no module or unit step is withdrawn, and no global import-closure pruning is claimed.
The resumed chart proof also avoids
Sheaf.SixFunctors.CompactificationOverField and def-sfb-compactification-over-field,
using the existing compactification_over_base existence theorem only inside a proof.

## Where the brief, the DAG or earlier work was wrong

restrictionLocal requires rational coefficients for its exceptional-functor clauses. Its
coefficient-independent geometric cover clause can nevertheless be extracted at E and used
for the integral argument. The integral comparison is constructed separately in Lean.
IntegralTensorInverseImage states the weaker upstream constructibility predicate, so its
statement is not substituted for constant-model constructibility. The existing integral
compact-support Coherence.constructible_pull provides the exact needed predicate.

All three component statements are proved. All compiles use lcompile.py. No shared source
or launcher script was edited. No statement or definition repair, change record or forced
adaptation is needed. On resumption, replaced the earlier chart proof calls to
compactificationOverField: its definition chooses from an unproved mere-existence theorem.
Direct existential elimination in this proposition avoids introducing or exposing such data.

## New nodes

lem-int-restriction-bounded-descent: proved boundedness on finite open covers from generic
source-library conservativity and the exact-derived-functor APIs.

lem-int-restriction-cohomology-descent: proved constant-model cohomology descent on
Noetherian schemes by explicit disjoint-first-open fibre products and scalar-model pullback.

lem-int-restriction-chart-cover: proved local integral exceptional constructibility using
finite affine charts, actual compactifications, integral composition and Brown uniqueness,
then the existing affine-space and closed-immersion theorems. Global descent and restriction
of the adjunction remain in the parent, whose proof is complete.

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
