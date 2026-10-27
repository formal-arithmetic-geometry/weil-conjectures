## What changed

Proved AlgebraicGeometry.ProEtale.finiteExceptionalDomain without changing its signature
or any of its definitions. The private restrictClass helper explicitly constructs the
full-subcategory Hom equivalences, their adjunction, its normalized unit and counit,
and every compactification comparison with Hom compatibility, identity and cocycle.

Reuse the adopted native preservation theorems
constructibleFiniteTor_rightDerivedLowerShriekOfCompactification (CompactifFiniteTor)
and constructibleFiniteTor_rightDerivedUpperShriek (UpperShriekFiniteness). A proved
private coefficient lemma establishes invertible exponent for the actual ULift quotient.
Adjunction.rightAdjointUniq transports preservation and boundedness to the exact supplied
ordinary-etale adjoint. No arbitrary pro-etale right adjoint is introduced.

In the unclaimed Sheaf.AlgebraicGeometry.FiniteComparisonClassAdjunction, add the proved
public nonempty_fixedComparisonClassAdjunction_of_boundedBelow wrapper around the
existing private buildFixedComparisonClassAdjunction. Every existing declaration and
import stays verbatim. The new wrapper is needed because the existing coefficient-specific
existence theorem uses E : Type (u+1) and chooses its etale adjoint, whereas the item uses
E : Type u, ULift of its quotient, and any specified etale adjunction.

Validation: both delivery modules compiled in import order through lcompile.py; the
final item compile passed in 19.8 seconds with no warnings. The wrapper's containing
module compiled in the combined check. No source-library file is changed.
The change record is coord/changes/D9-specified-comparison-class-construction.md.

## Proved and sorry left

Closed the one original hole:
AlgebraicGeometry.ProEtale.finiteExceptionalDomain
(node lem-sf-package-finite-exceptional-domain).

Added zero holes. Split off zero sorries. Both delivered modules have zero sorry tokens.
The public helper
AlgebraicGeometry.ProEtale.nonempty_fixedComparisonClassAdjunction_of_boundedBelow
(node lem-sf-specified-comparison-class-construction) is fully proved by the existing
constructor. The new native-preservation node records already proved source declarations;
it introduces no Lean declaration or hole.

## No longer needed

Removed private proof imports Sheaf.Paper.OpenExtensionFiniteTor,
Sheaf.Paper.ProEtaleFiniteCoefficientDirectImage, Sheaf.Paper.SfPreservationClass,
Sheaf.Paper.ProEtaleConstructibleOrigin, and
WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType.

The item's proof no longer directly needs def-weil-proper-morphism,
lem-sfb-finite-type-composition-base-change, lem-trf-open-ctf,
cor-sf-direct-image-ctf-proetale, thm-sf-preservation-class,
lem-sf-proetale-constructible-origin, or lem-kun-dimension-finite-type.
The already proved native preservation theorems replace the interval/chart constructions.
Native constructibleFiniteTor itself supplies plusEtaleOrigin/plus, so no separate
constructible-origin comparison is needed in this restriction proof. The supplied
compactification dimension bound and quasi-compactness of its open part are retained
in the unchanged theorem signature but not used by the stronger native APIs.
The original tool_uses entries lem-trf-open-ctf and lem-sf-proetale-constructible-origin
are removed from the item's node. The native preservation node still documents the
mathematics below the already proved source results; this delivery does not withdraw
any module or declare those results globally unnecessary.

No public import removed; no module withdrawn. The package unit's exceptional-adjunction
route through preservation and class-relative restriction is retained.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically valid but longer than the existing native source APIs.
Its class-data existence theorem cannot be applied literally at the item's coefficient
universe or to an arbitrary specified adjoint. Exposing the already proved general
constructor resolves both interface gaps without a coefficient transport theorem or any
statement change. The first compilation errors were explicit full-subcategory binder
inference issues; the final proof supplies the source hypotheses and typed arrows.

Edge cases: the finite coefficient lemma uses n >= 1 only for finiteness; empty source
or target schemes need no separate choice or dimension convention in the adopted APIs.
All comparisons are lifted from the exact retained class datum, and the right functor
keeps the specified adjoint, including its original adjunction maps.

## New nodes

lem-sf-specified-comparison-class-construction exposes the already proved normalized
class-data constructor for arbitrary finite coefficients and a specified etale adjunction
with the precise boundedness hypothesis. It is fully proved, contains no geometric
preservation conclusion, and supplies only the class-data portion of the argument.

lem-sf-native-finite-tor-preservation records the two already proved adopted native
finite-ring preservation declarations, in CompactifFiniteTor and UpperShriekFiniteness.
It introduces no new theorem or proof obligation. It documents the shorter proof route
and keeps the DAG aligned with the exact predicates and modules used by Lean.

Change record: coord/changes/D9-specified-comparison-class-construction.md.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
