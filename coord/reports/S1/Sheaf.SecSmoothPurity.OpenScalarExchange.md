## What changed

Proved `AlgebraicGeometry.ProEtale.openScalarExchange` with its original signature.
The proof compares inverses under the open adjunction, proves the scalar/open unit
normalization by uniqueness of left adjoints, and combines the specified base-change
unit equations with tensor-square coherence and naturality.

The new `OpenBaseChangeDerivedUnit` module proves exact descent of the actual inverse
open-unit equation, using private fully proved localization calculations. The new
`OrdinaryRestrictionPullbackSquare` module proves ordinary restriction coherence from
the section-normalized direct-image compositor and the adjunction mate laws. The new
`TensorPullbackSquare` module descends this ordinary cube through exact functors, then
uses the four scalar adjunctions to prove the tensor cube. These helpers have no sorry.

Repaired the unclaimed module `FiniteOpenBaseChangeNormalized`: `moduleSquareG` is fixed
by a proved unique specification requiring equality to its original explicit composite.
`moduleSquareG_eq` exposes precisely that equation. Passing this equation as an explicit
argument to generic pasting avoids expanding the sheaf-module composite in the final
ordinary coherence proof. All existing signatures and visibility are retained. No data
is chosen from an unproved existence theorem. Targets using the changed definition
require statement-meaning review again; its proved equality supplies the equivalence.
Change record:
`coord/changes/S1-constant-square-compositor-specification.md`.

Validation: on 2026-10-20, `lcompile.py --all` compiled all five current modules
cleanly. The resumed `deliver3.py --no-push` passed compilation, axiom checking and
server preflight (dry-run commit `21f6de9c56`); the packet is classified CODEX for
independent review. The consumer table was then refreshed for four new importers.
The change record consumer table was refreshed against all 755 current downstream
modules; the repaired module remains unclaimed. Earlier successful single-file
compiles took 14.5, 10.7 and 9.3 seconds for ordinary coherence, tensor coherence and the
item, and 3.4 and 7.6 seconds for the repaired base-change module and derived open-unit
helper. Consumer checks compiled `ExceptionalBaseChangeCartesianOpenInjectiveAcyclic`
and `OpenBaseChangeSiteTransport`. `FiniteOpenExchangeScalars` timed out both with
the repair and against its original baseline; `ProEtaleLocalizationFilteredSection`
also timed out. These checks establish no repair-induced consumer failure; complete
consumer validation remains the independent review and global build. No consumer
source is changed in this packet.

## Proved and sorry left

Closed the item's original hole:
`AlgebraicGeometry.ProEtale.openScalarExchange` (`lem-fix-open-scalar-exchange`):
1 of 1 original holes; zero new holes and zero postponed splits.

Also proved the new theorems `AlgebraicGeometry.ProEtale.openBaseChangeDerivedUnit`,
`AlgebraicGeometry.ProEtale.ordinaryRestrictionPullbackSquare`,
`AlgebraicGeometry.ProEtale.tensorPullbackSquare`,
`AlgebraicGeometry.ProEtale.StrictTower.moduleSquareG_existsUnique`, and
`AlgebraicGeometry.ProEtale.StrictTower.moduleSquareG_eq`, and all their private helpers.

The repaired pre-existing `FiniteOpenBaseChangeNormalized` module retains its two
original holes unchanged:
`AlgebraicGeometry.ProEtale.StrictTower.singleBetaInvApp_naturality` and
`AlgebraicGeometry.ProEtale.StrictTower.singleBetaInv_isIso`, both attached to
`lem-cbc-proetale-extension-zero-base-change`. They are existing dependencies of the
assigned statement, not new holes. The delivery therefore has two actual remaining
holes across all five files, zero in the item and zero in the three new helper modules.
The net hole change is minus one.

## No longer needed

Removed proof imports `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`,
`Sheaf.AlgebraicGeometry.FiniteOpenExchangeScalars`,
`Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange`,
`Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`, and
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses` from the item module.
The actual adjunctions and operations used in the proof are available through its
statement imports. In particular `lem-cbc-finite-open-exchange-scalars` and
`FiniteOpenExchangeScalars` are unnecessary for the inverse unit equation, which follows
from `singleBetaInvApp` and exact localization. The categorical tensor-square proof also
needs no K-flat representative computation or generic tensor/pullback theorem from
`RingedTopoiCanonicalTensorPullbackOfUniverses`. Removed the obsolete top-level
`lem-cbc-finite-open-exchange-scalars` tool approval from the parent node copy.
No unit realization is bypassed.

Removed redundant public imports `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap` and
`Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison` from the item: the same
statement declarations remain available through the other public imports. These
removals do not claim those modules leave the targets' complete import closure.

Removed the unused private `comparison_congr` experiment from the ordinary helper.
No landed module or DAG node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The generic `mapDerivedCategoryAdjunction` mate theorem concerns a different derived
adjunction. The private exact-localization calculation instead uses the actual
complex-localized open adjunction of `ProjectionFormulaCompactified`.

The earlier report described the tensor-square theorem as still postponed. It is now
proved by ordinary restriction coherence, exact derived composition coherence, and
scalar-adjunction mates. The direct-image compositor is specified by its section
normalization, not a definitional identity. The square compositor previously expanded
through a large explicit composite: its equality-specified API and a generic pasting
lemma with explicit equality arguments resolve that conversion cost. The ordinary
coherence module compiled in 16.8 and 17.8 seconds before the final cosmetic cleanup.

Several compile requests received no server response within the tool's retry window;
these were retried without changing compiler limits or tool scripts. The two
`whiskerLeft_id`/`whiskerRight_id` variants concern `NatTrans.id`; the composition
calculation requires the primed variants for categorical `𝟙`.

## New nodes

`lem-fix-open-base-change-derived-unit`, module
`Sheaf.SecSmoothPurity.OpenBaseChangeDerivedUnit`: proved localization of the specified
inverse open-unit equation.

`lem-fix-ordinary-restriction-pullback-square`, module
`Sheaf.SecSmoothPurity.OrdinaryRestrictionPullbackSquare`: proved compatibility of
ordinary restriction with the specified inverse-image square. Its source is Stacks
03D7/03D8; empty schemes, zero rings, identity maps and nonflat coefficient maps require
no exception because the proof uses only restriction, sections and adjunctions.

`lem-fix-tensor-pullback-square`, module `Sheaf.SecSmoothPurity.TensorPullbackSquare`:
proved tensor cube from that ordinary coherence and exact localization. No open
extension or base-change exchange occurs in its statement.

`lem-fix-constant-square-compositor-specification`, attached to the repaired existing
module `Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized`: proved unique equality
specification and the equation fixing the same original compositor. Its source is
Stacks 03D8. The change record above lists all downstream consumers and current holders.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
