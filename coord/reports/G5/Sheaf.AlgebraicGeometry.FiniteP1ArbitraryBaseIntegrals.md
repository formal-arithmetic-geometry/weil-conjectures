## What changed

Replaced the hole in `exists_arbitraryBaseFiniteP1Integrals` by a reduction to hyperplane
Kummer naturality and a direct diagonal Chern-component calculation. The actual Lean glue
constructs the splitting records, obtains trace naturality by inverting the decomposition
square, and computes both integrals using the two biproduct injection/projection equations.
Original public imports and all mathematical hypotheses and conclusions are retained.
The helper theorem now names its expanded diagonal clause as `finiteP1DiagonalProperty`;
unfolding that definition gives the original clause. This is an interface refactor of
the assigned helper, not a change to any fixed declaration in `Challenge.lean`.
The ordered source and derived direct-image target now have explicit object definitions,
`ordinaryFiniteP1SplittingSource` and `ordinaryFiniteP1SplittingTarget`. They are the
same biproduct and direct-image objects by delta reduction, and contain no admitted data.
The structure and trace name these objects; the new public import and updated Lean attachment
record this definition interface. A private constructor takes the isomorphism proof explicitly
and has a proved morphism equation, so the main proof uses that API. An explicit category
argument on IsIso supplies the same inferred derived category. Proofs witnessing invertibility
of N on the projective schemes now use the proved `finiteP1_unitOnPullback` API,
whose proof transports `IsUnit.map` through `map_natCast`. This avoids repeating
expensive global-sections normalization in the structure and the base-change predicates.
The trace projection and IsIso category have explicit arguments to avoid inferring
objects through chosen categorical constructions. Reducibility settings used for elaboration are local; no existing global definition attribute
is changed.

The canonical composite of alpha with the projected supported class is named
`ordinaryFiniteP1DiagonalSupportedMap`, with its exact original direct-image target
`ordinaryFiniteP1DiagonalTarget`. These actual definitions share the repeated map
construction across the component formula and diagonal predicate. The body is precisely
the original two-factor composite; it has no existence choice or admitted property.

The base-change predicate shares its functors and composite exchange arrow using
local lets; unfolding them gives exactly the original equations. The diagonal trace
now composes `ordinaryFiniteP1DiagonalChartMap` with the splitting trace. Unfolding
the chart map gives exactly the original four-factor construction, and the comparison
used in the integral calculation is reflexive. The structure
field `decomposition_hom` names the explicit `ordinaryFiniteP1SplittingMap`; unfolding
that map gives the original `biprod.desc` law. The definition
changes and absence of external consumers are recorded in
`coord/changes/finite-p1-diagonal-trace-api.md`.

Added `FiniteP1UnitOnPullback`, proving the elementary global-functions unit map.
Added `FiniteP1NoetherianBase`, proving the universal Noetherian base using the localization
of the universe-lifted integers and the global-sections/spectrum adjunction. Added
`FiniteP1KummerSplitting`, proving invertibility of the natural two-component map by descent
from that base. Its private lemmas prove invertibility of the exact-derived exchange from
the published cyclic-coefficient theorem and coefficient restriction, transporting
adjunction mates as in the proved
`UnboundedCoefficientForgetfulAux`; its source comparison is an additive biproduct isomorphism.
Added `FiniteP1DiagonalAlpha`, proving invertibility of the canonical pasted constant unit
from the fact that either projection composed with the diagonal is identity.

The remaining geometric results have their own modules: `FiniteP1KummerNaturality` and
`FiniteP1DiagonalKummerComponentFormula`. The latter computes the supported class before
any trace is chosen: it is the relative hyperplane adjunct plus a base class followed by the twisted
unit. Keeping the base term is essential. The now-proved `FiniteP1DiagonalChernComponents` obtains Cartier invertibility from
the same short relative-Cartier argument as `diagonalImmersion_cartier` and the boundary from
`ordinary_supported_kummer_uniqueBoundary`, then applies that formula.
The three explicit invertibility witnesses on the
projective schemes are consequences of the original base witness, passed explicitly to
avoid repeated elaboration of the same global-sections maps.

Validation: all eight delivered modules compile through `lcompile.py` under the default
60-second file limit. The final assigned module compiles cleanly in 36.4 seconds; the
seven supporting modules were checked together in import order. No diagnostic options
remain. Static checks found exactly the two named theorem holes below, no admitted data,
no forbidden declarations, no lines over 100 characters, and valid DAG dependency unions.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Etale.exists_arbitraryBaseFiniteP1Integrals`
by decomposition, not by a complete proof of its geometric dependencies. The assigned
module has zero remaining holes. Added two holes, strictly below the original statement:

- `AlgebraicGeometry.Etale.exists_ordinaryFiniteP1KummerNaturality`
  (`lem-sp-finite-p1-kummer-naturality`): canonical hyperplane Chern realization and its
  component square; no splitting invertibility, trace, Cartier diagonal, or integral.
- `AlgebraicGeometry.Etale.ordinaryFiniteP1_diagonal_kummer_component_formula`
  (`lem-sp-finite-p1-diagonal-kummer-component-formula`): the two Chern components of a
  specified supported diagonal boundary; no splitting, trace, or integral identity.

Proved the new declarations `AlgebraicGeometry.finiteP1_unitOnPullback`,
`AlgebraicGeometry.finiteP1_exists_noetherianBase`,
`AlgebraicGeometry.Etale.exists_ordinaryFiniteP1SplittingMap`, and
`AlgebraicGeometry.Etale.isIso_projectiveLineDiagonalAlpha`, and
`AlgebraicGeometry.Etale.ordinaryFiniteP1_diagonal_chern_components`, with their supporting private
lemmas. The three new public object definitions, three new public morphism definitions and
the diagonal predicate contain no admitted data.
This packet closes one upper hole and adds two lower holes: a decomposition with packet
net -1. The delivery ledger determines the impact in the targets' import closure. Existing
imported holes are not claimed as closed.

Edge cases checked in the statements and constructions: the zero coefficient ring, N=1,
the empty scheme, and identity changes of base introduce no extra assumption. The universal
base lemma also allows N=0; localization at zero and the ring-map adjunction cover that case.

## No longer needed

Removed these direct private proof imports from the assigned module:

- `Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts`
- `Mathlib.CategoryTheory.Adjunction.Mates`
- `Mathlib.AlgebraicGeometry.Pullbacks`
- `WeilConjectures.AlgebraicGeometry.EffectiveCartier`
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`
- `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`
- `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction`
- `Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer`
- `Sheaf.AlgebraicGeometry.ProjectiveLineTrace`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`

The original node's proof now directly depends on the new splitting, diagonal component,
and alpha nodes. The old Noetherian-diagonal-integral/pullback argument is replaced by the
explicit component computation. Thus its separate proof uses of `def-amb-p1-trace`,
`lem-amb-p1-diagonal-integrals`, `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`,
and `lem-weil-pbc-mate-pasting` are unnecessary at this node. Definitions from the first
three remain in statement/import dependencies; the generic inverse-image and mate tools
are still used below, where indicated in the new nodes. The Cartier, standard-chart,
supported-Kummer, finite-twist, and proper-exchange dependencies are retained in the lower
results. No library module or source declaration is withdrawn, and no global pruning is
claimed merely from the removed direct imports. The obsolete direct tool-use approval
`lem-kun-proper-base-change-torsion-ring` is removed; the proof uses the public cyclic
exchange theorem and coefficient restriction instead. The unit and its route are retained.

## Where the brief, the DAG or earlier work was wrong

The initial search records used LeanFinder, Loogle and grep, but preflight groups
LeanFinder and Loogle as one kind. Added a separate LeanSearch query for each new
node, with all returned declaration names and verdicts; retained the original searches.

The existing node's `proof_origin` still narrated a historical withdrawal, although its
current Lean attachment has been restored. This delivery retains that attachment and
updates only the proof route and its dependency union.

The `ProperUnboundedBaseChange` module currently exposes its local torsion theorem only
privately. The splitting proof assembles its needed instance from the existing public
`isIso_derivedBaseChangeMap_of_isProper_modN` and
`isIso_derivedBaseChangeMap_of_isIso_modN`, using the given N and NA=0. This avoids importing
the larger adopted-source `BaseChangeTheorems.Proper` module; no adopted source is edited.
The resulting exchange uses the ordinary derived adjunction; the displayed finite-P1
exchange uses exact derived inverse image, so the proof explicitly transports invertibility
between those mates.

The diagonal Chern adjunct is not just the relative hyperplane adjunct: O(diagonal) is
p1*O(1) tensor p2*O(1). Its base contribution is recorded as beta; the trace kills it.
This prevents a false component identity that would discard the first summand.

## New nodes

`lem-sp-finite-p1-unit-on-pullback` is the proved natural-number unit transport API,
in `FiniteP1UnitOnPullback`.

`lem-sp-finite-p1-noetherian-base` is the proved localization/global-sections construction,
in `FiniteP1NoetherianBase`.

`lem-sp-finite-p1-kummer-naturality` states the geometric hyperplane realization and
component naturality, in `FiniteP1KummerNaturality`, together with its actual source, target, and two-component
map definitions; this is one remaining hole.

`lem-sp-finite-p1-kummer-splitting` proves invertibility from that naturality and the
Noetherian base, in `FiniteP1KummerSplitting`.

`lem-sp-finite-p1-diagonal-alpha` proves the pasted constant-unit isomorphism over any
base and any commutative coefficient ring, in `FiniteP1DiagonalAlpha`.

`lem-sp-finite-p1-diagonal-chern-components` proves existence of the Cartier boundary
and reduces its component calculation to the following formula, in
`FiniteP1DiagonalChernComponents`.

`lem-sp-finite-p1-diagonal-kummer-component-formula` states the component formula of
a specified supported diagonal Kummer boundary, in
`FiniteP1DiagonalKummerComponentFormula`; this is the other remaining hole.

The equivalent object interfaces and invertibility witnesses are recorded in
`coord/changes/finite-p1-diagonal-trace-api.md`. The assigned helper statement names a definitionally identical diagonal predicate;
no fixed Challenge statement or global reducibility attribute is changed. There are
no forced consumer adaptations.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
