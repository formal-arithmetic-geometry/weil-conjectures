## What changed

Restored the complete four-module G1 packet preserved in
`coord/repair-notes/Sheaf.Paper.IntegralOperationsWellDefined.json`, rather than
replacing the rolled-back work by empty modules. The main theorem is proved from
finite reduction, exact finite pullback, independent-universe change of rings,
strict Roos invariance and localization by functorial flat resolutions. The three
restored coefficient helpers are proved in their own modules. The existing public
signatures, definition bodies, instances and ten public imports are preserved.

To avoid repeated expansion of completed coefficient sheaves during elaboration,
the Roos quasi-isomorphism argument is first proved for a generic abelian
category with exact countable products, then specialized to the coefficient
category. The derived-limit triangle is treated by the same generic approach.
Both helpers are private in the item module. The good-complex localization is
also proved generically for a ringed site before specialization. Private abstract
lemmas convert preservation of quasi-isomorphisms to acyclicity and apply this
to the core K-flat predicate. Explicit coefficient parameters prevent unnecessary
instance searches. File-local opacity
keeps the constant sheaves, monoidal structures and operation functors from
expanding during unrelated type comparisons; the final Roos comparison unfolds
only its defining functor compositions. Local caches share the flat-subcategory
coproduct and complex tensor instances. The derived-limit transport supplies
the ambient category and tower explicitly, with separately typed representative
isomorphisms, to avoid inferring them through coefficient limits. A file-local
priority for the existing `integralTowerHasDerivedCategory` instance makes proof
search use the exact completed-module presentation first; no exported instance
priority changes.

The reported global-build failure was missing `HasDerivedCategory A` in
`finiteTensor_quasiIso`. The finite tensor proof now uses the K-flat mapping-cone
argument directly, with no finite derived-category comparison or local derived
category instance. The private argument is adapted from the proof of the existing
site tensor descent theorem. Local elaboration commands and proof-only
imports are documented in `coord/changes/integral-operations-proof-commands.md`.
The DAG proof and proof dependencies follow the restored proof route. The existing
proved `integralOperationsDerivedCountableProducts` now uses the countable-product
core directly, preserving its statement while avoiding the unused general
derived-limit existence theorem.

## Proved and sorry left

Closed: `WeilConjectures.integralOperationsWellDefined`, one of the item's three
original holes. Added holes: none. Split-off holes: none.

Remaining original holes, both attached to
`lem-pur-integral-operations-well-defined`:

- `WeilConjectures.integralOperationsPullbackTransition_existsUnique`.
- `WeilConjectures.integralOperationsTensorTransition_existsUnique`.

The three restored public helper theorems are fully proved:

- `SheafOfModules.exists_changeOfRings_tensorCancellation_independentCoefficients`.
- `SheafOfModules.changeOfRings_isKFlat_of_flat_terms_independentCoefficients`.
- `AlgebraicGeometry.Scheme.coefficientProEtaleModulePullback_exact`.

The three helper modules compile without holes. The final packet is checked by
`lcompile.py --all` and `deliver3.py` in this session; historical compilation
claims from the earlier G1/R9 packets are not used as validation. The current
shared baseline has three holes, including the top-level theorem, after rollback.

K1 removes eight redundant redeclarations of the coefficient variables in private
proof sections and gives the existing `Algebra.toModule` instance file-local
priority 3000 in the proof part. This avoids repeated coefficient typeclass search.
The final main module compiled without warnings in 52.3 seconds. No public
signature, construction body, instance body or public import changes.

## No longer needed

The main proof removes these direct proof-only imports:

- `Sheaf.Algebra.Homology.ChangeOfRingsKFlatQuasiIso`.
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescent`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.
- `Mathlib.CategoryTheory.Localization.Predicate`.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`.
- `Mathlib.CategoryTheory.Adjunction.Additive`.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence`
  (both duplicate direct imports).

The recovered packet's direct import of
`Sheaf.CategoryTheory.Triangulated.DerivedLimitExistence` is also removed: that
module is absent from the current source and this proof constructs the required
Roos triangle directly. The obsolete top-level tool approvals
`prop-weil-pbc-proetale-constant-exact`, `lem-weil-derived-limit-existence` and
`lem-weil-pbc-site-derived-tensor-descent` are
removed from the item's node. Their statements are not used by this proof.

The old change-of-rings interface ties the site and coefficient universes
together; the new independent-universe results fit the specified completed
coefficients. Finite tensor invariance now follows directly from the K-flat
mapping-cone argument and its signed flip, so neither site tensor descent
interface is needed. The older constant-pullback exactness interface does not
state exactness of the specified coefficient-sized pullback functor. The new
exactness theorem proves precisely that result.

The private finite-reduction helper retains only K-flatness, the consequence used
by the mapping-cone argument; it does not repeat the unused flat-term transport.

Functorial flat resolutions give the good-complex localization directly, so this
proof does not require the planned operation-specific homotopy and roof
calculations. Strict Roos invariance and the product comparison establish the
needed derived-limit claim directly. These are proof-plan simplifications, not
withdrawals of unit statements or upstream declarations. Some removed direct
imports remain transitive dependencies. No module is withdrawn and no global
pruning count is claimed.

## Where the brief, the DAG or earlier work was wrong

The repair note records that the earlier local packet passed its own check but
the global build failed three times to find `HasDerivedCategory A`. The repaired proof eliminates that finite derived-category
comparison by using K-flat cones directly. The previous packet's compile claims
and review metadata are not reused as evidence for this delivery. R9 was later
returned by blanket batch triage after unrelated `bad import` failures; its return
records no type error in this proof packet. K1 restores that repaired packet and
checks it against the current shared baseline.

The preserved public theorem docstring outlines the original plan. Its older
references to site tensor descent and general tower-limit existence are replaced
in the actual proof; the updated node and dependency list describe the route used.

The original DAG plan used coefficient interfaces with insufficient universe
generality for this item. The restored helpers retain the exact coefficient
universe and the specified pullback and scalar-extension constructions. The
unit route is unchanged. The two transition-map existence/uniqueness holes remain explicit.

## New nodes

`lem-pur-change-of-rings-tensor-cancellation-independent` records natural tensor
cancellation for independent site and coefficient universes. Its sectionwise
balanced equivalence descends through monoidal sheafification; no flatness
assumption is needed. Fully proved, no hole.

`lem-pur-kflat-change-of-rings-independent` records preservation of K-flatness and
flat terms by the specified scalar extension. Exact conservative restriction,
natural cancellation and the total-complex comparison prove it. Fully proved,
no hole.

`lem-pur-coefficient-pullback-exact` records exactness of the specified
constant-coefficient pro-etale module pullback. Constant-sheaf adjunctions give
the normalized inverse-image ring comparison; exact abelian inverse image and
module equivalences give the result. Fully proved, no hole.

All three are recovered from the rolled-back G1 packet, with the delivery metadata
recorded for K1 because the current baseline contains none of them. The change record is
`coord/changes/integral-operations-proof-commands.md`.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
