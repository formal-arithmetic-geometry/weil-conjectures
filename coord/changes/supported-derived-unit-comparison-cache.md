# AlgebraicGeometry.Etale.supportedDerivedUnit

## Reason

Specializing the full unbounded derived-unit/single comparison repeatedly exceeded the
60-second file limit. A statement-only probe identified kernel conversion between different
proof constants stored in the abelian and derived-category instances. Selecting the instance
proofs captured by DerivedCategoryModule reduced that probe to 42 ms of kernel checking.
The full derived-unit specialization still repeats the large structural instance application.
Name that exact composite generically once and use its proved single-comparison API.

This is a cache of the original construction, not a new choice of adjunction or normalization.
The generic body is the same full derivedAdjunction unit, followed by the right-derived image
of its existing left-single comparison and the same constant-sheaf comparison. Unfolding the
names recovers the old composite definitionally. The existing supportedDerivedUnit signature
and attributes are unchanged. No data is chosen from an existence theorem.

The local instance attributes select the existing proof constants already captured in the
source DerivedCategoryModule abbreviation. Their scope stays local to the system module. These auxiliary names are exposed by the source
but have no stable named API;
refactoring that source may require updating these local selections. No source file is edited.
A public import of the new definition is needed by this definition body. Every other declaration,
public import and explicit body in the system module is unchanged. The generic cache module also
adds the proved derivedSingleUnit_eq expansion API, whose proof unfolds that cache
and closes by reflexivity. The system module has B3's exact restored construction.

## Old

```lean
@[irreducible]
def supportedDerivedUnit (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) :
    ordinaryFiniteUnit A T ⟶ (ordinaryFinitePushforward A i).obj (ordinaryFiniteUnit A D) :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).unit.app
      (ordinaryFiniteUnit A T) ≫
    (ordinaryFinitePushforward A i).map (ordinaryFiniteUnitPullback A i).hom
```

## New

```lean
@[irreducible]
def supportedDerivedUnit (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) :
    ordinaryFiniteUnit A T ⟶ (ordinaryFinitePushforward A i).obj (ordinaryFiniteUnit A D) :=
  Adjunction.derivedSingleUnit (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i)
    (ordinaryFiniteConstant A T) (ordinaryFiniteConstant A D)
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) i).hom.app (ModuleCat.of A A))
```

## Users

The definition module is unclaimed. The direct repository users were checked with
`tools/downstream.py --uses supportedDerivedUnit`; the new comparison proof module is added below.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.DerivedSingleUnit | unclaimed (B3 landing) | Original generic cache retained; add only its proved expansion-equation API. |
| Sheaf.CategoryTheory.DerivedSingleUnitExact | unclaimed (B3 landing) | Existing direct user of the generic cache; current source is unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalData | unclaimed | Current direct user of supportedDerivedUnit; signature and canonical derived-unit formula preserved. |
| Sheaf.AlgebraicGeometry.OrdinarySupportedKummerSystem | unclaimed | Cache and one public import; signature and mathematical data preserved. |
| Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer | C3 (current), B3 (restored) | Existing unit realization is proved using the cached comparison API. |
| Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals | A7 | Original source checked against the repair; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedDerivedUnitForget | unclaimed (B3 restoration) | Proves the exact-unit and integral-generator equations. |

| Sheaf.AlgebraicGeometry.FiniteP1DiagonalAlpha | unclaimed | Use a private generic pasting lemma for the cache, proved by derivedSingleUnit_eq and the original pasted-unit argument. |
| Sheaf.AlgebraicGeometry.OrdinarySupportedChernNormalization | unclaimed (A7 restoration) | Compose proved unit-forgetting and Chern identities. |

The definition and all targets using it require the usual independent definition review.

## Status

landed 20261021T134548-L-1367600 2026-10-21 (merge of deliver/T3/Sheaf.AlgebraicGeometry.GeoCartierCycleClass)

T3 restoration, 2026-10-21: the return requires keeping B3's proved ordinary module.
The shared branch's batch recovery removed this matching cache and its support
modules during the repair. Restore B3's reviewed cf48da8d1bd implementation and
mathematical node fields; the generic module additionally gains its proved expansion API
and node attachment;
its original meaning and proof remain unchanged. Reintroduction metadata names T3;
the restoration fields preserve B3's original provenance. The T3
interface change record lists the six additional checked consumers.
