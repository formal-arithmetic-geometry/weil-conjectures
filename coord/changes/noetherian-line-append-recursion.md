# AlgebraicGeometry.Etale.NoetherianSmoothDuality.lineAppend

## Reason

The retained parent module exceeds the 60-second compilation limit with its original
recursive equation definition. The inherited sandbox's explicit Nat.rec version compiled
in 22.3 seconds with profiling enabled. Write the same structural recursion directly to
avoid expensive recursive-definition elaboration. Profiling options are removed.
The module is unclaimed. This accompanies withdrawal of the unused arbitrary-base item.

## Old

```lean
def lineAppend (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (X : Scheme.{u}) (s : ℕ) : ∀ r : ℕ,
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj (line A N hA X s)).obj
        (line A N hA X r) ≅ line A N hA X (s + r)
  | 0 => ((derivedTensor (ModuleCat.{u + 1} A) X).obj (line A N hA X s)).mapIso
      (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) X) ≪≫
        derivedTensorRightUnitor (ModuleCat.{u + 1} A) X (line A N hA X s)
  | r + 1 =>
    (derivedTensorAssociator (ModuleCat.{u + 1} A) X (line A N hA X s)
      (line A N hA X r) ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧)).symm ≪≫
      ((derivedTensor (ModuleCat.{u + 1} A) X).mapIso (lineAppend A N hA X s r)).app _
```

## New

```lean
def lineAppend (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (X : Scheme.{u}) (s : ℕ) : ∀ r : ℕ,
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj (line A N hA X s)).obj
        (line A N hA X r) ≅ line A N hA X (s + r) :=
  Nat.rec
    (((derivedTensor (ModuleCat.{u + 1} A) X).obj (line A N hA X s)).mapIso
      (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) X) ≪≫
        derivedTensorRightUnitor (ModuleCat.{u + 1} A) X (line A N hA X s))
    (fun r ih ↦
      (derivedTensorAssociator (ModuleCat.{u + 1} A) X (line A N hA X s)
        (line A N hA X r) ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧)).symm ≪≫
        ((derivedTensor (ModuleCat.{u + 1} A) X).mapIso ih).app _)

```

The type and visibility are identical. The zero value is the same tensor-unit constraint;
the successor is the same associator followed by the tensor image of the induction value.
Nat.rec supplies exactly those recursive equations. No mathematical choice, hypothesis,
or normalization changes. No new proof hole or data extracted from a theorem is introduced.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.NoetherianPrimePowerSmoothDuality | unclaimed | Own definition rewritten; compositionSource still uses exactly the same tensor concatenation |
| Sheaf.AlgebraicGeometry.LogSmoothTraitPunctualPurity | unclaimed | Transitive importer; no source occurrence of lineAppend; interface and meaning preserved |
| Sheaf.AlgebraicGeometry.MonomialBoundaryPurityCriterion | unclaimed | Transitive importer; no source occurrence of lineAppend; interface and meaning preserved |
| Sheaf.AlgebraicGeometry.MonomialTraitPunctualPurity | unclaimed | Transitive importer; no source occurrence of lineAppend; interface and meaning preserved |
| Sheaf.AlgebraicGeometry.PrimeFieldPunctualPurity | unclaimed | Transitive importer; no source occurrence of lineAppend; interface and meaning preserved |
| Sheaf.AlgebraicGeometry.PunctualPurityTraitTest | unclaimed | Transitive importer; no source occurrence of lineAppend; interface and meaning preserved |
| Sheaf.AlgebraicGeometry.SmoothPunctualPurityAscent | unclaimed | Transitive importer; no source occurrence of lineAppend; interface and meaning preserved |

Users checked by tools/downstream.py with the fully qualified declaration name and a full
source search. The only external use of this definition's value is compositionSource in
the same module. No consumer adaptation or target-statement review is required.

## Status

landed 20261019T154013-L-3026593 2026-10-19 (merge of deliver/J1/Sheaf.AlgebraicGeometry.ArbitraryBaseP1Integrals)
