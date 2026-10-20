# AlgebraicGeometry.artinSchreier_trace_cover_map

## Reason

The proof uses the existing affine-space Artin–Schreier finite/étale theorems and the
pullback coordinate universal property. The former relative-Spec and additive-character
imports are unnecessary. Removing unused public imports changes the exported import
closure, so this record documents the sole consumer check. All existing public definitions,
structure fields, signatures, and mathematical statements remain identical.

## Old

```lean
public import WeilConjectures.AlgebraicGeometry.AffineSpace.ArtinSchreier
public import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.FieldTheory.Separable
import Sheaf.AlgebraicGeometry.RelativeSpecBaseChange
import Sheaf.AlgebraicGeometry.CoherentFiniteType
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.Mathlib.Algebra.CharP.Lemmas
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.AffineSpace.ArtinSchreier
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.RingTheory.AdjoinRoot
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.GroupTheory.Index
import WeilConjectures.Mathlib.Algebra.CharP.Lemmas
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ArtinSchreierTraceCoverMap | V5 | Sole original theorem proved; private coordinate API seals definitions locally during proofs. |
| Sheaf.AlgebraicGeometry.ArtinSchreierPrimeCharacterComparison | F8 | Direct importer checked unchanged against the delivered module; no adaptation. |

The downstream query found only the prime-character comparison module. No public definition
or target meaning changes, and no target-statement review is reopened by this import pruning.

## Status

landed 20261020T131212-L-1259071 2026-10-20 (merge of deliver/V5/Sheaf.AlgebraicGeometry.ArtinSchreierTraceCoverMap)
