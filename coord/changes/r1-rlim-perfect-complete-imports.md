# Sheaf.RingTheory.RlimPerfectComplete proof support

## Reason

Prune an unused public import of the sheaf-level change-of-rings interface and
supply local notation, scoped elaboration options
for the proof. The module's existing public declarations, their signatures and the
bodies of its five definitions are unchanged. The scoped transparency options only
control elaboration of the new proofs. No target statement or definition used by a
target has changed meaning.

## Old

The relevant original import and open command were:

```lean
public import Sheaf.Algebra.Homology.DerivedChangeOfRings
```

```lean
open CategoryTheory CategoryTheory.Limits
```

The three old proof-only imports of KFlatTelescopeClosure,
PerfectRingComplexGeneral and DerivedChangeOfRingsIndependentCoefficients are also
removed; they were never re-exported.

## New

The unused public import above is removed. The proof uses these additional
proof-only imports:

```lean
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Sheaf.Algebra.Homology.KFlatScalarExtensionDerivedIso
import Sheaf.Algebra.Homology.BoundedFlatKFlat
import Sheaf.RingTheory.FiniteConeFreeModel
import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.FiniteFree
```

The local proof environment contains:

```lean
open CategoryTheory CategoryTheory.Limits MonoidalCategory

open scoped TensorProduct
```

Several private proofs and the main proof use scoped
`backward.isDefEq.respectTransparency` options. They export no instances or new
public declarations. The adic restriction comparison is checked in the expected interface supplied by
the reconstruction theorem. A private record and a proved generic projection helper
provide a small interface to its existing witness data. All proof parts remain in
the item's single module under the existing time limit; the reconstruction module
held by B4 is unchanged.

## Users

`python3 tools/downstream.py Sheaf.RingTheory.RlimPerfectComplete` reported zero
modules downstream. There is no consumer to adapt. The preserved public signatures
continue to express exactly the original assertions.

| module | group holding it | effect |
| --- | --- | --- |
| none | none | no downstream modules |

## Status

landed 20261018T071216-L-1675709 2026-10-18 (merge of deliver/R1/Sheaf.RingTheory.RlimPerfectComplete)
