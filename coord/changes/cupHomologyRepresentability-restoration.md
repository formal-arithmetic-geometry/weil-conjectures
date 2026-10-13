# CupHomologyRepresentability

## Reason

Repair the stale-base return. The current sheaf-dag tree no longer contains
Sheaf.Paper.ModuleCupHomologyRepresentability or its node after withdrawal of the
N4 ModuleCupEqualDerivedMapsClass delivery. Restore only the assigned interface
from the saved rollback patch and reapply the canonical-evaluation proof.
The original signatures, visibility and all four public imports are preserved.
The parent node is restored with M1 ownership and without obsolete review stamps.

## Old

The module is absent from the current delivery base. The withdrawn original
interface, whose signatures are preserved, was:

```lean
abbrev cupSingleModule (k : Type u) [CommRing k] (n : ℤ) :=
  (HomologicalComplex.single (ModuleCat.{u} k) (ComplexShape.up ℤ) n).obj
    (ModuleCat.of k k)

variable (k : Type u) [CommRing k] [HasDerivedCategory.{u} (ModuleCat.{u} k)]

/-- Homology represented by the shifted free module, with the cocycle normalization.
No representative or derived object is selected by this interface. -/
structure CupHomologyRepresentability where
  equiv : ∀ (A : DerivedCategory (ModuleCat.{u} k)) (n : ℤ),
    (DerivedCategory.Q.obj (cupSingleModule k n) ⟶ A) ≃ₗ[k]
      (DerivedCategory.homologyFunctor (ModuleCat.{u} k) n).obj A
  natural : ∀ (A B : DerivedCategory (ModuleCat.{u} k)) (n : ℤ)
    (f : DerivedCategory.Q.obj (cupSingleModule k n) ⟶ A) (g : A ⟶ B),
    equiv B n (f ≫ g) = (DerivedCategory.homologyFunctor (ModuleCat.{u} k) n).map g
      (equiv A n f)
  on_cycles : ∀ (K : CochainComplex (ModuleCat.{u} k) ℤ) (n : ℤ)
    (f : cupSingleModule k n ⟶ K) (z : K.cycles n),
    ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n (ModuleCat.of k k)).inv ≫
      f.f n) (1 : k) = K.iCycles n z →
    equiv (DerivedCategory.Q.obj K) n (DerivedCategory.Q.map f) =
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} k) n).app K).inv
        (K.homologyπ n z)

theorem exists_cupHomologyRepresentability : Nonempty (CupHomologyRepresentability k)
```

Its theorem proof was `by sorry`. Its public imports were DerivedCategory.Linear,
DerivedCategory.HomologySequence, Single, and ShortComplex.ModuleCat from Mathlib.

## New

Restore precisely the signatures above and the same public imports.
The theorem now constructs the equivalences from cupHomologyEvaluation and its
bijectivity, and proves naturality and the cocycle normalization by the existing
homology identities. Its added import
Sheaf.Paper.ModuleCupHomologyEvaluationBijective is a plain proof import.
The only remaining hole is the bijectivity of that concrete map, in its own module.
There is no change to any existing target statement or to any definition it uses.

## Users

The current source tree has no importer of the absent module. No other existing
module is changed or adapted. Future restoration of the withdrawn consumers can
use the identical interface. The three supporting modules do not import this item,
so they introduce no cycle.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ModuleCupHomologyRepresentability | M1 | Restore the original interface and reduce its original proof hole. |

No current target uses this absent interface, so restoration does not alter a
current target's meaning or reopen a target-statement review.

## Status

landed 20261013T224514-L-1473237 2026-10-13 (merge of deliver/M1/Sheaf.Paper.ModuleCupHomologyRepresentability)
