# CochainComplex.CyclePullback comparison module retirement

## Reason

Retire the duplicate `Sheaf.Algebra.Homology.CyclePullbackTowerComparison` in favour of
`WeilConjectures.Algebra.Homology.CyclePullbackTowerComparison`, as requested by the
retirement queue. All definitions and all retained theorem implementations match
upstream after stripping comments and whitespace. The only extra public declaration
is the unused existential first-projection wrapper `tower_comparison_first`.
Its conclusion follows from the upstream canonical comparison and its first-projection
equation; a scratch Lean example with the wrapper's exact statement and proof compiles.

The recorded consumer `Sheaf.Algebra.Homology.CyclePullbackCore` has already been
retired from the shared tree. The surviving upstream `CyclePullbackCore` already imports
the upstream comparison. A source scan and `tools/downstream.py` find zero direct or
transitive importers of the Sheaf copy. No consumer adaptation is required.

## Old

The Sheaf module defines `evaluatedPullbackIso`, `indexedPullback`, `canonicalComparison`,
`term_step_eq`, `tower_comparison_canonical_first`, `tower_comparison_second`,
`tower_comparison`, and the additional wrapper with this signature:

```lean
theorem tower_comparison_first {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    (F : B ⥤ CochainComplex A ℤ) (N : ℤ) (b : B) (i : ℤ) (hi : i ≤ N) :
    let d := (differential T π F N (i + 1)).app b
    let f := (F.obj b).d i (i + 1)
    let g := kernel.ι d ≫ (augmentation T π F N (i + 1)).app b
    ∃ (c : (term T π F N i).obj b ≅ T.obj (pullback f g)),
      c.hom ≫ π.app (pullback f g) ≫ pullback.fst f g =
        (augmentation T π F N i).app b
```

## New

Withdraw the Sheaf module using `deleted.txt`. The delivery tool leaves an empty
module with no declarations. Keep every upstream file unchanged. The seven shared
public declarations are provided by the upstream module with identical signatures
and implementations. The extra wrapper is unnecessary; its existential witness is
upstream `canonicalComparison`, whose first equation is:

```lean
theorem tower_comparison_canonical_first (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    (F : B ⥤ CochainComplex A ℤ) (N : ℤ) (b : B) (i : ℤ) (hi : i ≤ N) :
    (canonicalComparison T π F N b i hi).hom ≫ π.app _ ≫ pullback.fst _ _ =
      (augmentation T π F N i).app b
```

Reattach all four DAG nodes to the upstream module. The first-projection node is
realized by `canonicalComparison` and `tower_comparison_canonical_first` together;
it no longer names the deleted existential wrapper. Other declaration lists stay
unchanged. Update the proof-origin paths to the actual retained implementation.
No mathematical statement, construction, proof route, unit, or target meaning changes.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.CyclePullbackTowerComparison | Y5 | Withdraw duplicate declarations. |
| WeilConjectures.Algebra.Homology.CyclePullbackCore | not adapted | Already uses the upstream module; unchanged source compiles. |

There are no remaining importers of the withdrawn module. Source search finds no
external call to `tower_comparison_first`. All uses of shared declarations continue
to resolve to the identical upstream implementations. The former Sheaf Core consumer
listed in `coord/retire-items.tsv` is absent; this delivery does not recreate it.

## Status

landed 20261020T135441-L-1825136 2026-10-20 (merge of deliver/Y5/Sheaf.Algebra.Homology.CyclePullbackTowerComparison)
