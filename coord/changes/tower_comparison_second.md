# CochainComplex.CyclePullback.tower_comparison_second

## Reason

Repair reviewer X-6c272, head 6c272bd40, E2 / brief point 4. The old helper is
false for arbitrary comparisons preserving only the first projection. The
swapped comparison in rational vector spaces with zero F preserves the zero
augmentation but exchanges the two differential coordinates.

The replacement states and proves the second projection equation for the
explicit canonicalComparison. Its data is constructed with eqToIso of a proved
recursive equality, evaluation's canonical kernel and pullback isomorphisms,
and T.mapIso. No data or equality proof is taken from an unproved theorem.
The complete signatures of tower_comparison and tower_comparison_first are
unchanged; the former now returns this canonical witness and both equations.

## Old

```lean
theorem tower_comparison_second {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    (F : B ⥤ CochainComplex A ℤ) (N : ℤ) (b : B) (i : ℤ) (hi : i ≤ N)
    (c : (term T π F N i).obj b ≅
      T.obj (pullback ((F.obj b).d i (i + 1))
        (kernel.ι ((differential T π F N (i + 1)).app b) ≫
          (augmentation T π F N (i + 1)).app b)))
    (h : c.hom ≫ π.app _ ≫ pullback.fst _ _ =
      (augmentation T π F N i).app b) :
    c.hom ≫ π.app _ ≫ pullback.snd _ _ ≫
      kernel.ι ((differential T π F N (i + 1)).app b) =
      (differential T π F N i).app b
```

## New

```lean
theorem tower_comparison_second {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    (F : B ⥤ CochainComplex A ℤ) (N : ℤ) (b : B) (i : ℤ) (hi : i ≤ N) :
    (canonicalComparison T π F N b i hi).hom ≫ π.app _ ≫ pullback.snd _ _ ≫
      kernel.ι ((differential T π F N (i + 1)).app b) =
      (differential T π F N i).app b
```

New public construction declarations are evaluatedPullbackIso, indexedPullback,
term_step_eq and canonicalComparison. The new proved projection lemma is
tower_comparison_canonical_first. Their full signatures and implementations are
in the delivered module; the construction is recorded by node
def-tower-canonical-comparison-g3. The two added public Mathlib imports are
required by these construction bodies.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.CyclePullbackTowerComparison | G3 | The only user of tower_comparison_second. tower_comparison now supplies canonicalComparison and pairs the two canonical projection equations. |

The source scan with tools/downstream.py --uses tower_comparison_second found
only this module; no external module mentions the changed helper. Existing
existential comparison signatures, all target signatures, and existing tower
definitions remain unchanged. No other module requires a forced adaptation.
The sole DAG citer is lem-pc-cycle-pullback-tower-comparison-stage3: its statement
still holds and its proof dependencies are updated to the canonical route.

## Status

landed 20261012T223406-L-1637048 2026-10-12 (merge of deliver/G3/Sheaf.Algebra.Homology.CyclePullbackTowerComparison)
