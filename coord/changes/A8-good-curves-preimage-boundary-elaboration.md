# AlgebraicGeometry.Etale.goodCurvesPreimage_boundary

## Reason

The proof uses the coproduct APIs and selects the general discrete-colimit instances locally
so finite-index induction and the lifted-index coproduct use compatible constructions.
The static scanner flags namespace commands conservatively. The new `open` affects name
resolution only. The attribute has `local` scope within `AlgebraicGeometry.Etale` and exports
no instance or priority change. The helper is private and completely proved. There is no
change to a definition, a public signature, a target, or the meaning of a consumer statement.

## Old

No local colimit-instance priority command or `open CategoryTheory.Limits` in this namespace.
The public signature was:

```lean
theorem goodCurvesPreimage_boundary
    {X V : Scheme.{u}} [IsNoetherian X] [IsNoetherian V]
    (f : X ⟶ V) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (n : ℕ) (T Y Ybar : Fin n → Scheme.{u})
    (t : ∀ i, T i ⟶ V) (j : ∀ i, Y i ⟶ Ybar i) (p : ∀ i, Ybar i ⟶ T i)
    (ν : (∐ Y) ⟶ X) [IsFinite ν] [Surjective ν]
    (hcomm : ∀ i, Limits.Sigma.ι Y i ≫ ν ≫ f = j i ≫ p i ≫ t i)
    (ht : ∀ i, IsFinite (t i) ∧ AlgebraicGeometry.Etale (t i))
    (hj : ∀ i, IsOpenImmersion (j i))
    (hjp : ∀ i, Smooth (j i ≫ p i) ∧ Surjective (j i ≫ p i))
    (hp : ∀ i, Smooth (p i) ∧ IsProper (p i) ∧
      ∀ s : T i, GeometricallyConnected ((p i).fiberToSpecResidueField s) ∧
        topologicalKrullDim ((p i).fiber s) ≤ 1)
    (W : X.Opens)
    (hWi : ∀ (i : Fin n) (s : T i),
      Dense (((j i ≫ p i).fiberι s ≫ Limits.Sigma.ι Y i ≫ ν) ⁻¹' (W : Set X)))
    : IsNoetherian (∐ Ybar) ∧
      IsProper (Limits.Sigma.desc fun i ↦ p i ≫ t i) ∧
      ∃ (O : (∐ Ybar : Scheme.{u}).Opens)
        (e : Limits.pullback ν W.ι ≅ O.toScheme)
        (Z : Scheme.{u}) (i : Z ⟶ (∐ Ybar)),
        IsClosedImmersion i ∧ Set.range i.base = (O : Set (∐ Ybar : Scheme.{u}))ᶜ ∧
        e.hom ≫ O.ι ≫ (Limits.Sigma.desc fun k ↦ p k ≫ t k) =
          Limits.pullback.snd ν W.ι ≫ W.ι ≫ f ∧
        (i ≫ (Limits.Sigma.desc fun k ↦ p k ≫ t k)).IsQuasiFinite
```

## New

Added within the namespace:

```lean
open CategoryTheory.Limits

attribute [local instance high] instHasColimitOfHasColimitsOfShape
  hasColimitsOfShape_discrete
```

The public signature is unchanged:

```lean
theorem goodCurvesPreimage_boundary
    {X V : Scheme.{u}} [IsNoetherian X] [IsNoetherian V]
    (f : X ⟶ V) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (n : ℕ) (T Y Ybar : Fin n → Scheme.{u})
    (t : ∀ i, T i ⟶ V) (j : ∀ i, Y i ⟶ Ybar i) (p : ∀ i, Ybar i ⟶ T i)
    (ν : (∐ Y) ⟶ X) [IsFinite ν] [Surjective ν]
    (hcomm : ∀ i, Limits.Sigma.ι Y i ≫ ν ≫ f = j i ≫ p i ≫ t i)
    (ht : ∀ i, IsFinite (t i) ∧ AlgebraicGeometry.Etale (t i))
    (hj : ∀ i, IsOpenImmersion (j i))
    (hjp : ∀ i, Smooth (j i ≫ p i) ∧ Surjective (j i ≫ p i))
    (hp : ∀ i, Smooth (p i) ∧ IsProper (p i) ∧
      ∀ s : T i, GeometricallyConnected ((p i).fiberToSpecResidueField s) ∧
        topologicalKrullDim ((p i).fiber s) ≤ 1)
    (W : X.Opens)
    (hWi : ∀ (i : Fin n) (s : T i),
      Dense (((j i ≫ p i).fiberι s ≫ Limits.Sigma.ι Y i ≫ ν) ⁻¹' (W : Set X)))
    : IsNoetherian (∐ Ybar) ∧
      IsProper (Limits.Sigma.desc fun i ↦ p i ≫ t i) ∧
      ∃ (O : (∐ Ybar : Scheme.{u}).Opens)
        (e : Limits.pullback ν W.ι ≅ O.toScheme)
        (Z : Scheme.{u}) (i : Z ⟶ (∐ Ybar)),
        IsClosedImmersion i ∧ Set.range i.base = (O : Set (∐ Ybar : Scheme.{u}))ᶜ ∧
        e.hom ≫ O.ι ≫ (Limits.Sigma.desc fun k ↦ p k ≫ t k) =
          Limits.pullback.snd ν W.ι ≫ W.ι ≫ f ∧
        (i ≫ (Limits.Sigma.desc fun k ↦ p k ≫ t k)).IsQuasiFinite
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.GoodCurvesPreimageBoundary --uses
AlgebraicGeometry.Etale.goodCurvesPreimage_boundary` reports the following declaration users.
The remaining transitive importers see the same statement and exported instances.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.GoodCurvesPreimageBoundary | A8 | Item proof filled; signature identical. |
| Sheaf.AlgebraicGeometry.GoodCurvesPreimageConstructible | unclaimed | Existing application at line 277 has identical arguments and result; no adaptation. |

## Status

landed 20261019T112436-L-3939873 2026-10-19 (merge of deliver/A8/Sheaf.AlgebraicGeometry.GoodCurvesPreimageBoundary)
