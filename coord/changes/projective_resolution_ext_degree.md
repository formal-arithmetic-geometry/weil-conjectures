# ModuleCat.projective_resolution_ext_degree

## Reason

The prior declaration stated a generic abelian-category resolution criterion, while the
repaired callers and the project's module-level predicate use `HasProjectiveResolutionLE`
for modules. The declaration is specialized to that existing predicate and its proof now
reuses the proved successor splicing theorem. This is the upstream duplicate-projective-
dimension repair; no target statement is changed.

## Old

```lean
theorem projective_resolution_ext_degree
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughProjectives C]
    (X : C) (n : ℕ) :
    (∃ P : ProjectiveResolution X, ∀ i : ℕ, n < i → Limits.IsZero (P.complex.X i)) ↔
      HasProjectiveDimensionLE X n
```

## New

```lean
theorem projective_resolution_ext_degree
    {R : Type u} [CommRing R] (X : ModuleCat.{max u v} R) (n : ℕ) :
    HasProjectiveResolutionLE X n ↔ HasProjectiveDimensionLE X n
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffinePolynomialResolutionOfStalkwise | unclaimed | proof adapted to the module-specific bridge; statement unchanged |
| Sheaf.RingTheory.ProjectiveResolutionExtAllDegrees | unclaimed | proof adapted to the module-specific bridge; statement unchanged |
| Sheaf.RingTheory.ProjectiveResolutionExtCharacterization | unclaimed | proof adapted to the module-specific bridge; statement unchanged |

## Status

landed 20261013T234510-L-2162546 2026-10-13 (merge of deliver/G2/Sheaf.RingTheory.ProjectiveResolutionExtDegree)
