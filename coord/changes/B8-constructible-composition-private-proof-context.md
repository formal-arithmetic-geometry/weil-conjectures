# AlgebraicGeometry.Etale.hasConstructibleHigherDirectImages_comp

## Reason

The delivery proves the existing theorem by the prescribed Leray spectral sequence
argument. The static interface check detects added `open`, `section`, and `variable`
commands used to state three proved private helpers. The opens affect name resolution
in this file only; the section variables are parameters of private proof helpers.
No public declaration signature or public import changes. This record documents the
static context delta; no definition or target meaning changes.

The added context is:
```lean
open CategoryTheory Limits
open scoped AlgebraicGeometry.Etale
section SpectralSequence
variable {Z : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
```
The section ends before the original public theorem. All helpers are private theorems,
fully proved; they export no instances or notation.

## Old

```lean
theorem hasConstructibleHigherDirectImages_comp
    (k : Type u) [Field k] (N : ℕ) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    (hX : IsSmoothBaseChangeCoefficients N Λ X)
    (hY : IsSmoothBaseChangeCoefficients N Λ Y)
    (hZ : IsSmoothBaseChangeCoefficients N Λ Z)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : HasConstructibleHigherDirectImages k N Λ hX hY f)
    (hg : HasConstructibleHigherDirectImages k N Λ hY hZ g) :
    HasConstructibleHigherDirectImages k N Λ hX hZ (f ≫ g)
```

Original name-resolution context: `open CategoryTheory`.

## New

```lean
theorem hasConstructibleHigherDirectImages_comp
    (k : Type u) [Field k] (N : ℕ) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    (hX : IsSmoothBaseChangeCoefficients N Λ X)
    (hY : IsSmoothBaseChangeCoefficients N Λ Y)
    (hZ : IsSmoothBaseChangeCoefficients N Λ Z)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : HasConstructibleHigherDirectImages k N Λ hX hY f)
    (hg : HasConstructibleHigherDirectImages k N Λ hY hZ g) :
    HasConstructibleHigherDirectImages k N Λ hX hZ (f ≫ g)
```

The signature is verbatim identical. Its proof now uses the proved private helpers
`constructible_homology`, `constructible_page`, and `constructible_abutment`.
Only proof imports change: the retired spectral-sequence wrapper is removed;
constructibility comparison and zero-object constructibility are imported privately.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.ConstructibleHigherDirectImagesComp
--uses hasConstructibleHigherDirectImages_comp` reports three downstream modules.
The source-text name search finds no existing consumer proof mentioning the theorem;
the direct importer still has its original `sorry`. Each consumer's statement and
public import context are unchanged, and no adaptation is required.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ConstructibleHigherDirectImagesComp | B8 | The theorem is proved; signature identical; only private helpers and local name-resolution context added. |
| Sheaf.AlgebraicGeometry.ProjectiveConstructibilityFromLine | V2 | Unchanged; imports the same public theorem with its identical signature. |
| Sheaf.AlgebraicGeometry.ProjectiveConstructibleHigherDirectImages | N4 | Unchanged transitive consumer; no exported declaration or definition changes. |
| Sheaf.AlgebraicGeometry.ProperConstructibleHigherDirectImages | F3 | Unchanged transitive consumer; no exported declaration or definition changes. |

No target uses a changed definition; no target meaning review is reopened.

## Status

landed 20261018T062705-L-632586 2026-10-18 (merge of deliver/B8/Sheaf.AlgebraicGeometry.ConstructibleHigherDirectImagesComp)
