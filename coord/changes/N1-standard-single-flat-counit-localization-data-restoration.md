# AlgebraicGeometry.standardSingleFlatCounit_localization_data

## Reason

Restore the exact theorem attachment named in the assigned `coord/rework.tsv` row.
The library path is absent; its full source is preserved at
`quarantine/Sheaf/AlgebraicGeometry/StandardSingleFlatCounitLocalizationData.lean`.
The current presentation provider has already been repaired by B3. The archived
statement is true: the zero complex is bounded above and termwise flat. Restore
that statement with a direct Mathlib proof of flatness, removing the old
proof-only categorical-flatness import. The archived declaration's signature and
docstring are unchanged. This is a source restoration, not a new theorem hole or
a change to the meaning of a target.

## Old

The library source is absent. The archived signature is:

```lean
theorem standardSingleFlatCounit_localization_data
    (h_affine : ∀ {Y₀ B₀ A₀ : Scheme.{u}} (p₀ : Y₀ ⟶ B₀)
      [QuasiCompact p₀] [QuasiSeparated p₀] [IsAffine B₀] [IsAffine A₀]
      (g₀ : A₀ ⟶ B₀), StandardSingleFlatCounitOnOpen p₀ g₀ ⊤)
    {Y B A : Scheme.{u}} (p : Y ⟶ B) [QuasiCompact p] [QuasiSeparated p]
    (M : Y.Modules) [M.IsQuasicoherent] (hM : M.IsFlatOver p) (g : A ⟶ B) (a : A) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let R := B.presheaf.stalk (g a)
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ),
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i)) ∧
      (∀ i : ℤ, Module.Flat R (P.X i))
```

## New

The restored signature is identical:

```lean
theorem standardSingleFlatCounit_localization_data
    (h_affine : ∀ {Y₀ B₀ A₀ : Scheme.{u}} (p₀ : Y₀ ⟶ B₀)
      [QuasiCompact p₀] [QuasiSeparated p₀] [IsAffine B₀] [IsAffine A₀]
      (g₀ : A₀ ⟶ B₀), StandardSingleFlatCounitOnOpen p₀ g₀ ⊤)
    {Y B A : Scheme.{u}} (p : Y ⟶ B) [QuasiCompact p] [QuasiSeparated p]
    (M : Y.Modules) [M.IsQuasicoherent] (hM : M.IsFlatOver p) (g : A ⟶ B) (a : A) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let R := B.presheaf.stalk (g a)
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ),
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i)) ∧
      (∀ i : ℤ, Module.Flat R (P.X i))
```

The proof constructs `HomologicalComplex.zero`, uses the bound `0`, and proves
flatness via `ModuleCat.subsingleton_of_isZero`, `Module.Free.of_subsingleton`
and `Module.Flat.of_free`. No data is selected from an unproved theorem.

## Users

`python3 tools/downstream.py
Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalizationData --allow-missing
--uses AlgebraicGeometry.standardSingleFlatCounit_localization_data` reports
zero downstream modules and zero declaration users. A text search of both
`lean/` and `quarantine/` finds no other Lean consumer.

| module | group holding it | effect |
| --- | --- | --- |
| None | — | No Lean consumer requires adaptation. |

The pending DAG parent
`lem-pc-standard-single-flat-counit-localization-completion` still names this
node in its proof plan. Its archived Lean proof instead constructs the actual
presentation complex through the homology theorem and does not use this
existential witness. Neither that parent nor its dependencies are changed or
withdrawn. The assigned node's Lean attachment and statement dependencies remain
intact. No unit route, adopted source-library declaration, target statement or
public definition is changed.

## Status

landed 20261021T004837-L-1793805 2026-10-21 (merge of deliver/N1/Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalizationData)
