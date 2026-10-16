# SheafOfModules.tensorPreadditive and SheafOfModules.flat_to_cat

## Reason

The returned delivery duplicated these existing private lemmas in the acyclic-pullback
module. Export the original, fully proved lemmas in their existing unclaimed module
and import that module, maintaining one proof of each fact. Categorical flatness must
be publicly imported because it now occurs in an exported statement. The assigned
module's duplicate reflexivity theorem is deleted; definitional equality suffices.

## Old

In `Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients`, with its existing
section variables and notation, the declarations were:

```lean
private theorem tensorPreadditive :
    letI := isMonoidal_W_independentCoefficients R
    letI := monoidalCategory R
    MonoidalPreadditive 𝒜 := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := symmetricCategory R
  let (M : 𝒜) : (tensorLeft M).Additive := tensorLeft_additive_independent R M
  have (M : 𝒜) : (tensorRight M).Additive :=
    Functor.additive_of_iso (F := tensorLeft M)
      (BraidedCategory.tensorLeftIsoTensorRight M)
  exact
    { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
      zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
      whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
      add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add (f := f) (g := g) }

private theorem flat_to_cat (M : 𝒜) (h : IsFlatOnSite (J := J) (R := R) M) :
    letI := isMonoidal_W_independentCoefficients R
    letI := monoidalCategory R
    ObjectProperty.flat M := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := symmetricCategory R
  have hr : exactFunctor _ _ (tensorRight M) :=
    (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R M) h
  exact ⟨(exactFunctor _ _).prop_of_iso
    (BraidedCategory.tensorLeftIsoTensorRight M).symm hr, hr⟩
```

There was no public import of
`WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic`.

The retained, returned item also locally repeated these two signatures and had
`private theorem changeOfRings_eq_ofUniverses ... := by rfl`.

## New

The same existing declarations are exported in the same module, with new descriptive
docstrings. Their complete statements and proof bodies are unchanged:

```lean
theorem tensorPreadditive :
    letI := isMonoidal_W_independentCoefficients R
    letI := monoidalCategory R
    MonoidalPreadditive 𝒜 := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := symmetricCategory R
  let (M : 𝒜) : (tensorLeft M).Additive := tensorLeft_additive_independent R M
  have (M : 𝒜) : (tensorRight M).Additive :=
    Functor.additive_of_iso (F := tensorLeft M)
      (BraidedCategory.tensorLeftIsoTensorRight M)
  exact
    { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
      zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
      whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
      add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add (f := f) (g := g) }

theorem flat_to_cat (M : 𝒜) (h : IsFlatOnSite (J := J) (R := R) M) :
    letI := isMonoidal_W_independentCoefficients R
    letI := monoidalCategory R
    ObjectProperty.flat M := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := symmetricCategory R
  have hr : exactFunctor _ _ (tensorRight M) :=
    (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R M) h
  exact ⟨(exactFunctor _ _).prop_of_iso
    (BraidedCategory.tensorLeftIsoTensorRight M).symm hr, hr⟩
```

Add `public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic`.
No instance is registered and no mathematical definition changes.

In `Sheaf.Algebra.Homology.RingedToposAcyclicKFlatPullback`, delete both local copies
and retain the existing proof-only import of `BoundedFlatIndependentCoefficients`. Delete the
local `changeOfRings_eq_ofUniverses` theorem and change its only call from
`rw [hobj M, changeOfRings_eq_ofUniverses]` to `rw [hobj M]`.

## Users

`tools/downstream.py --uses tensorPreadditive` and `--uses flat_to_cat` list only
`BoundedFlatIndependentCoefficients` on the baseline, because the helpers were private.
The new acyclic-pullback module is their additional caller. No existing public
statement, definition body, instance, target or theorem meaning changes. The imported
flatness definition is the existing one, not a new notion.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients | unclaimed | Export two existing helpers, document them, and import their signature's flatness definition publicly; existing calls unchanged. |
| Sheaf.Algebra.Homology.RingedToposAcyclicKFlatPullback | F2 | Import and use the existing helpers; delete three duplicate local theorems. |
| Sheaf.Paper.KFlatRingedToposPullback | unclaimed | Existing call of the unchanged acyclic theorem needs no adaptation. Its private change-of-rings equality remains private and is not imported here. |

## Status

landed 20261016T075723-L-1295408 2026-10-16 (merge of deliver/F2/Sheaf.Algebra.Homology.RingedToposAcyclicKFlatPullback)
