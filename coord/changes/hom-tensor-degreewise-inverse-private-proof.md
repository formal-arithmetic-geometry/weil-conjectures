# homTensorDegreewise_inverse

## Reason

The static interface checker conservatively classifies the newly added private
helper namespace, its scoped `open`/`variable` commands and local proof attributes
as an interface change. All helpers are private and fully proved. These commands
support the concrete tensor-Hom and product-extensionality inverse calculations;
they add no public declaration to this existing module, change no public import,
and change no existing statement or definition. This record documents that
classification without claiming a mathematical statement change.

## Old

```lean
theorem homTensorDegreewise_inverse (K L M : CochainComplex Mod ℤ) (n : ℤ) :
    letI := SheafOfModules.monoidalCategory R
    ∃ b : (homComplex (R := R)
        (CochainComplex.mapBifunctor K L (curriedTensor Mod)) M).X n ⟶
      (homComplex (R := R) K (homComplex (R := R) L M)).X n,
      ∀ a, HomTensorDegreewiseEquation R K L M n a → a ≫ b = 𝟙 _ ∧ b ≫ a = 𝟙 _
```

The old proof was `by sorry`. There was no `IsoTensorHom` private-helper namespace
and no private extensionality/restriction helpers.

## New

```lean
theorem homTensorDegreewise_inverse (K L M : CochainComplex Mod ℤ) (n : ℤ) :
    letI := SheafOfModules.monoidalCategory R
    ∃ b : (homComplex (R := R)
        (CochainComplex.mapBifunctor K L (curriedTensor Mod)) M).X n ⟶
      (homComplex (R := R) K (homComplex (R := R) L M)).X n,
      ∀ a, HomTensorDegreewiseEquation R K L M n a → a ≫ b = 𝟙 _ ∧ b ≫ a = 𝟙 _
```

The identical statement is proved from the new reverse-construction theorem.
The private namespace `IsoTensorHom` contains proved concrete presheaf
currying/uncurrying helpers and their equivalence, generalized to independent
site universes `u`, `v` and an extra ambient universe `w`. Its four curry-application
lemmas explicitly bind coefficients in `CommRingCat.{max u v w}` and modules in
`PresheafOfModules.{max u v w}`. This repairs the duplicate-statement return:
the localized private APIs instead fix coefficients to `max u v`, and importing
their modules would create a cycle. The public source API fixes all universes
to one universe. These generalized private statements have complete proofs. Additional private lemmas give
Hom-product section/morphism extensionality, restriction evaluation and localized
tensor extensionality. Every new helper is private; every existing declaration
retains its signature and visibility. No public definition changes, so no target
statement-meaning review is reopened.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.HomTensorDegreewiseIso | F3 | Only its proof changes; all new helpers are private. |
| Sheaf.Algebra.Homology.HomTensorDegreewise | unclaimed | Calls the identical inverse theorem; no adaptation required. |

`tools/downstream.py Sheaf.Algebra.Homology.HomTensorDegreewiseIso --uses
homTensorDegreewise_inverse` reports the item and `HomTensorDegreewise` as the two
textual users of the declaration. Its 492 transitive downstream modules retain
the same public declarations and imports and need no forced adaptation. No other
module is adapted by this delivery. The static command-change marker names no
additional downstream declaration user.

## Status

landed 20261013T133225-L-4192889 2026-10-13 (merge of deliver/F3/Sheaf.Algebra.Homology.HomTensorDegreewiseIso)
