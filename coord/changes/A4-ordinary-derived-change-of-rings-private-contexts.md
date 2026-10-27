# ModuleCat.nonempty_ordinaryDerivedChangeOfRings

## Reason

Prove the existing theorem using private helpers with universe-polymorphic section
variables. Stage-3 preflight treats additions of `section`, `universe`, and `variable`
commands as an interface change and requests this record. They only supply the
elaboration contexts of private declarations. Both helper sections end before the
existing public theorem. There is no new public instance, notation, attribute or
signature. No existing definition body or public import changes.

## Old

```lean
theorem nonempty_ordinaryDerivedChangeOfRings {R S : Type u}
    [CommRing R] [CommRing S] (φ : R →+* S) :
    Nonempty (OrdinaryDerivedChangeOfRings φ) := by
  sorry
```

## New

```lean
theorem nonempty_ordinaryDerivedChangeOfRings {R S : Type u}
    [CommRing R] [CommRing S] (φ : R →+* S) :
    Nonempty (OrdinaryDerivedChangeOfRings φ) := by
```

The body is the complete proof in the delivered module, with no remaining holes.
The additional command contexts, verbatim, are:

```lean
section LocalizationTensor

universe v w
variable {A : Type*} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
  [HasDerivedCategory.{v} A] [Abelian.HasFunctorialFlatResolution A]
```

This section contains only `private theorem ordinary_Q_μ` and
`private theorem ordinary_Q_ε`, followed by `end LocalizationTensor`.

```lean
section UniversalPair

universe v w
variable {A B : Type*} [Category.{v} A] [Category.{w} B] [Abelian A] [Abelian B]
  [IsGrothendieckAbelian.{v} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [MonoidalClosed A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
  [HasDerivedCategory.{v} A] [HasDerivedCategory.{w} B]
  [HasColimitsOfSize.{0, 0} A]
```

This section contains only `private theorem ordinary_pair`, followed by
`end UniversalPair`. These commands add no parameters to any existing declaration.
All helpers are private and fully proved; no new public signatures use them.

## Users

Checked with `tools/downstream.py` on the assigned module, with `--uses` for all
five existing public declarations. The full downstream list contains the two
consumer modules below. Their uses retain exactly the same types and definitions.
Neither requires adaptation. No target statement or definition changes meaning.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings | A4 | The existing theorem is proved; all public signatures and definition bodies are preserved. |
| Sheaf.Paper.IntegralPointDualModels | unclaimed | Its scalar reduction and monoidal instance use the unchanged public definitions. No edit needed. |
| Sheaf.Paper.LocalizationScalarUnit | unclaimed | Its public import retains the same interface. No edit needed. |

## Status

landed 20261022T142407-L-730339 2026-10-22 (merge of deliver/A4/Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings)
