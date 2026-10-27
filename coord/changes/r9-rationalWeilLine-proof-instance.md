# WeilConjectures.FrobeniusCoefficientTwists.rationalWeilLine

## Reason

The file now respects transparency while keeping large functor constructions folded.
The four Weil-line constructors need their existing Frobenius-isomorphism proof
supplied explicitly. Each added local instance is the public theorem
`Iso.isIso_hom` applied to the already constructed geometric Frobenius iso. IsIso
is a proposition, so proof irrelevance makes the resulting definitions identical
to their previous definitions. No object, morphism or mathematical target changes.

## Old

```lean
def rationalWeilLine (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (m : ℤ) :
    sfWeilComplex D l hl Y₀ E :=
  letI : ∀ x : (D.geometricFiber Y₀).left,
    Invertible (l : (D.geometricFiber Y₀).left.residueField x) :=
      fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x
  IsoAlgebra.mk (sfRationalTwistingCoefficient l E (D.geometricFiber Y₀).left m)
    (rationalDerivedLineMap l E (D.geometricFrobenius Y₀).hom m)
```

## New

```lean
def rationalWeilLine (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (m : ℤ) :
    sfWeilComplex D l hl Y₀ E :=
  letI : IsIso (D.geometricFrobenius Y₀).hom := (D.geometricFrobenius Y₀).isIso_hom
  letI : ∀ x : (D.geometricFiber Y₀).left,
    Invertible (l : (D.geometricFiber Y₀).left.residueField x) :=
      fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x
  IsoAlgebra.mk (sfRationalTwistingCoefficient l E (D.geometricFiber Y₀).left m)
    (rationalDerivedLineMap l E (D.geometricFrobenius Y₀).hom m)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | R9 | Supplies the same proof explicitly; signatures and data are preserved. |
| Sheaf.Paper.TwistFrobeniusScalar | A8 | Unchanged; no adaptation, by proof irrelevance. |
| Sheaf.Paper.InverseContravariantBidual | unclaimed | Unchanged; no adaptation, by proof irrelevance. |
| Sheaf.Paper.WeilTateTwistFrobenius | unclaimed | Unchanged; no adaptation, by proof irrelevance. |

Users were found by a library-wide text search. No other module is adapted.
No hypothesis is added, and the mathematical definition is unchanged.

## Status

landed 20261026T070903-L-3686575 2026-10-26 (merge of deliver/R9/Sheaf.Paper.FrobeniusCoefficientTwistsCanonical)
