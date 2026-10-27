# AlgebraicGeometry.Scheme.fixedScalarEtaleSheafEquivalence

## Reason

The fixed-scalar etale-origin equivalence needs an explicit etale cochain equivalence,
its pro-etale derived localization factors, a sheaf constructibility bridge, the ordinary
comparison square, and a constant-field Tor bound. New proved APIs expose these parts
without modifying any existing public declaration, target or definition.

## Old

The four new modules and their public declarations are absent. The item has its original
public imports and the original statement of `AlgebraicGeometry.Scheme.fixedScalar_etaleOrigin`.
No existing definition or signature is replaced.

## New

`Sheaf.AlgebraicGeometry.FixedScalarEtaleModel` explicitly defines the etale and pro-etale
scalar sheaf equivalences, the termwise etale functor, the pro-etale derived functor and
the canonical localization factor, with additive/equivalence proofs. It proves equality
with the prescribed `fixedScalarComplexToModel`.

`Sheaf.AlgebraicGeometry.FixedScalarEtaleConstructibleSheaf` proves
`fixedScalarEtale_constructible_sheaf`: coefficient constructibility of the explicit model
is equivalent to `IsConstructibleSheaf`, for a Noetherian ring and Noetherian scheme.

`Sheaf.AlgebraicGeometry.FixedScalarOrdinaryComparison` proves
`fixedScalar_ordinary_comparison`: the etale forward equivalence commutes with ordinary
comparison inverse image and the pro-etale forward equivalence, over any commutative ring.

`Sheaf.AlgebraicGeometry.CoefficientFieldTorBounds` proves
`CategoryTheory.coefficientFieldTorBounds`: a coefficient-model derived object over a
constant field with cohomology bounded in an ordered interval has Tor amplitude in that
same interval. These are all complete proofs, with no new postponed obligation.

The new principal signatures are:

```lean
def fixedScalarEtaleSheafEquivalence (X : Scheme.{u}) (k : Type (u + 1)) [CommRing k] :
    Sheaf (X.smallEtaleTopology) (ModuleCat.{u + 1} k) ≌
      ConstantCompletion.Mod
        (ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, u} X) k)
```

```lean
theorem coefficientFieldTorBounds {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (k : Type w) [Field k]
    (K : ConstantCompletion.D (ConstantCompletion.constant J k))
    (a b : ℤ) (hab : a ≤ b)
    (h : ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((coefficientModelCohomology _ q).obj K)) :
    HasCoefficientModelTorAmplitude _ K a b
```

```lean
theorem fixedScalarEtale_constructible_sheaf (X : Scheme.{u}) [IsNoetherian X]
    (k : Type (u + 1)) [CommRing k] [IsNoetherianRing k]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} k)) :
    IsCoefficientConstructibleEtaleModule.{u, u} X k
      ((fixedScalarEtaleSheafEquivalence X k).functor.obj F) ↔ IsConstructibleSheaf F
```

```lean
theorem fixedScalar_ordinary_comparison (X : Scheme.{u})
    (k : Type (u + 1)) [CommRing k] :
    Nonempty ((fixedScalarEtaleSheafEquivalence X k).functor ⋙
        ProEtale.constructibleComparisonPullback.{u, u} X k ≅
      ProEtale.comparisonUpperStar (ModuleCat.{u + 1} k) X ⋙
        (fixedScalarProEtaleSheafEquivalence X k).functor)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FixedScalarEtaleOrigin | M3 | Proof uses the new helper APIs; original signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.FixedScalarEtaleModel | M3 (new) | New explicit constructions and proved factors. |
| Sheaf.AlgebraicGeometry.FixedScalarEtaleConstructibleSheaf | M3 (new) | Uses the explicit equivalences. |
| Sheaf.AlgebraicGeometry.FixedScalarOrdinaryComparison | M3 (new) | Uses the explicit equivalences and the existing general-ring square. |
| Sheaf.AlgebraicGeometry.CoefficientFieldTorBounds | M3 (new) | Generic constant-field bound; no original consumer changed. |

All other consumers retain identical definitions, signatures and public imports. There are
no existing consumers of these fresh names. No target meaning changes or forced adaptations.

## Status

landed 20261025T180900-L-4047669 2026-10-25 (merge of deliver/M3/Sheaf.AlgebraicGeometry.FixedScalarEtaleOrigin)
