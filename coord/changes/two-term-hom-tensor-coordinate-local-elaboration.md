# WeilConjectures.IntegralHom.twoTermFreeHomTensor_coordinate_unique

## Reason

Prove uniqueness by the coproduct/product universal properties and pure-tensor
identity-slice evaluation. Declaration signatures and the public import remain
unchanged. The static command comparison flags the added local attributes, so this
record documents their scope. No declaration or instance visible to importers is
changed, and no consumer requires adaptation. No target statement or definition
changes meaning.

The item locally prioritizes `abSheafify` and `abLocallyBijective`, locally avoids
unfolding `homComplexFunctor` and `SheafOfModules.monoidalCategory`, and disables
`CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall` only for the
uniqueness declaration. These are elaboration controls: they avoid a generic
sheafification instance creating unresolved coefficient-universe metavariables.
The new fully proved helper module also makes `SheafOfModules.monoidalCategory`
locally irreducible. All local attribute scopes end within their module.

## Old

```lean
theorem twoTermFreeHomTensor_coordinate_unique
    (P I Q : CochainComplex (Modules.{t, u} Y R) ℤ)
    (hzero : ∀ k : ℤ, k ≠ -1 → k ≠ 0 → IsZero (Q.X k))
    (eNeg : Q.X (-1) ≅ (show Modules.{t, u} Y R from SheafOfModules.unit
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)))
    (eZero : Q.X 0 ≅ (show Modules.{t, u} Y R from SheafOfModules.unit
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)))
    (f g : ((totalTensor Y R).obj
        (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I)).obj Q ⟶
      homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P
        (((totalTensor Y R).obj I).obj Q))
    (hf : IsSignedHomTensor Y R P I Q f) (j : ℤ)
    (hg : ∀ (a b p : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
        (v : (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I).X a
          |>.val.obj U) (z : (Q.X b).val.obj U) (x : (P.X p).val.obj U),
        evaluate Y R P (((totalTensor Y R).obj I).obj Q) (a + b) p U
          ((g.f (a + b)).val.app U
            (totalPair Y R (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)}
              (R := R) P I) Q a b U v z)) x =
          (b * p).negOnePow •
            (eqToHom (congrArg (fun k : ℤ ↦ (((totalTensor Y R).obj I).obj Q).X k)
              (add_assoc p a b))).val.app U
              (totalPair Y R I Q (p + a) b U (evaluate Y R P I a p U v x) z)) :
    f.f j = g.f j
```

## New

The same signature, with the following local elaboration setup:

```lean
attribute [local instance 2000] abSheafify abLocallyBijective
attribute [local irreducible] homComplexFunctor SheafOfModules.monoidalCategory
```

The uniqueness declaration alone is preceded by:

```lean
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
```

```lean
theorem twoTermFreeHomTensor_coordinate_unique
    (P I Q : CochainComplex (Modules.{t, u} Y R) ℤ)
    (hzero : ∀ k : ℤ, k ≠ -1 → k ≠ 0 → IsZero (Q.X k))
    (eNeg : Q.X (-1) ≅ (show Modules.{t, u} Y R from SheafOfModules.unit
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)))
    (eZero : Q.X 0 ≅ (show Modules.{t, u} Y R from SheafOfModules.unit
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)))
    (f g : ((totalTensor Y R).obj
        (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I)).obj Q ⟶
      homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P
        (((totalTensor Y R).obj I).obj Q))
    (hf : IsSignedHomTensor Y R P I Q f) (j : ℤ)
    (hg : ∀ (a b p : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
        (v : (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I).X a
          |>.val.obj U) (z : (Q.X b).val.obj U) (x : (P.X p).val.obj U),
        evaluate Y R P (((totalTensor Y R).obj I).obj Q) (a + b) p U
          ((g.f (a + b)).val.app U
            (totalPair Y R (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)}
              (R := R) P I) Q a b U v z)) x =
          (b * p).negOnePow •
            (eqToHom (congrArg (fun k : ℤ ↦ (((totalTensor Y R).obj I).obj Q).X k)
              (add_assoc p a b))).val.app U
              (totalPair Y R I Q (p + a) b U (evaluate Y R P I a p U v x) z)) :
    f.f j = g.f j
```

## Users

`tools/downstream.py --uses` reports the following modules mentioning either
`twoTermFreeHomTensor_coordinate_unique` or `IsSignedHomTensor`. Holders are from
the shared snapshot, except this dispatched item. No consumer source is changed.
The delivery tool compiled the one direct importer successfully against this packet.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.TwoTermFreeHomTensorCoordinateMap | G7 | uniqueness proof completed |
| Sheaf.Algebra.Homology.TwoTermFreeHomTensorComponents | unclaimed in snapshot | unchanged; direct importer passed |
| Sheaf.Algebra.Homology.SignedHomTensorMap | unclaimed in snapshot | unchanged |
| Sheaf.Paper.IntegralHomComparisonRepresentative | unclaimed in snapshot | unchanged |
| Sheaf.Paper.IntegralHomReducedEvaluation | unclaimed in snapshot | unchanged |
| Sheaf.Paper.IntegralHomRepresentativeSquare | unclaimed in snapshot | unchanged |
| Sheaf.Paper.SignedHomTensorComparison | unclaimed in snapshot | unchanged |

## Status

landed 20261028T055653-L-794316 2026-10-28 (merge of deliver/G7/Sheaf.Algebra.Homology.TwoTermFreeHomTensorCoordinateMap)
