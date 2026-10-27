# AlgebraicGeometry.ProEtale.spIntegralTwistLevel_finiteEtale_representation

## Reason

Expose the finite-level geometric representation required by the current
blueprint's Integral twist argument, independently of inverse limits and
inverse image. The original item is reduced to this strictly smaller step;
all transition, geometric-limit and categorical transfer arguments are proved.

## Old

No declaration of this finite-level representation existed. The original item
`spIntegralTwist_inverseImage_isLimit` had one whole-proof sorry.
Its existing signature remains verbatim.

## New

```lean
theorem spIntegralTwistLevel_finiteEtale_representation
    (Y : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ y : Y, Invertible (ℓ : Y.residueField y)]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    ∃ V : Y.ProEt, IsFinite V.hom ∧ Etale V.hom ∧
      Nonempty ((Scheme.ProEt.topology Y).uliftYoneda.{u + 1}.obj V ≅
        (sheafCompose (Scheme.ProEt.topology Y) (forget AddCommGrpCat.{u + 1})).obj
          (spIntegralTwistLevel Y ℓ E n).X)
```

The whole proof is a named theorem with sorry and node
`lem-pur-native-integral-tate-finite-representation`. No definition uses a
witness selected from this theorem; the item eliminates the existence only
inside a proposition proof.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.NativeIntegralTateTowerLimit | Z5 | New private proof import; signature unchanged. The proof constructs the whole represented diagram from these individual levels. |

The new declaration has no pre-existing users. No existing statement,
definition or public import is modified, and no consumer adaptation is needed.

## Status

landed 20261025T164934-L-1135274 2026-10-25 (merge of deliver/Z5/Sheaf.Paper.NativeIntegralTateTowerLimit)
