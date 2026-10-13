# AlgebraicGeometry.Scheme.Modules.picardExternalCup_left_cech_comparison

## Reason
The proof adds proof-only imports and namespace declarations needed for the tensor Kunneth and direct-sum argument. The theorem signature and all public mathematical interfaces remain unchanged.

## Old
```lean
theorem picardExternalCup_left_cech_comparison
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    (G : Y.Modules) [G.IsQuasicoherent] :
    ∃ θ : picardLeftTensorCechFunctor f g G ⟶ picardLeftProductCechFunctor f g G,
      ∀ (F : X.Modules) (_ : F.IsQuasicoherent)
        (d : picardExternalTotal f g F G ⟶
          picardScalarModel (pullback.fst f g ≫ f) (externalCupCoefficients f g F G)),
        IsPicardExternalCupCochain f g F G d → ∀ n : ℕ,
          ∃ (a : ((picardLeftTensorCechFunctor f g G).obj F).homology (n : ℤ) ≅
              (picardExternalTotal f g F G).homology (n : ℤ))
            (b : ((picardLeftProductCechFunctor f g G).obj F).homology (n : ℤ) ≅
              (picardScalarModel (pullback.fst f g ≫ f)
                (externalCupCoefficients f g F G)).homology (n : ℤ)),
            HomologicalComplex.homologyMap (θ.app F) (n : ℤ) ≫ b.hom =
              a.hom ≫ HomologicalComplex.homologyMap d (n : ℤ)
```

## New
```lean
theorem picardExternalCup_left_cech_comparison
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    (G : Y.Modules) [G.IsQuasicoherent] :
    ∃ θ : picardLeftTensorCechFunctor f g G ⟶ picardLeftProductCechFunctor f g G,
      ∀ (F : X.Modules) (_ : F.IsQuasicoherent)
        (d : picardExternalTotal f g F G ⟶
          picardScalarModel (pullback.fst f g ≫ f) (externalCupCoefficients f g F G)),
        IsPicardExternalCupCochain f g F G d → ∀ n : ℕ,
          ∃ (a : ((picardLeftTensorCechFunctor f g G).obj F).homology (n : ℤ) ≅
              (picardExternalTotal f g F G).homology (n : ℤ))
            (b : ((picardLeftProductCechFunctor f g G).obj F).homology (n : ℤ) ≅
              (picardScalarModel (pullback.fst f g ≫ f)
                (externalCupCoefficients f g F G)).homology (n : ℤ)),
            HomologicalComplex.homologyMap (θ.app F) (n : ℤ) ≫ b.hom =
              a.hom ≫ HomologicalComplex.homologyMap d (n : ℤ)
```

The new generator module adds `picardExternalCup_left_cech_generators`. The comparison
module privately imports that module and `Sheaf.Algebra.Homology.TensorKunnethNat`
and adds `open scoped TensorProduct DirectSum` for proof notation. No existing
statement or definition changes; the record covers the added module and namespace
command that the preflight classifies as visible changes.

## Users
| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftCechComparison | J2 | proof implementation |

## Status
landed 20261013T115430-L-3359275 2026-10-13 (merge of deliver/J2/Sheaf.AlgebraicGeometry.PicardExternalCupLeftCechComparison)
