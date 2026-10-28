# WeilConjectures.IntegralVerdier.reduction_tensor_symmetry

## Reason

Isolate the tensor-only signed interchange step of the integral delta reduction argument.
The existing theorem is proved by a full mate calculation from this square. No existing
signature, definition, instance, attribute or public import changes.

## Old

The new module and declaration did not exist. The assigned item had one sorry.

## New

New module `Sheaf.SixFunctors.IntegralVerdierReductionTensorSymmetry`:

```lean
theorem reduction_tensor_symmetry
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u})
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheaf l E X D hl))
    (s : SignedSymmetry X (completedIntegralCommRingSheaf l E X D hl) a)
    (hs : ∀ (K L K' L' : Ambient l E X) (f : K ⟶ K') (g : L ⟶ L'),
      a.tensor.map (Prod.mkHom f g) ≫ (s.swap K' L').hom =
        (s.swap K L).hom ≫ a.tensor.map (Prod.mkHom g f))
    (n : ℕ) (m : IntegralHom.ReductionPresentation l E X D hl a n)
    (t : SignedSymmetry X (integralCoefficientCommRingSheaf l E X n) m.target)
    (ht : ∀ (K L K' L' : DerivedCategory (scalarReductionTarget l E X n))
      (f : K ⟶ K') (g : L ⟶ L'),
      m.target.tensor.map (Prod.mkHom f g) ≫ (t.swap K' L').hom =
        (t.swap K L).hom ≫ m.target.tensor.map (Prod.mkHom g f))
    (K L : Ambient l E X) :
    m.mu.inv.app (K, L) ≫
        (scalarReductionDerivedExtension l E X n).map (s.swap K L).hom =
      (t.swap ((scalarReductionDerivedExtension l E X n).obj K)
        ((scalarReductionDerivedExtension l E X n).obj L)).hom ≫ m.mu.inv.app (L, K) := by
  sorry
```

The assigned item imports this module only for its proof. Its existing public theorem
signature is unchanged, and its proof has no sorry. A declaration-scoped
`set_option linter.unusedVariables false in` permits the retained but unnecessary
ambient evaluation hypothesis `he`; it affects lint only and is not exported.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.IntegralVerdierReductionPairingDeltaUncurried | B6 | New proof-only import and application; existing public interface preserved. |

The new module has no pre-existing importers. Existing consumers of the item see the
same declaration, with the same signature and visibility. No forced adaptation is needed.

## Status

landed 20261028T020208-L-2478137 2026-10-28 (merge of deliver/B6/Sheaf.SixFunctors.IntegralVerdierReductionPairingDeltaUncurried)
