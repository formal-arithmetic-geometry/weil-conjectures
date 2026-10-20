# completedIntegralCommRingPresheafUnrestricted

## Reason

The commutative presentation is an objectwise wrapper around the recorded completed
ring sheaf. Comparing it with the underlying ring sheaf made Lean expand the inverse
limit during kernel checking of the completed tensor shift proof. The presheaf wrapper now
uses `abbrev` so the kernel unfolds it before the inverse-limit expression.
No construction, signature, object, morphism, instance or mathematical property changes.

## Old

```lean
noncomputable def completedIntegralCommRingPresheafUnrestricted :
    (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ ⥤ CommRingCat.{max u (t + 1)} where
  obj U := @CommRingCat.of ((completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj U)
    (completedIntegralCoefficientCommRingUnrestricted l E Y U)
  map {U V} f :=
    letI := completedIntegralCoefficientCommRingUnrestricted l E Y U
    letI := completedIntegralCoefficientCommRingUnrestricted l E Y V
    CommRingCat.ofHom ((completedIntegralCoefficientSheafUnrestricted l E Y).obj.map f).hom
  map_id U := (forget₂ CommRingCat RingCat).map_injective
    ((completedIntegralCoefficientSheafUnrestricted l E Y).obj.map_id U)
  map_comp f g := (forget₂ CommRingCat RingCat).map_injective
    ((completedIntegralCoefficientSheafUnrestricted l E Y).obj.map_comp f g)
```


## New

```lean
noncomputable abbrev completedIntegralCommRingPresheafUnrestricted :
    (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ ⥤ CommRingCat.{max u (t + 1)} where
  obj U := @CommRingCat.of ((completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj U)
    (completedIntegralCoefficientCommRingUnrestricted l E Y U)
  map {U V} f :=
    letI := completedIntegralCoefficientCommRingUnrestricted l E Y U
    letI := completedIntegralCoefficientCommRingUnrestricted l E Y V
    CommRingCat.ofHom ((completedIntegralCoefficientSheafUnrestricted l E Y).obj.map f).hom
  map_id U := (forget₂ CommRingCat RingCat).map_injective
    ((completedIntegralCoefficientSheafUnrestricted l E Y).obj.map_id U)
  map_comp f g := (forget₂ CommRingCat RingCat).map_injective
    ((completedIntegralCoefficientSheafUnrestricted l E Y).obj.map_comp f g)
```


The complete signature and body are byte-for-byte unchanged; only this
`def` keyword becomes `abbrev`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletedIntegralCoefficients | unclaimed | Changes only reducibility of the presheaf presentation wrapper. |
| Sheaf.SixFunctors.CompletedTensorFiniteShift | J8, new | Finite tensor tower comparison uses the same coefficients. |
| Sheaf.SixFunctors.CompletedTensorShiftRight | J8 | Kernel comparisons can unfold the presheaf wrapper first. |

All existing consumers retain the identical definitionally equal interfaces.
No forced adaptation is included.

## Status

landed 20261020T230756-L-611403 2026-10-20 (merge of deliver/J8/Sheaf.SixFunctors.CompletedTensorShiftRight)
