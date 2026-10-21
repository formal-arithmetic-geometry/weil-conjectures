# AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerShriek

## Reason

Complete the remaining coefficient-reduction proof and repair the reverted H2
landing while preserving the source module's public interface. The local proof
controls need a review record because the static checker sees attribute commands.

## Old

```lean
theorem nonempty_iso_reductionModIdeal_rightDerivedLowerShriek (J : Ideal Λ) :
    Nonempty (R(f)_![ModuleCat.{u + 1} Λ] ⋙ reductionModIdeal Λ Y J ≅
      reductionModIdeal Λ X J ⋙ R(f)_![ModuleCat.{u + 1} Λ]) :=
  sorry
```

## New

The signature is unchanged and its proof is complete. Two private imports are
added: ConstantTensorProjection and CompactificationUpperShriek in the same derived
etale namespace. The following command is local to elaboration in the namespace:

```lean
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
```

Before the theorem, the following command applies only to that declaration:

```lean
attribute [-instance]
  CompactificationUpperShriek.isLeftAdjoint_rightDerivedLowerStar_of_isProper
  CompactificationUpperShriek.isLeftAdjoint_rightDerivedLowerShriek in
```

The proper adjoint is supplied explicitly in the proof, avoiding recursive global
instance search. It supplies coproduct preservation; the existing
DerivedCategory.isIso_app_singleFunctor_obj then proves the projection comparison
for arbitrary constant modules from its unit case. The compactification comparison
and explicit reduction/tensor isomorphisms finish the proof. The proper adjoint
premise remains admitted and disputed in its original module. No public
attribute, import, signature, data definition or target meaning changes. The finite and upper-star corollaries explicitly transport across
`reductionModIdeal_eq_derivedTensorRight`. The principal lower-star proof applies
the fully proved private `principalIdeal_property` helper to the existing zero-ideal
and nonzero-generator-power comparisons. The principal lower-shriek proof first
types the open comparison with tensor functors, then transports it to reduction.
These proof-only rewrites avoid the kernel timeout caused by repeated unfolding;
all existing theorem signatures and all non-theorem bodies stay verbatim. No downstream adaptation is required by an
interface change.

## Users

The downstream textual declaration-use scan finds only Exchange itself. The
PoincareDuality.Transport mention is documentation only. Other importers receive
exactly the original exported interface. The seven consumers from the repair
record are accounted for in the report.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | H4 | Fill one proof; scoped elaboration only. |

## Status

landed 20261021T203519-L-3803688 2026-10-21 (merge of deliver/H4/WeilConjectures.SixFunctors.Etale.Derived.Exchange)
