# AlgebraicGeometry.etale_sum_tensor_comparison

## Reason

An arbitrary open immersion need not be quasi-compact. K-flat preservation only
requires the total-tensor projection isomorphism family. The existing canonical
generic construction in this module does not use quasi-compactness, so expose
that proved part as a new theorem. This avoids changing any existing statement
or definition. The source is Stacks Tag 0GKF and the signed direct-sum totalization
calculation already implemented by the module's private `totalTensorIso`.

A proved private generic `totalTensor_exists` groups the existing construction
and its five clauses before specializing the original full theorem. This proof
refactoring preserves its canonical component, both homotopy laws and descent.

## Old

There was no public declaration `etale_sum_tensor_comparison`. The only complete
public totalization interface included quasi-compactness:

```lean
theorem etale_sum_tensor_totalization
    (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (u : U ⟶ X) (hu : Etale u)
    [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u] :
    ∃ Ψ : EtaleSumTensorComparison A u hu,
      EtaleSumPreservesDirectSums A u hu ∧ EtaleSumTensorClauses A u hu Ψ
```

## New

Every existing public signature and defining body is preserved verbatim. The
existing full theorem keeps the same signature, all hypotheses and all clauses.
The additional proved interface is:

```lean
theorem etale_sum_tensor_comparison
    (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (u : U ⟶ X) (hu : Etale u)
    [IsSeparated u] [LocallyOfFiniteType u] :
    Nonempty (TotalTensorComparison
      (curriedTensor (EtaleModuleSheaf U A)) (curriedTensor (EtaleModuleSheaf X A))
      (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) u hu)
      (Etale.upperStar (ModuleCat.{u + 1} A) u))
```

It returns the already constructed family of comparison isomorphisms and adds no
choice-based definition. Its proof invokes the actual total-complex constructor
with the natural canonical sheaf projection isomorphism and coproduct preservation.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.EtaleSumTensorTotalization | unclaimed | Adds the proved comparison-family API; factors the existing proof through a proved private helper. |
| Sheaf.AlgebraicGeometry.EtaleSumTensorTestProjection | unclaimed | Existing signatures, definitions and theorem remain identical; no edits. |
| Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility | N3 | Existing public interface preserved; no edits to this held module. |
| Sheaf.SixFunctors.EtaleOpenKFlat | new, K3 | Uses the new proved comparison family for an arbitrary open immersion. |

The import graph and downstream name searches identify the two existing direct
consumers above. The new declaration is used only by the delivered K-flat module.
No consumer adaptation and no target statement review is required: the existing
definitions and statements retain exactly the same mathematical meaning.

## Status

landed 20261020T233153-L-902140 2026-10-20 (merge of deliver/K3/Sheaf.SixFunctors.EtaleOpenTensor)
