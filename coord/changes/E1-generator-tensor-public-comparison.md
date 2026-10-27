# LocallyClosedGeneratorTensorIntersection public tensor comparison

## Reason

Restore the quarantined item and repair the upstream-sync overload failure at
line 839 recorded in `coord/rework.tsv`. A private helper name formerly imported
from the source Grothendieck module is no longer an unambiguous API. The existing
public comparison in `CategoryTheory.Mod.ResidueOrdinary` has the same functor
source and target and is proved by the balanced tensor coequalizer construction.
This repair changes a proof import, a private theorem body and the final
proof's reuse of its comparison-existence witness. Every public
signature, definition body, attribute and public import is retained verbatim.

## Old

```lean
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
```

In the private theorem `lisse_flat`:

```lean
  exact preservesFiniteLimits_of_natIso
    (Mod.relativeTensorRightIso P ≪≫
      (BraidedCategory.tensorLeftIsoTensorRight P).symm)
```

## New

```lean
import Sheaf.Paper.IntegralResidueOrdinaryMonoidal
```

In the same private theorem:

```lean
  exact preservesFiniteLimits_of_natIso
    (Mod.ResidueOrdinary.relativeTensorRightIso P ≪≫
      (BraidedCategory.tensorLeftIsoTensorRight P).symm)
```

The full archive is restored with the import and private-body repair above.
The comparison transports the finite-limit preservation of `Mod.tensorLeft P` first
to monoidal right tensor, then to monoidal left tensor via the braiding. It
therefore proves the original flatness assertion without any change of statement.
The final theorem also reuses its comparison-existence proof instead of
elaborating it twice. Its old proof body was:

```lean
  obtain ⟨e, _⟩ := actual_generator_comparison_exists Λ a b (derivedTensor Λ X)
    (generatorIntersectionModule Λ a b) (derivedTensor_eq_curriedTensor Λ X)
    (generatorIntersectionModule_eq_tensor Λ a b)
  have hp := actual_tensor_properties Λ a b (derivedTensor Λ X) (fun A B C ↦ ⟨e A B C⟩)
  have hn := And.intro (actual_generator_comparison_exists Λ a b (derivedTensor Λ X)
    (generatorIntersectionModule Λ a b) (derivedTensor_eq_curriedTensor Λ X)
    (generatorIntersectionModule_eq_tensor Λ a b)) hp
  simp only [generatorTensorSource, generatorTensorTarget, actualTensorSource,
    actualTensorTarget, functorComp_assoc] at hn ⊢
  exact hn
```

The new proof body is:

```lean
  have h := actual_generator_comparison_exists Λ a b (derivedTensor Λ X)
    (generatorIntersectionModule Λ a b) (derivedTensor_eq_curriedTensor Λ X)
    (generatorIntersectionModule_eq_tensor Λ a b)
  obtain ⟨e, _⟩ := id h
  have hp := actual_tensor_properties Λ a b (derivedTensor Λ X) (fun A B C ↦ ⟨e A B C⟩)
  have hn := And.intro h hp
  simp only [generatorTensorSource, generatorTensorTarget, actualTensorSource,
    actualTensorTarget, functorComp_assoc] at hn ⊢
  exact hn
```

`id h` retains `h` in the local context while extracting its witness. This is the
same mathematical argument and requires no DAG route change. The initial
revision compiled in 58.0 seconds, but its delivery compile hit the 60-second
limit. Profiling showed expensive derived-comparison type checking; eliminating
the repeated comparison-existence application gives a clean final compile in
35.8 seconds. No time limit was raised, no file was split, and the delivered
file contains no profiler or reduced-heartbeat options.

## Users

`tools/downstream.py Sheaf.SixFunctors.LocallyClosedGeneratorTensorIntersection
--allow-missing --uses GeneratorFactorization generatorExtension
generatorRestriction generatorTensorSource generatorIntersectionModule
generatorTensorTarget locallyClosedGeneratorTensorIntersection` reports zero
current downstream modules and zero users for every declaration. An exact import
scan of `lean/Sheaf`, `lean/WeilConjectures` and `quarantine` also finds no importers.
The DAG parent `lem-sfb-admissible-tensor-constructibility` continues to need this
item and is unaffected. No consumer adaptation is necessary.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.LocallyClosedGeneratorTensorIntersection | E1 | Restore archived proof; repair the private flatness proof using the public tensor comparison. |

## Status

landed 20261022T113916-L-393969 2026-10-22 (merge of deliver/E1/Sheaf.SixFunctors.LocallyClosedGeneratorTensorIntersection)
