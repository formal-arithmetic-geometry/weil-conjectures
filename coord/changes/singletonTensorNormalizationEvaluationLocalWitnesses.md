# singletonTensor_normalization_evaluation proof-local limit witnesses

## Reason

Repair return A from reviewer X-7a434 (head 7a434abbc). The returned local instance
attributes changed the witnesses embedded in the theorem's public type, making the
unchanged direct importer exceed the single-file compile limit. Independent synthesis
inside the proof also causes expensive comparisons through tensor-pullback sections.

## Old

The repository theorem has its unchanged signature and proof `:= by sorry`.
The returned delivery inserted these registrations before that signature:

```lean
set_option linter.auxLemma false in
attribute [local instance] IsSingletonTensorDegreeComparison._proof_1
  IsSingletonTensorDegreeComparison._proof_2
```

## New

Both registrations are removed. The theorem's public signature is elaborated using the
same standard limit instances as the repository. Inside its proof, a small `run_tac`
constructs an explicit transport from the normalization predicate's product witness to
the standard witness, using only `Subsingleton.elim`, `congrArg` and `Eq.mp`.
The subsequent proof-local class lets reuse the predicate's two witnesses when defining
the additive evaluation map. The projection followed by ULift.down gives the map, and
the normalization hypothesis proves its pure-tensor formula.

The linter.auxLemma option is scoped to the theorem solely because the proof refers to
the generated witness names. It changes no instance registration or elaboration behavior.
No public statement, definition, visibility or import changes. Generated witness names
may need updating if the normalization predicate is refactored.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleSingletonTensorNormalizationEvaluation | Q4 | Proof only. |
| Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeKernel | unclaimed | Unchanged source and interface. |

The unchanged importer is compiled against the repaired module in an isolated sandbox
overlay. No forced adaptations or target meaning changes occur.

## Status

landed 20261013T142901-L-499427 2026-10-13 (merge of deliver/Q4/Sheaf.AlgebraicGeometry.EtaleSingletonTensorNormalizationEvaluation)
