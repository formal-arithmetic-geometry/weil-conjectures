# Historical reproductions

This file records the first reproduction step. Times are wall-clock measurements from the
historical diagnostic runs; a value marked `>` was terminated at the stated limit. The
historical sources are preserved by commit id, so the snippets below are the exact source
forms used by the declarations.

## Environment

| Case | Baseline commit | Control commit | Lean | Mathlib |
| --- | --- | --- | --- | --- |
| Slow Derived Tensor | `bdab171985a` | `428569e1ce1` | `leanprover/lean4:v4.33.1` | `0df444a360eaa60ab8c11dca51a86af692955474` |
| Derived-Completion Cone | `9ba4d01f55c` (inline source) | `fe5f5d78f1c` (named diagram) | `leanprover/lean4:v4.33.1` | `0df444a360eaa60ab8c11dca51a86af692955474` |

The target modules were the imported module itself in each case. Runs used the repository
options `backward.isDefEq.respectTransparency=false` and `maxSynthPendingDepth=3`; diagnostic
runs used `debug.skipKernelTC` only as an isolation control. `sorry` runs are diagnostic and
are not counted as successful proofs.

## A: Slow Derived Tensor

The baseline consumer is the instance in `WeilConjectures/SixFunctors/Etale/Derived/Tensor.lean`:

```lean
instance isLeftDerivedFunctor₂_derivedTensor :
    -⊗ᴸ-(X)[A].IsLeftDerivedFunctor₂
      (Functor.LaxMonoidal.μNatTrans DerivedCategory.Qh)
      (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology A) (ComplexShape.up ℤ))
      (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology A) (ComplexShape.up ℤ)) :=
  DerivedCategory.isLeftDerivedFunctor₂CurriedTensor
    (Sheaf X.smallEtaleTopology A)
```

In the baseline, `HasLeftDerivedFunctor₂` and `IsLeftDerivedFunctor₂` are `abbrev`s in
`LeftDerivedTwo.lean` (and the analogous arities three and four are also `abbrev`s). The
control commit changes those six declarations, with the same bodies, to ordinary
`@[reducible] def`s.

| Probe | `Kernel.check(value)` | `isDefEq` inferred -> declared | reverse | Result |
| --- | ---: | ---: | ---: | --- |
| `test_tensorObj_kernelProbe` | 1 ms | 49,867 ms | 50,279 ms | succeeds |
| `isLeftDerivedFunctor₂_derivedTensor_kernelProbe` | 1 ms | 131,963 ms | 121,742 ms | succeeds |
| control declaration after `@[reducible] def` change | fast (seconds including imports) | fast (seconds including imports) | fast | succeeds |

The first two rows are direct kernel probes from commit `195ac97d078`, run against the
same v4.33.1/mathlib environment. The control row is the successful `428569e1ce1` module
build; its source change is only the six declaration-kind changes above. This is the
historical reproduction of the disproportionate conversion cost: checking the value is
essentially free, while converting the inferred and written types is not.

## B: Derived-Completion Cone

The failing baseline declaration is exactly:

```lean
noncomputable def DerivedCategory.derivedCompletionCone
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    Cone (DerivedCategory.quotPowFunctor J I ⋙ tensorLeft K) :=
  sorry
```

The successful source introduces the named diagram and states the cone over it:

```lean
noncomputable def DerivedCategory.derivedCompletionDiagram
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    ℕᵒᵖ ⥤ DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) :=
  DerivedCategory.quotPowFunctor J I ⋙ tensorLeft K

noncomputable def DerivedCategory.derivedCompletionCone
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    Cone (DerivedCategory.derivedCompletionDiagram J I K) :=
  ((tensorLeft K).mapCone (DerivedCategory.quotPowCone J I)).extend (ρ_ K).inv
```

| Declaration | Elaboration / skip-kernel control | `Kernel.check(type)` | `Kernel.check(value)` | Final conversion |
| --- | ---: | ---: | ---: | ---: |
| inline `:= sorry` | 17.7 s with kernel skipped | 3 ms | 3 ms | `>600 s`, terminated |
| inline real value | finite elaboration | 3 ms | 3 ms | `>7 min`, terminated |
| named diagram `:= sorry` | 17 s | fast | fast | approximately free |
| named diagram, real value and remaining API | 9.5 s | fast | fast | completes |

The inline result is the requested timeout reproduction even though the value is `sorry`.
The source report records 36 minimal inferred/declaration differences, all proof positions,
after `abstractNestedProofs`; those proposition types contain the concrete derived-category
`MonoidalCategory` instance. The named diagram keeps that instance expression in a body and
out of the declared cone type.

## Reproduction conclusion

Both cases reproduce on the historical toolchain. A is a successful-vs-slow conversion
change at a family of derived-functor heads. B is a timeout in the final declaration
conversion, isolated by `sorry`, and disappears when the indexing diagram is named.
