# AlgebraicGeometry.coherent_kernel_condition_local_generators

## Reason

The original conclusion left the index universe of `LocalGeneratorsData` unconstrained.
Lean prints the original theorem with independent universe parameters `{u, u_1}`,
so it requests generating data in an arbitrary universe `u_1`, including one smaller
than the site. The Stacks source imposes no such cardinality constraint. The cover
is indexed in `Type u`, and the finite-type predicate itself uses local data indexed
in the site universe `u`. Set the conclusion to `LocalGeneratorsData.{u}`.
This records the intended finite-generators construction; the scheme, hypotheses,
map, rank, and finite-generation conclusion are unchanged. No target signature or
underlying definition changes.

The compiler rejected the constructed witness before this repair:
```
SheafOfModules.finite_generators_of_cover (kernel f) I V hV hlocal
has type Exists.{u + 2} ...
but is expected to have type Exists.{max (u + 2) (u_1 + 2)} ...
```

## Old

```lean
theorem coherent_kernel_condition_local_generators
    (X : Scheme.{u}) (F : X.Modules)
    (I : Type u) (U : I → X.Opens) (hU : ⨆ i, U i = ⊤)
    (hK : ∀ (i : I) (V : (U i).toScheme.Opens) (n : ℕ)
      (f : SheafOfModules.free (R := (U i).toScheme.ringCatSheaf.over V)
        (ULift.{u} (Fin n)) ⟶ ((Scheme.Modules.restrictFunctor (U i).ι).obj F).over V),
      (kernel f).IsFiniteType)
    (W : X.Opens) (n : ℕ)
    (f : SheafOfModules.free (R := X.ringCatSheaf.over W) (ULift.{u} (Fin n)) ⟶
      F.over W) :
    ∃ σ : (kernel f).LocalGeneratorsData, σ.IsFiniteType
```

## New

```lean
theorem coherent_kernel_condition_local_generators
    (X : Scheme.{u}) (F : X.Modules)
    (I : Type u) (U : I → X.Opens) (hU : ⨆ i, U i = ⊤)
    (hK : ∀ (i : I) (V : (U i).toScheme.Opens) (n : ℕ)
      (f : SheafOfModules.free (R := (U i).toScheme.ringCatSheaf.over V)
        (ULift.{u} (Fin n)) ⟶ ((Scheme.Modules.restrictFunctor (U i).ι).obj F).over V),
      (kernel f).IsFiniteType)
    (W : X.Opens) (n : ℕ)
    (f : SheafOfModules.free (R := X.ringCatSheaf.over W) (ULift.{u} (Fin n)) ⟶
      F.over W) :
    ∃ σ : SheafOfModules.LocalGeneratorsData.{u} (kernel f), σ.IsFiniteType
```

## Users

`tools/downstream.py` found 410 transitive importers; declaration-use scanning found
only the item and its immediate caller below. Transitive importers that do not use
this declaration see identical caller signatures. The original caller was copied
unchanged into the sandbox and compiled with the repaired module in the local overlay.
It compiled without errors or warnings; no forced adaptation is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CoherentKernelConditionGluing | K4 | Constructs data in universe u. |
| Sheaf.AlgebraicGeometry.CoherentKernelConditionDescent | unclaimed | Unchanged proof instantiates the data at u; compiled successfully. |

## Status

landed 20261013T011929-L-2763847 2026-10-13 (merge of deliver/K4/Sheaf.AlgebraicGeometry.CoherentKernelConditionGluing)
