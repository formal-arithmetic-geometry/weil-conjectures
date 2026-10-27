# AlgebraicGeometry componentwise normalization helper visibility

## Reason

The returned calculus packet duplicated four existing proved private lemmas in
`Sheaf.AlgebraicGeometry.ReducedAlgebraicNormalizationFieldChange`. Importing their
module does not expose private declarations. Make those existing lemmas public in
that unclaimed Sheaf module and delete all four calculus copies. Their names,
binders, conclusions and proofs stay identical in their owning module; only
visibility changes, with source docstrings added. The calculus uses the shared
lemmas by fully qualified names through its existing private proof import.

## Old

```lean
private theorem finite_normalization {k : Type u} [Field k]
    (X : Scheme.{u}) (q : X ⟶ Spec (.of k))
    [LocallyOfFiniteType q] [QuasiCompact q] :
    IsFinite X.fromReducedNormalization

private theorem normal_normalization (X : Scheme.{u}) (z : X.reducedNormalization) :
    IsDomain (X.reducedNormalization.presheaf.stalk z) ∧
      IsIntegrallyClosed (X.reducedNormalization.presheaf.stalk z)

private theorem component_meets_dense_open (X : Scheme.{u})
    (hfinite : (irreducibleComponents X).Finite) (U : X.Opens) (hU : Dense (U : Set X))
    (Z : irreducibleComponents X) : (Z.1 ∩ (U : Set X)).Nonempty

private theorem dense_preimage_normalization {k : Type u} [Field k]
    (X : Scheme.{u}) (q : X ⟶ Spec (.of k))
    [LocallyOfFiniteType q] [QuasiCompact q]
    (U : X.Opens) (hU : Dense (U : Set X)) :
    Dense (X.fromReducedNormalization ⁻¹ᵁ U : Set X.reducedNormalization)
```

## New

```lean
theorem finite_normalization {k : Type u} [Field k]
    (X : Scheme.{u}) (q : X ⟶ Spec (.of k))
    [LocallyOfFiniteType q] [QuasiCompact q] :
    IsFinite X.fromReducedNormalization

theorem normal_normalization (X : Scheme.{u}) (z : X.reducedNormalization) :
    IsDomain (X.reducedNormalization.presheaf.stalk z) ∧
      IsIntegrallyClosed (X.reducedNormalization.presheaf.stalk z)

theorem component_meets_dense_open (X : Scheme.{u})
    (hfinite : (irreducibleComponents X).Finite) (U : X.Opens) (hU : Dense (U : Set X))
    (Z : irreducibleComponents X) : (Z.1 ∩ (U : Set X)).Nonempty

theorem dense_preimage_normalization {k : Type u} [Field k]
    (X : Scheme.{u}) (q : X ⟶ Spec (.of k))
    [LocallyOfFiniteType q] [QuasiCompact q]
    (U : X.Opens) (hU : Dense (U : Set X)) :
    Dense (X.fromReducedNormalization ⁻¹ᵁ U : Set X.reducedNormalization)
```

## Users

`tools/downstream.py --uses` was run for all four names. Besides the owning module,
only `Sheaf.TraceFormula.ConductorSmoothBaseChange` mentions one of these names;
it declares its own private `normal_normalization`. The consumer compile against
the changed dependency failed at line 138: `a non-private declaration
AlgebraicGeometry.normal_normalization has already been declared`. Remove that
private duplicate and qualify the two existing calls to the shared theorem.
The 93 transitive importers otherwise contain no references to these formerly
private names. No existing public statement or definition changes; only the duplicate private
helper and its two proof call sites are removed/adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ReducedAlgebraicNormalizationFieldChange | unclaimed | Expose the four proved helpers, keeping every proof and signature. |
| Sheaf.AlgebraicGeometry.NormalizedBlowupCalculus | D5 | Remove four duplicate private lemmas and use the existing qualified declarations. |
| Sheaf.TraceFormula.ConductorSmoothBaseChange | unclaimed | Forced by the public-name conflict: delete its private duplicate and use the shared theorem at two proof call sites. Public declarations unchanged. |

The existing normalization node's Lean attachment now lists its four helper
lemmas as well as its main declaration. No new mathematical statement or node,
no sorry, and no target-meaning change is introduced.

## Status

landed 20261023T230629-L-3453249 2026-10-23 (merge of deliver/D5/Sheaf.AlgebraicGeometry.NormalizedBlowupCalculus)
