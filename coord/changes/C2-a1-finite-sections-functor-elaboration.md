# A1 finite-sections functor elaboration

## Reason

Restore the source preserved by the timeout rework entry for
`Sheaf.Paper.A1FiniteWeilSectionsDecomposition`. The archived module eagerly
expands its four functor abbreviations while inferring the module structures
used by the nested direct sums, especially the Qbar stalks. The profiler trace
shows non-easy whnf of `a1FiniteStalkFunctor` and its object and additive-group
projections during statement elaboration. With file-wide transparency disabled,
these checks expand the underlying derived pullback and coefficient cohomology.

Make these four functors ordinary definitions with explicit source and target
categories, keeping each construction body verbatim. Restore normal transparency
for this module. This retains definitional equality with the old constructions
but stops eager abbreviation expansion during typeclass search. Remove seven
unused private imports. All public imports, theorem signatures, evaluation maps,
Frobenius maps and the two existing theorem holes are preserved.

The unmodified archive compiled in 24.5 seconds against the current published
build (the historical failure was a 60-second timeout). The repaired complete
module compiled cleanly in 12.8 seconds, with the existing 60-second limit.
The profiling probes are scratch files and are not part of this delivery.

## Old

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev a1FiniteCohomologyFunctor :=
  sfWeilForget D c.l c.different Z₀ E.val ⋙
    frobeniusCohomologyRationalFunctor D c.l c.different E.val Z₀
      (Compactification.ofIsProper Z₀.hom) true ⋙
    DerivedCategory.coefficientFdCohomology E.val 0

abbrev a1FiniteStalkFunctor (z : Spec (.of D.k) ⟶ (D.geometricFiber Z₀).left) :=
  letI := frobeniusPointPrimeInvertible D c.l c.different
  letI := sfWeilPrimeInvertible D c.l c.different Z₀
  sfWeilForget D c.l c.different Z₀ E.val ⋙
    rationalDerivedPullback c.l E.val z ⋙ pointRationalFibre D c.l c.different E.val ⋙
    DerivedCategory.coefficientFdCohomology E.val 0

abbrev a1FiniteQbarCohomologyFunctor :=
  a1FiniteCohomologyFunctor D c Z₀ E ⋙ a1FiniteExtend D c E

abbrev a1FiniteQbarStalkFunctor
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Z₀).left) :=
  a1FiniteStalkFunctor D c Z₀ E z ⋙ a1FiniteExtend D c E
```

The seven private imports removed are listed in the delivery report.

## New

```lean
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

def a1FiniteCohomologyFunctor :
    sfWeilComplex D c.l c.different Z₀ E.val ⥤ ModuleCat.{u} E.val :=
  sfWeilForget D c.l c.different Z₀ E.val ⋙
    frobeniusCohomologyRationalFunctor D c.l c.different E.val Z₀
      (Compactification.ofIsProper Z₀.hom) true ⋙
    DerivedCategory.coefficientFdCohomology E.val 0

def a1FiniteStalkFunctor (z : Spec (.of D.k) ⟶ (D.geometricFiber Z₀).left) :
    sfWeilComplex D c.l c.different Z₀ E.val ⥤ ModuleCat.{u} E.val :=
  letI := frobeniusPointPrimeInvertible D c.l c.different
  letI := sfWeilPrimeInvertible D c.l c.different Z₀
  sfWeilForget D c.l c.different Z₀ E.val ⋙
    rationalDerivedPullback c.l E.val z ⋙ pointRationalFibre D c.l c.different E.val ⋙
    DerivedCategory.coefficientFdCohomology E.val 0

def a1FiniteQbarCohomologyFunctor :
    sfWeilComplex D c.l c.different Z₀ E.val ⥤ ModuleCat.{u} c.Qbar :=
  a1FiniteCohomologyFunctor D c Z₀ E ⋙ a1FiniteExtend D c E

def a1FiniteQbarStalkFunctor
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Z₀).left) :
    sfWeilComplex D c.l c.different Z₀ E.val ⥤ ModuleCat.{u} c.Qbar :=
  a1FiniteStalkFunctor D c Z₀ E z ⋙ a1FiniteExtend D c E
```

## Users

`tools/downstream.py` reports the item unknown because its live source is
quarantined. Therefore the reverse import closure was computed from both
`lean/` and `quarantine/`, giving the complete table below. The three direct
quarantined consumers were read in full: FiniteMapPurity,
FiniteBoundaryWeights and FiniteCompactificationStalkReturn. They import this
module for their intended proofs but do not yet mention any of the changed
functor names in their Lean declarations or proof bodies. No consumer requires
adaptation. The dependent DAG nodes and the unit route are retained.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | C2 | Restored with typed functor definitions and reduced elaboration. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Identical mathematical interface; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Direct quarantined importer; no changed-name use. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Identical mathematical interface; no adaptation. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Direct quarantined importer; no changed-name use. |
| Sheaf.Paper.FiniteCompactificationEigenvalues | unclaimed | Identical mathematical interface; no adaptation. |
| Sheaf.Paper.FiniteCompactificationStalkReturn | unclaimed | Direct quarantined importer; no changed-name use. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Identical mathematical interface; no adaptation. |

No target meaning changes: the four construction bodies are unchanged, so
ordinary delta reduction identifies the old and new functors, including their
object maps and morphism maps. Only their reducibility hints and explicit type
annotations change.

## Status

landed 20261024T184709-L-3113391 2026-10-24 (merge of deliver/C2/Sheaf.Paper.A1FiniteWeilSectionsDecomposition)
