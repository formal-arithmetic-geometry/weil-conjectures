# Algebra.PopescuLiftPresentation.partial_chart_fibre_dimension

## Reason

The returned chart-flat delivery relied on `partial_chart_fibre_dimension`, which the
upstream sync had commented out along with its corollary `partial_chart_flat`.
Restoring the original proof with its old import reproduces these compiler errors:

```text
Unknown identifier `FormallyEtale`
Unknown identifier `FormallyEtale.of_equiv`
Unknown constant `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`
```

The retired Sheaf wrapper publicly re-exports only the upstream module's public API.
`import all` must name the upstream module itself to obtain the proof dependencies
and its private open-embedding dimension lemma. This delivery restores the two
original proofs in place and repairs that import. The module is unclaimed; this is
an allowed dependency repair, not an adaptation of another group's claimed module.
No definition, active signature, instance, target statement or target meaning changes.

## Old

```lean
import all Sheaf.RingTheory.SmoothAtPrimeDifferentialsDimension
```

The following original declarations were inside the two upstream-sync take-out
comments and hence unavailable to importers. Their signatures are reproduced verbatim:

```lean
theorem partial_chart_fibre_dimension [Algebra R Cbar]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    (d : PopescuLiftPresentation R Cbar π) (hd : d.Prepared)
    (k : Fin d.r) (q : PrimeSpectrum d.liftingAlgebra)
    (hπ : algebraMap R d.liftingAlgebra π ∈ q.asIdeal)
    (hk : ULift.up (Ideal.Quotient.mk d.definingIdeal (d.includeX (d.a k))) ∉ q.asIdeal) :
    let q' := PrimeSpectrum.comap (d.finiteChartEquiv k).toRingHom (d.chartPrime k q)
    let p := PrimeSpectrum.comap (algebraMap R (d.finiteChartAlgebra k)) q'
    topologicalKrullDimAt
      (PrimeSpectrum.preimageEquivFiber R (d.finiteChartAlgebra k) p ⟨q', rfl⟩) =
        (d.n : WithBot ℕ∞)

theorem partial_chart_flat [Algebra R Cbar] [IsNoetherianRing R]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    (d : PopescuLiftPresentation R Cbar π) (hd : d.Prepared)
    (k : Fin d.r) (q : PrimeSpectrum d.liftingAlgebra)
    (hπ : algebraMap R d.liftingAlgebra π ∈ q.asIdeal)
    (hk : ULift.up (Ideal.Quotient.mk d.definingIdeal (d.includeX (d.a k))) ∉ q.asIdeal) :
    Module.Flat R (d.chartLocal k q)
```

The inherited variables are exactly the existing ones in the file, including
`{R : Type a}`, `{Cbar : Type c}`, `{π : R}` and their ring and quotient-algebra instances.

## New

```lean
import all WeilConjectures.RingTheory.SmoothAtPrimeDifferentialsDimension
```

Remove only the two take-out comment delimiters and restore the declarations above
with exactly their original signatures and complete original proofs. The public
imports remain identical. The only proof import replaced is the one shown here.
The existing node's Lean attachment now names both restored theorems.

## Users

`tools/downstream.py Sheaf.RingTheory.PopescuLiftPartialChart --direct --uses
partial_chart_fibre_dimension partial_chart_flat` found one direct importer and no
active textual users of the removed theorems on the base. The existing declarations
of the partial-chart module are unchanged, so transitive users keep their statements.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.PopescuLiftPartialChart | unclaimed | Restore both original proved theorems and fix the proof import. |
| Sheaf.RingTheory.PopescuLiftChartFlat | R4 | Use restored partial_chart_flat in the complete proof; signature unchanged. |
| Sheaf.RingTheory.PopescuLiftChartComparison | unclaimed | Sole existing direct importer; original source compiled unchanged against the repaired module. |
| Sheaf.RingTheory.PopescuLiftSmoothSpecial | unclaimed | Direct consumer of the item; original source compiled unchanged against the repaired item and dependency. |

Both changed files and both unchanged direct consumers compiled together in dependency
order with lcompile.py. No forced consumer adaptation is necessary.

## Status

landed 20261017T003428-L-3317504 2026-10-17 (merge of deliver/R4/Sheaf.RingTheory.PopescuLiftChartFlat)
