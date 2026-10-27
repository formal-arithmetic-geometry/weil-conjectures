# Finite adjunction diagram definition interfaces

## Reason

The main realization theorem combines geometric realization, duality and enriched
adjunction, but all their data types originally live before it in the same module.
New proof modules need those types without importing the theorem that consumes them.
Extract the existing definitions into two public interfaces to avoid that import cycle.
This is a dependency extraction, not a change in mathematical meaning or a selection of
operations from unproved existence. Every non-proof definition body is copied verbatim.
The six remaining proof obligations are separate named public theorems in new modules.

## Old

The original module publicly imports these three interfaces:

```lean
public import Sheaf.SixFunctors.FiniteAdjunctionSystemData
public import Sheaf.SixFunctors.IntegralDualizing
public import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
```

It declares ordinaryCoefficientUnit, coefficientUnit, coefficientUnit_mem, normalizedUnit,
the mapping/dualizing/duality/integral-support interfaces, and the main realization theorem.
The two changed helper proofs originally are:

```lean
theorem coefficientUnit_mem (W : Scheme.{u}) :
    domain l E W (coefficientUnit (l := l) (E := E) W) := by
  sorry

theorem structure_isOver (W : Scheme.{u}) [W.Over (Spec (.of D.k))] :
    (W ↘ Spec (.of D.k)).IsOver (Spec (.of D.k)) := by
  sorry
```

## New

FiniteAdjunctionCoefficientUnitData owns the two concrete degree-zero unit definitions.
FiniteAdjunctionDiagramData owns the remaining pre-theorem declarations. Their names,
parameters, universes, attributes and non-proof bodies are unchanged. The original module retains all three old public imports verbatim and additionally
publicly imports FiniteAdjunctionDiagramData, which publicly imports the two other
original public interfaces and the concrete-unit interface. That interface publicly imports
FiniteAdjunctionSystemData. Every old public prerequisite remains publicly visible.
The main theorem's statement is verbatim and its proof assembles the four new steps.

The helper proofs are now:

```lean
theorem coefficientUnit_mem (W : Scheme.{u}) :
    domain l E W (coefficientUnit (l := l) (E := E) W) := by
  exact ⟨coefficientUnit_normalized W, coefficientUnit_finiteTor W⟩

theorem structure_isOver (W : Scheme.{u}) [W.Over (Spec (.of D.k))] :
    (W ↘ Spec (.of D.k)).IsOver (Spec (.of D.k)) := by
  exact ⟨by simp [specOverSpec_over, Algebra.algebraMap_self]⟩
```

The two coefficient-unit lemmas assert respectively normalization and levelwise finite-Tor
constructibility. The four main steps assert common symmetric calculus, geometric
realization with absolute dualizing objects and integral support, the dual formula on those
already realized operations, and enriched adjunction for the actual internal transpose.
No lemma repackages the full original conclusion. Choice elimination occurs only in the
proof of an existential proposition; no data definition uses an arbitrary unproved witness.

## Users

Read-only `tools/downstream.py` lists these thirteen transitive importers. All thirteen see
the same old declarations through the original public module; none is edited. The only
textual uses of coefficientUnit_mem are in the original module's extracted declarations.
The data extraction does not alter any target statement or the objects those statements use.
All seven unchanged direct importers were compiled against the delivered overlay:
CartesianSectionData, RamifiedScalarSystemTranspose, SystemProjectionFormulaCoherence,
FiniteScalarMateData, IntegralDualExceptionalSystem, IntegralExceptionalMappingAdjunction,
and IntegralExceptionalMappingSystem. All seven passed with no compiler diagnostics.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CartesianSectionAdjointMates | unclaimed in local claim records | Public signatures and definition bodies are reexported unchanged; no adaptation. |
| Sheaf.Paper.CartesianSectionData | unclaimed in local claim records | Public signatures and definition bodies are reexported unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalRefinementMates | unclaimed in local claim records | Public signatures and definition bodies are reexported unchanged; no adaptation. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | unclaimed in local claim records | Public signatures and definition bodies are reexported unchanged; no adaptation. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | unclaimed in local claim records | Public signatures and definition bodies are reexported unchanged; no adaptation. |
| Sheaf.Paper.SystemScalarProjectionIdentification | unclaimed in local claim records | Public signatures and definition bodies are reexported unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateData | unclaimed in local claim records | Public signatures and definition bodies are reexported unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | unclaimed in local claim records | Public signatures and definition bodies are reexported unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralDualExceptionalSystem | unclaimed in local claim records | Public signatures and definition bodies are reexported unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalDescendedCounit | unclaimed in local claim records | Public signatures and definition bodies are reexported unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction | unclaimed in local claim records | Public signatures and definition bodies are reexported unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingSystem | unclaimed in local claim records | Public signatures and definition bodies are reexported unchanged; no adaptation. |
| Sheaf.SixFunctors.RamifiedScalarExceptionalLimit | unclaimed in local claim records | Public signatures and definition bodies are reexported unchanged; no adaptation. |

## Status

landed 20261025T101124-L-3659846 2026-10-25 (merge of deliver/H1/Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization)
