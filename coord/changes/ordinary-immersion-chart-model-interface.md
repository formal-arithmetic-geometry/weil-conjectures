# WeilConjectures.OrdinaryImmersionChart model interface

## Reason

The underived exactness and represented-chart lemmas need the same module and
comparison vocabulary as the main theorem. Extract that vocabulary into
Sheaf.Paper.OrdinaryImmersionChartModels and publicly re-export it from the item.
This avoids an import cycle; it is not a file split to evade a compiler timeout.
The ordinary pullback expands the large free-presentation adjunction if Lean unfolds
it while forming the square. Give Rings, pull and adj irreducible boundaries. Rings is written directly as the existing completed ring sheaf, definitionally equal
to forgetting commutativity from its recorded commutative version. Pull and adj retain
the original chosen module pullback and its adjunction.
No source-library file changes.

## Old

```lean
abbrev Rings (T : Scheme.{t}) :=
  (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
      (completedIntegralCommRingSheafUnrestricted l E T)

abbrev pull {T W : Scheme.{t}} (g : T ⟶ W) : Modules l E W ⥤ Modules l E T :=
  letI := SheafOfModules.module_pushforward_isRightAdjoint_of_universes.{t + 1, t, u}
    (directRingMap l E g)
  SheafOfModules.pullback.{max u (t + 1)} (directRingMap l E g)

def adj {T W : Scheme.{t}} (g : T ⟶ W) : pull l E g ⊣ push l E g :=
  letI := SheafOfModules.module_pushforward_isRightAdjoint_of_universes.{t + 1, t, u}
    (directRingMap l E g)
  SheafOfModules.pullbackPushforwardAdjunction (directRingMap l E g)

```

The other seventeen model declarations occur in the original item module. Their
signatures, values and visibility remain verbatim in the extracted Models module.

## New

```lean
@[irreducible]
def Rings (T : Scheme.{t}) : Sheaf (ProEt.topology T) RingCat.{max u (t + 1)} :=
  completedIntegralCoefficientSheafUnrestricted l E T

@[irreducible]
def pull {T W : Scheme.{t}} (g : T ⟶ W) : Modules l E W ⥤ Modules l E T :=
  letI := SheafOfModules.module_pushforward_isRightAdjoint_of_universes.{t + 1, t, u}
    (directRingMap l E g)
  SheafOfModules.pullback.{max u (t + 1)} (directRingMap l E g)

@[irreducible]
def adj {T W : Scheme.{t}} (g : T ⟶ W) : pull l E g ⊣ push l E g := by
  letI := SheafOfModules.module_pushforward_isRightAdjoint_of_universes.{t + 1, t, u}
    (directRingMap l E g)
  unfold pull
  exact SheafOfModules.pullbackPushforwardAdjunction (directRingMap l E g)

```

The main module publicly imports OrdinaryImmersionChartModels. The public qualified
names are unchanged. The three irreducibility attributes hide implementation reduction;
local semireducibility exposes Rings during model construction; the existing adjunction is the API, and explicit unfolding recovers the old values.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.OrdinaryImmersionChartComparison | P1 | Publicly re-exports the extracted definitions; uses their adjunction API. |
| Sheaf.Paper.OrdinaryImmersionChartModels | new, P1 | Houses the original model vocabulary. |
| Sheaf.Paper.OrdinaryCompletedPullbackExact | new, P1 | States only finite-limit preservation of the original pullback. |
| Sheaf.Paper.OrdinaryCompletedChartComparison | new, P1 | States only the underived represented chart square. |

`tools/downstream.py Sheaf.Paper.OrdinaryImmersionChartComparison --uses
WeilConjectures.OrdinaryImmersionChart.adj` reported zero downstream modules and
only the item itself using adj. The corresponding Rings check also reported zero
downstream modules. DAG parents with unfinished proofs still need the
main comparison theorem; none is withdrawn. No target signature changes. The
extracted definitions have the same meaning, including coefficient and scheme
universes, so target semantics are preserved. No modules held by another group
are adapted.

## Status

landed 20261024T190502-L-4070171 2026-10-24 (merge of deliver/P1/Sheaf.Paper.OrdinaryImmersionChartComparison)
