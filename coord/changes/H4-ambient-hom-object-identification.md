# WeilConjectures.AdicQbarRealization.AmbientHomEvaluation.gammaH

## Reason

Profiling found repeated comparison of the full unique-existence predicate while
checking `eqToIso` in `gammaH` (about five seconds in this definition alone).
Use a proved object-equality lemma with the actual functor object in its type,
and keep the chosen common-stage Hom functor locally irreducible. This changes
only the proof argument of `eqToIso`: proof irrelevance makes its value equal to
the old value. No object, scalar comparison, signature, exported attribute, instance, or target
meaning changes. Existing public imports are retained; the new support module is
publicly imported because the object-equality theorem occurs in the public
definition body. All ten generic proof calculations
are housed in the new support module to avoid elaborating them again in the item.

## Old

```lean
/-- The finite-stage H comparison uses exactly the prescribed rational Hom scalar map.
The first equality merely exposes the unchanged literal object of the chosen functor.
Source: DAG step 7; commonStageHomComparison of the recorded operations
(blueprint: lem-sf-adic-ambient-hom-evaluation-comparison). -/
def gammaH (P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory)
    (F : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (h : (commonStageHomObject l (PadicAlgCl l) X P).stage ≤ F) :
    (ordinary l X R).obj ((commonStageDerivedInternalHom l (PadicAlgCl l) X).obj P) ≅
      finiteH l X R P F h :=
  (ordinary l X R).mapIso
    (eqToIso ((commonStageDerivedInternalHom_existsUnique l (PadicAlgCl l)
        X).exists.choose_spec.1 P) ≪≫
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).isoToStage
        (commonStageHomObject l (PadicAlgCl l) X P) h ≪≫
      (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := X) F).mapIso
          (commonStageHomComparison l (PadicAlgCl l) X P F h))
```

## New

```lean
/-- The finite-stage H comparison uses exactly the prescribed rational Hom scalar map.
The first equality merely exposes the unchanged literal object of the chosen functor.
Source: DAG step 7; commonStageHomComparison of the recorded operations
(blueprint: lem-sf-adic-ambient-hom-evaluation-comparison). -/
def gammaH (P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory)
    (F : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (h : (commonStageHomObject l (PadicAlgCl l) X P).stage ≤ F) :
    (ordinary l X R).obj ((commonStageDerivedInternalHom l (PadicAlgCl l) X).obj P) ≅
      finiteH l X R P F h :=
  (ordinary l X R).mapIso
    (eqToIso (commonStageDerivedInternalHom_obj_eq l (PadicAlgCl l) X P) ≪≫
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).isoToStage
        (commonStageHomObject l (PadicAlgCl l) X P) h ≪≫
      (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := X) F).mapIso
          (commonStageHomComparison l (PadicAlgCl l) X P F h))
```

The supporting `commonStageDerivedInternalHom_obj_eq` theorem is proved directly
from the existing defining unique-existence theorem; it adds no hole.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.AdicAmbientHomEvaluationComparison` | H4 | Owner; the equality proof in gammaH and the corresponding local source iso use the proved API. |
| `Sheaf.Paper.AdicQbarConstructibleRealization` | unclaimed in current shared records | Sole direct importer; public names and values are preserved, no source adaptation expected. |

The downstream query lists 138 import descendants but only the owner directly
mentions the fully qualified gammaH name. Only the sole direct importer needs
a compatibility compile; no class or instance is changed.

The repository has no other textual users of the four old private evaluation
helpers, which are now provided by the proved CoherenceCalculus API.

The unchanged direct importer compiled against the delivered dependencies in
15.4 seconds. Its temporary sandbox copy was removed after the check.

## Status

landed 20261028T072417-L-1944104 2026-10-28 (merge of deliver/H4/Sheaf.Paper.AdicAmbientHomEvaluationComparison)
