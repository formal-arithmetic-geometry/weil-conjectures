# Algebra-diagram normalization interface

## Reason

Return C-98383 reconciliation: preserve M4's current
`AlgebraDiagramOrdinaryComparisons` file and
`lem-pur-algebra-diagram-ordinary-comparisons` node unchanged. Put A5's evaluation
comparison construction in `AlgebraDiagramEvaluationOrdinaryComparisons` under the
separate `lem-pur-algebra-diagram-normalized-ordinary-comparisons` node. Update the
coherence module to import the new evaluation module. Its declarations retain their
existing signatures. M4's current consumers need no change because neither their
module nor its dependencies are modified.

Move the concrete interface into a publicly reexported definition module so ordinary
comparison construction and coherence of already constructed derived comparisons can
be stated independently without cyclic imports. The original item retains its theorem
and public import surface. The original unmodified module compiled in about 47 seconds. Diagnostics of the
expanded proof identified repeated unfolding of the constant sheaf (a chosen
sheafification left adjoint) and repeated concrete abelian instance terms. Ordinary definitions for the constant ring and total scalar restriction,
a cached canonical abelian instance, and explicit local constant-slice localization
bindings avoid that unfolding. The new coherence helper binds the already-proved constant-evaluation exactness
properties explicitly, and the main theorem supplies these proofs. This avoids
trying to infer the presentation from a constant evaluation that forgets it. Their values and all original normalization equations
are preserved. No target statement is changed.

## Old

The declarations originally lived in
`Sheaf.CategoryTheory.AlgebraDiagramEvaluationAdjunctionNormalization`.

```lean
abbrev algebraDiagramConstantRing
```

```lean
abbrev rX := SheafOfModules.restrictScalars.{u} p.aX
```

```lean
abbrev rY := SheafOfModules.restrictScalars.{u} p.aY
```

```lean
def EvaluationAdjunctionNormalization : Prop :=
  letI : ∀ j : J, (p.eAX j).Additive := p.eAX_additive
  letI : ∀ j : J, (p.eAY j).Additive := p.eAY_additive
  letI : ∀ j : J, PreservesFiniteLimits (p.eAX j) := p.eAX_limits
  letI : ∀ j : J, PreservesFiniteLimits (p.eAY j) := p.eAY_limits
  letI : ∀ j : J, PreservesFiniteColimits (p.eAX j) := p.eAX_colimits
  letI : ∀ j : J, PreservesFiniteColimits (p.eAY j) := p.eAY_colimits
    ∃ (c : p.fB.modules ⋙ p.rY ≅ p.rX ⋙ p.fA.modules)
      (d : p.PB ⋙ p.rY.mapDerivedCategory ≅ p.rX.mapDerivedCategory ⋙ p.PA)
      (cB : ∀ j : J, p.fB.modules ⋙ p.eBY j ≅ p.eBX j ⋙
              (p.fj j).modules)
      (cA : ∀ j : J, p.fA.modules ⋙ p.eAY j ≅ p.eAX j ⋙ p.s.modules)
      (lambda0 : ∀ j : J, p.pullB ⋙ p.eBX j ≅ p.eBY j ⋙ p.pullj j)
      (beta : ∀ j : J, p.PB ⋙ (p.eBY j).mapDerivedCategory ≅
        (p.eBX j).mapDerivedCategory ⋙ p.Pj j)
      (delta : ∀ j : J, p.PA ⋙ (p.eAY j).mapDerivedCategory ≅
        (p.eAX j).mapDerivedCategory ⋙ p.P)
      (cj : ∀ j : J, (p.fj j).modules ⋙ p.rYj j ≅ p.rXj j ⋙ p.s.modules)
      (dj : ∀ j : J, p.Pj j ⋙ (p.rYj j).mapDerivedCategory ≅
        (p.rXj j).mapDerivedCategory ⋙
              p.P),
      AlgebraDiagramOrdinaryRestrictionNormalized p.aX p.aY p.fB p.fA
        (p.directB.trans p.directA.symm) c ∧
      AlgebraDiagramDerivedSquareNormalized p.fB.modules p.fA.modules p.rX p.rY c d ∧
      (∀ j : J,
        AlgebraDiagramOrdinaryEvaluationNormalized p.s.direct p.fB j (p.fj j)
          p.directB (p.directLevel j) (cB j) ∧
        AlgebraDiagramOrdinaryEvaluationNormalized p.s.direct p.fA j p.s
          p.directA rfl (cA j) ∧
        AlgebraDiagramOrdinaryRestrictionNormalized
          (algebraDiagramCoefficientAt p.aX j) (algebraDiagramCoefficientAt p.aY j)
          (p.fj j) p.s (p.directLevel j) (cj j) ∧
        AlgebraDiagramDerivedSquareNormalized p.fB.modules (p.fj j).modules
          (p.eBX j) (p.eBY j) (cB j) (beta j) ∧
        AlgebraDiagramDerivedSquareNormalized p.fA.modules p.s.modules
          (p.eAX j) (p.eAY j) (cA j) (delta j) ∧
        AlgebraDiagramDerivedSquareNormalized (p.fj j).modules p.s.modules
          (p.rXj j) (p.rYj j) (cj j) (dj j) ∧
        (∀ N : ringedSiteModules.{u} p.BX,
          (p.eBX j).map (p.moduleAdjB.counit.app N) =
            (lambda0 j).hom.app (p.fB.modules.obj N) ≫
              (p.pullj j).map ((cB j).hom.app N) ≫
              (p.moduleAdjj j).counit.app ((p.eBX j).obj N)) ∧
        (∀ N : DerivedCategory (ringedSiteModules.{u} p.BX),
          (p.eBX j).mapDerivedCategory.map (p.adjDB.counit.app N) =
            (Functor.mapDerivedCategorySquareIso (lambda0 j)).hom.app (p.PB.obj N) ≫
              (p.Gj j).map ((beta j).hom.app N) ≫
              (p.adjDj j).counit.app ((p.eBX j).mapDerivedCategory.obj N)) ∧
        (∀ (M : DerivedCategory (ringedSiteModules.{u} p.BY))
          (N : DerivedCategory (ringedSiteModules.{u} p.BX)) (t : M ⟶ p.PB.obj N),
          ((p.adjDj j).homEquiv ((p.eBY j).mapDerivedCategory.obj M)
            ((p.eBX j).mapDerivedCategory.obj N)).symm
              ((p.eBY j).mapDerivedCategory.map t ≫ (beta j).hom.app N) =
            (Functor.mapDerivedCategorySquareIso (lambda0 j)).inv.app M ≫
              (p.eBX j).mapDerivedCategory.map ((p.adjDB.homEquiv M N).symm t)) ∧
        (∀ N : DerivedCategory (ringedSiteModules.{u} p.BX),
          (p.eAY j).mapDerivedCategory.map (d.hom.app N) ≫
              (delta j).hom.app (p.rX.mapDerivedCategory.obj N) ≫
              p.P.map
                ((Functor.mapDerivedCategorySquareIso
                  (algebraDiagramRestrictionEvaluation p.aX j)).hom.app N) =
            (Functor.mapDerivedCategorySquareIso
                (algebraDiagramRestrictionEvaluation p.aY j)).hom.app (p.PB.obj N) ≫
              (p.rYj j).mapDerivedCategory.map ((beta j).hom.app N) ≫
              (dj j).hom.app ((p.eBX j).mapDerivedCategory.obj N))) ∧
      (∀ (j k : J) (a : j ⟶ k),
        ∃ (ca : (p.fj k).modules ⋙
              (SheafOfModules.restrictScalars.{u} (algebraDiagramRingArrow p.BY a)) ≅
            (SheafOfModules.restrictScalars.{u} (algebraDiagramRingArrow p.BX a)) ⋙
              (p.fj j).modules)
          (qa : p.Pj k ⋙
              (SheafOfModules.restrictScalars.{u}
                (algebraDiagramRingArrow p.BY a)).mapDerivedCategory ≅
            (SheafOfModules.restrictScalars.{u}
              (algebraDiagramRingArrow p.BX a)).mapDerivedCategory ⋙
              p.Pj j),
          AlgebraDiagramOrdinaryRestrictionNormalized
            (algebraDiagramRingArrow p.BX a) (algebraDiagramRingArrow p.BY a)
            (p.fj k) (p.fj j) (p.directLevel k |>.trans (p.directLevel j).symm) ca ∧
          AlgebraDiagramDerivedSquareNormalized (p.fj k).modules (p.fj j).modules
            (SheafOfModules.restrictScalars.{u} (algebraDiagramRingArrow p.BX a))
            (SheafOfModules.restrictScalars.{u} (algebraDiagramRingArrow p.BY a)) ca qa ∧
          ∀ N : DerivedCategory (ringedSiteModules.{u} p.BX),
            (algebraDiagramDerivedTransition p.BY a).app (p.PB.obj N) ≫
                (SheafOfModules.restrictScalars.{u}
                  (algebraDiagramRingArrow p.BY a)).mapDerivedCategory.map
                  ((beta k).hom.app N) ≫
                qa.hom.app ((p.eBX k).mapDerivedCategory.obj N) =
              (beta j).hom.app N ≫
                (p.Pj j).map ((algebraDiagramDerivedTransition p.BX a).app N)) ∧
      (∀ (j k : J) (a : j ⟶ k),
        ∃ (ca : p.s.modules ⋙
              (SheafOfModules.restrictScalars.{u} (algebraDiagramRingArrow p.AY a)) ≅
            (SheafOfModules.restrictScalars.{u} (algebraDiagramRingArrow p.AX a)) ⋙ p.s.modules)
          (qa : p.P ⋙
              (SheafOfModules.restrictScalars.{u}
                (algebraDiagramRingArrow p.AY a)).mapDerivedCategory ≅
            (SheafOfModules.restrictScalars.{u}
              (algebraDiagramRingArrow p.AX a)).mapDerivedCategory ⋙
              p.P),
          AlgebraDiagramOrdinaryRestrictionNormalized
            (algebraDiagramRingArrow p.AX a) (algebraDiagramRingArrow p.AY a)
            p.s p.s rfl ca ∧
          AlgebraDiagramDerivedSquareNormalized p.s.modules p.s.modules
            (SheafOfModules.restrictScalars.{u} (algebraDiagramRingArrow p.AX a))
            (SheafOfModules.restrictScalars.{u} (algebraDiagramRingArrow p.AY a)) ca qa ∧
          ∀ N : DerivedCategory (ringedSiteModules.{u} p.AX),
            (algebraDiagramDerivedTransition p.AY a).app (p.PA.obj N) ≫
                (SheafOfModules.restrictScalars.{u}
                  (algebraDiagramRingArrow p.AY a)).mapDerivedCategory.map
                  ((delta k).hom.app N) ≫
                qa.hom.app ((p.eAX k).mapDerivedCategory.obj N) =
              (delta j).hom.app N ≫
                p.P.map ((algebraDiagramDerivedTransition p.AX a).app N))

```

## New

The interface lives in `Sheaf.CategoryTheory.AlgebraDiagramEvaluationAdjunctionNormalizationDefs`
and is publicly reexported by the original module.

```lean
def algebraDiagramConstantRing
```

```lean
def rX : ringedSiteModules.{u} p.BX ⥤ ringedSiteModules.{u} p.AX :=
  SheafOfModules.restrictScalars.{u} p.aX
```

```lean
def rY : ringedSiteModules.{u} p.BY ⥤ ringedSiteModules.{u} p.AY :=
  SheafOfModules.restrictScalars.{u} p.aY
```

```lean
def EvaluationAdjunctionNormalization : Prop :=
  letI : ∀ j : J, HasDerivedCategory.{w}
      (ringedSiteModules.{u} (algebraDiagramRingAt p.AX j)) :=
    fun j ↦ algebraDiagramConstantDerivedAt (algebraDiagramConstantRing K A) j
  letI : ∀ j : J, HasDerivedCategory.{w}
      (ringedSiteModules.{u} (algebraDiagramRingAt p.AY j)) :=
    fun j ↦ algebraDiagramConstantDerivedAt (algebraDiagramConstantRing L A) j
  letI : ∀ j : J, (p.eAX j).Additive := p.eAX_additive
  letI : ∀ j : J, (p.eAY j).Additive := p.eAY_additive
  letI : ∀ j : J, PreservesFiniteLimits (p.eAX j) := p.eAX_limits
  letI : ∀ j : J, PreservesFiniteLimits (p.eAY j) := p.eAY_limits
  letI : ∀ j : J, PreservesFiniteColimits (p.eAX j) := p.eAX_colimits
  letI : ∀ j : J, PreservesFiniteColimits (p.eAY j) := p.eAY_colimits
    ∃ (c : p.fB.modules ⋙ p.rY ≅ p.rX ⋙ p.fA.modules)
      (d : p.PB ⋙ p.rY.mapDerivedCategory ≅ p.rX.mapDerivedCategory ⋙ p.PA)
      (cB : ∀ j : J, p.fB.modules ⋙ p.eBY j ≅ p.eBX j ⋙
              (p.fj j).modules)
      (cA : ∀ j : J, p.fA.modules ⋙ p.eAY j ≅ p.eAX j ⋙ p.s.modules)
      (lambda0 : ∀ j : J, p.pullB ⋙ p.eBX j ≅ p.eBY j ⋙ p.pullj j)
      (beta : ∀ j : J, p.PB ⋙ (p.eBY j).mapDerivedCategory ≅
        (p.eBX j).mapDerivedCategory ⋙ p.Pj j)
      (delta : ∀ j : J, p.PA ⋙ (p.eAY j).mapDerivedCategory ≅
        (p.eAX j).mapDerivedCategory ⋙ p.P)
      (cj : ∀ j : J, (p.fj j).modules ⋙ p.rYj j ≅ p.rXj j ⋙ p.s.modules)
      (dj : ∀ j : J, p.Pj j ⋙ (p.rYj j).mapDerivedCategory ≅
        (p.rXj j).mapDerivedCategory ⋙
              p.P),
      AlgebraDiagramOrdinaryRestrictionNormalized p.aX p.aY p.fB p.fA
        (p.directB.trans p.directA.symm) c ∧
      AlgebraDiagramDerivedSquareNormalized p.fB.modules p.fA.modules p.rX p.rY c d ∧
      (∀ j : J,
        AlgebraDiagramOrdinaryEvaluationNormalized p.s.direct p.fB j (p.fj j)
          p.directB (p.directLevel j) (cB j) ∧
        AlgebraDiagramOrdinaryEvaluationNormalized p.s.direct p.fA j p.s
          p.directA rfl (cA j) ∧
        AlgebraDiagramOrdinaryRestrictionNormalized
          (algebraDiagramCoefficientAt p.aX j) (algebraDiagramCoefficientAt p.aY j)
          (p.fj j) p.s (p.directLevel j) (cj j) ∧
        AlgebraDiagramDerivedSquareNormalized p.fB.modules (p.fj j).modules
          (p.eBX j) (p.eBY j) (cB j) (beta j) ∧
        AlgebraDiagramDerivedSquareNormalized p.fA.modules p.s.modules
          (p.eAX j) (p.eAY j) (cA j) (delta j) ∧
        AlgebraDiagramDerivedSquareNormalized (p.fj j).modules p.s.modules
          (p.rXj j) (p.rYj j) (cj j) (dj j) ∧
        (∀ N : ringedSiteModules.{u} p.BX,
          (p.eBX j).map (p.moduleAdjB.counit.app N) =
            (lambda0 j).hom.app (p.fB.modules.obj N) ≫
              (p.pullj j).map ((cB j).hom.app N) ≫
              (p.moduleAdjj j).counit.app ((p.eBX j).obj N)) ∧
        (∀ N : DerivedCategory (ringedSiteModules.{u} p.BX),
          (p.eBX j).mapDerivedCategory.map (p.adjDB.counit.app N) =
            (Functor.mapDerivedCategorySquareIso (lambda0 j)).hom.app (p.PB.obj N) ≫
              (p.Gj j).map ((beta j).hom.app N) ≫
              (p.adjDj j).counit.app ((p.eBX j).mapDerivedCategory.obj N)) ∧
        (∀ (M : DerivedCategory (ringedSiteModules.{u} p.BY))
          (N : DerivedCategory (ringedSiteModules.{u} p.BX)) (t : M ⟶ p.PB.obj N),
          ((p.adjDj j).homEquiv ((p.eBY j).mapDerivedCategory.obj M)
            ((p.eBX j).mapDerivedCategory.obj N)).symm
              ((p.eBY j).mapDerivedCategory.map t ≫ (beta j).hom.app N) =
            (Functor.mapDerivedCategorySquareIso (lambda0 j)).inv.app M ≫
              (p.eBX j).mapDerivedCategory.map ((p.adjDB.homEquiv M N).symm t)) ∧
        (∀ N : DerivedCategory (ringedSiteModules.{u} p.BX),
          (p.eAY j).mapDerivedCategory.map (d.hom.app N) ≫
              (delta j).hom.app (p.rX.mapDerivedCategory.obj N) ≫
              p.P.map
                ((Functor.mapDerivedCategorySquareIso
                  (algebraDiagramRestrictionEvaluation p.aX j)).hom.app N) =
            (Functor.mapDerivedCategorySquareIso
                (algebraDiagramRestrictionEvaluation p.aY j)).hom.app (p.PB.obj N) ≫
              (p.rYj j).mapDerivedCategory.map ((beta j).hom.app N) ≫
              (dj j).hom.app ((p.eBX j).mapDerivedCategory.obj N))) ∧
      (∀ (j k : J) (a : j ⟶ k),
        ∃ (ca : (p.fj k).modules ⋙
              (SheafOfModules.restrictScalars.{u} (algebraDiagramRingArrow p.BY a)) ≅
            (SheafOfModules.restrictScalars.{u} (algebraDiagramRingArrow p.BX a)) ⋙
              (p.fj j).modules)
          (qa : p.Pj k ⋙
              (SheafOfModules.restrictScalars.{u}
                (algebraDiagramRingArrow p.BY a)).mapDerivedCategory ≅
            (SheafOfModules.restrictScalars.{u}
              (algebraDiagramRingArrow p.BX a)).mapDerivedCategory ⋙
              p.Pj j),
          AlgebraDiagramOrdinaryRestrictionNormalized
            (algebraDiagramRingArrow p.BX a) (algebraDiagramRingArrow p.BY a)
            (p.fj k) (p.fj j) (p.directLevel k |>.trans (p.directLevel j).symm) ca ∧
          AlgebraDiagramDerivedSquareNormalized (p.fj k).modules (p.fj j).modules
            (SheafOfModules.restrictScalars.{u} (algebraDiagramRingArrow p.BX a))
            (SheafOfModules.restrictScalars.{u} (algebraDiagramRingArrow p.BY a)) ca qa ∧
          ∀ N : DerivedCategory (ringedSiteModules.{u} p.BX),
            (algebraDiagramDerivedTransition p.BY a).app (p.PB.obj N) ≫
                (SheafOfModules.restrictScalars.{u}
                  (algebraDiagramRingArrow p.BY a)).mapDerivedCategory.map
                  ((beta k).hom.app N) ≫
                qa.hom.app ((p.eBX k).mapDerivedCategory.obj N) =
              (beta j).hom.app N ≫
                (p.Pj j).map ((algebraDiagramDerivedTransition p.BX a).app N)) ∧
      (∀ (j k : J) (a : j ⟶ k),
        ∃ (ca : p.s.modules ⋙
              (SheafOfModules.restrictScalars.{u} (algebraDiagramRingArrow p.AY a)) ≅
            (SheafOfModules.restrictScalars.{u} (algebraDiagramRingArrow p.AX a)) ⋙ p.s.modules)
          (qa : p.P ⋙
              (SheafOfModules.restrictScalars.{u}
                (algebraDiagramRingArrow p.AY a)).mapDerivedCategory ≅
            (SheafOfModules.restrictScalars.{u}
              (algebraDiagramRingArrow p.AX a)).mapDerivedCategory ⋙
              p.P),
          AlgebraDiagramOrdinaryRestrictionNormalized
            (algebraDiagramRingArrow p.AX a) (algebraDiagramRingArrow p.AY a)
            p.s p.s rfl ca ∧
          AlgebraDiagramDerivedSquareNormalized p.s.modules p.s.modules
            (SheafOfModules.restrictScalars.{u} (algebraDiagramRingArrow p.AX a))
            (SheafOfModules.restrictScalars.{u} (algebraDiagramRingArrow p.AY a)) ca qa ∧
          ∀ N : DerivedCategory (ringedSiteModules.{u} p.AX),
            (algebraDiagramDerivedTransition p.AY a).app (p.PA.obj N) ≫
                (SheafOfModules.restrictScalars.{u}
                  (algebraDiagramRingArrow p.AY a)).mapDerivedCategory.map
                  ((delta k).hom.app N) ≫
                qa.hom.app ((p.eAX k).mapDerivedCategory.obj N) =
              (delta j).hom.app N ≫
                p.P.map ((algebraDiagramDerivedTransition p.AX a).app N))

```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.AlgebraDiagramEvaluationAdjunctionNormalization | A5 | Reexports definitions and assembles the same proposition. |
| Sheaf.CategoryTheory.AlgebraDiagramEvaluationOrdinaryComparisons | A5, new | Constructs evaluation comparisons using the interface. |
| Sheaf.CategoryTheory.AlgebraDiagramDerivedComparisonCoherence | A5, new | Uses ordinary comparisons and the interface for coherence equations. |
| Sheaf.CategoryTheory.AlgebraDiagramComparisonTools | A5, new | Private derived-comparison helpers use the interface. |

`tools/downstream.py` reports zero downstream modules and only the item using
`EvaluationAdjunctionNormalization`. The unfinished DAG parents are retained.
The cached abelian structure retains the canonical preadditive data and caches only
proposition-valued fields; no category data or localization is replaced.
No WeilConjectures source file is modified.

## Status

landed 20261025T122446-L-1774038 2026-10-25 (merge of deliver/A5/Sheaf.CategoryTheory.AlgebraDiagramEvaluationAdjunctionNormalization)
