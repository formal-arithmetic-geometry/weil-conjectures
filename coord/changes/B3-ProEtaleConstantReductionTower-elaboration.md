# AlgebraicGeometry.Scheme.OrderedExchange local elaboration boundaries

## Reason

Filling `reduction_exists` makes its chosen derived functor and universal counit
large expressions. Later comparison definitions can repeatedly unfold nested
chosen functors, natural isomorphisms and mates during elaboration. Add file-local
irreducibility attributes after the relevant definitions to bound this work.
No declaration type or definition body changes, and the attributes do not escape
the file. The preflight's static command comparison requested this record.

## Old

The following definitions had their ordinary transparency during the rest of the
file. Their definitions, reproduced verbatim below, remain unchanged.


```lean
def reduction (T : Scheme.{t}) : D (A := A) T ⥤ TD (A := A) T := (reduction_exists d T).choose
```

```lean
def reductionCounit (T : Scheme.{t}) :
    DerivedCategory.Qh ⋙ reduction d T ⟶ reductionHomotopy d T :=
  (reduction_exists d T).choose_spec.choose
```

```lean
def ordinaryReductionPullInv (n : ℕ) :
    proEtaleRingModulePullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
        (exchangeConstantIso f A) ⋙ proEtaleRingExtension (quotient d U n) ⟶
      proEtaleRingExtension (quotient d V n) ⋙
        proEtaleRingModulePullback f (d.finiteRing V n) (d.finiteRing U n)
          (d.finiteRingIso f n) :=
  (mateEquiv (proEtaleRingExtensionAdjunction (quotient d V n))
    (proEtaleRingExtensionAdjunction (quotient d U n))).symm
      (proEtaleRingRestrictionPullbackInv f (exchangeConstantRing V A) (d.finiteRing V n)
        (exchangeConstantRing U A) (d.finiteRing U n) (quotient d V n) (quotient d U n)
          (exchangeConstantIso f A) (d.finiteRingIso f n) (quotient_comm d f n))
```

```lean
def levelPullIso (n : ℕ) :
    level d V n ⋙
        proEtaleRingModulePullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
          (exchangeConstantIso f A) ≅
      proEtaleRingModulePullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
        (exchangeConstantIso f A) ⋙ level d U n :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (proEtaleRingExtension (quotient d V n))
      (@asIso _ _ _ _ (proEtaleRingRestrictionPullbackInv f
        (exchangeConstantRing V A) (d.finiteRing V n) (exchangeConstantRing U A) (d.finiteRing U n)
        (quotient d V n) (quotient d U n) (exchangeConstantIso f A)
        (d.finiteRingIso f n) (quotient_comm d f n))
        (proEtaleRingRestrictionPullbackInv_isIso f
          (exchangeConstantRing V A) (d.finiteRing V n)
          (exchangeConstantRing U A) (d.finiteRing U n)
          (quotient d V n) (quotient d U n) (exchangeConstantIso f A)
          (d.finiteRingIso f n) (quotient_comm d f n))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (ordinaryReductionPullInv d f n)).symm
      (proEtaleRingRestrictScalars (quotient d U n)) ≪≫
    Functor.associator _ _ _
```

```lean
def ordinaryReductionPullIso :
    reductionModule d V ⋙ exchangeTowerModulePull f (exchangeConstantRing V A)
          (exchangeConstantRing U A) (exchangeConstantIso f A) ≅
      proEtaleRingModulePullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
        (exchangeConstantIso f A) ⋙ reductionModule d U :=
  NatIso.ofComponents
    (fun M ↦ NatIso.ofComponents
      (fun n ↦ (levelPullIso d f n.unop).app M)
      (fun a ↦ levelPullIso_transition d f M a))
    (fun a ↦ by
      apply NatTrans.ext
      funext n
      exact (levelPullIso d f n.unop).hom.naturality a)

set_option linter.defProp false in
```

```lean
def ReductionPullNormalized
    (τ : reduction d V ⋙ exchangeConstantPull (A := A) f ≅
        pull (A := A) f ⋙ reduction d U) : Prop :=
  ∀ P : CochainComplex (reductionModules V (exchangeConstantRing V A)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients (R := exchangeConstantRing V A) P →
        τ.hom.app (DerivedCategory.Q.obj P) ≫
            (reduction d U).map
              ((proEtaleRingDerivedPullbackFactors f
                (exchangeConstantRing V A) (exchangeConstantRing U A)
                (exchangeConstantIso f A)).hom.app P) ≫
            reductionComplexCounit d U
              (((proEtaleRingModulePullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
                (exchangeConstantIso f A)).mapHomologicalComplex (.up ℤ)).obj P) =
          (exchangeConstantPull (A := A) f).map (reductionComplexCounit d V P) ≫
            (exchangeTowerModulePull f (exchangeConstantRing V A)
          (exchangeConstantRing U A) (exchangeConstantIso f A)).mapDerivedCategoryFactors.hom.app
              (((reductionModule d V).mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex (ordinaryReductionPullIso d f)
                (.up ℤ)).hom.app P)
```

```lean
def reductionPullIso :
    reduction d V ⋙ exchangeConstantPull (A := A) f ≅
      pull (A := A) f ⋙ reduction d U :=
  (reductionPullIso_existsUnique d f).choose
```

```lean
def projection (K : D (A := A) U) :
    (reduction d V).obj ((push (A := A) f).obj K) ⟶
      (exchangeConstantPush (A := A) f).obj ((reduction d U).obj K) :=
  (exchangeTowerAdjunction f (exchangeConstantRing V A) (exchangeConstantRing U A)
    (exchangeConstantIso f A)).homEquiv _ _
      ((reductionPullIso d f).hom.app ((push (A := A) f).obj K) ≫
        (reduction d U).map ((proEtaleRingDerivedAdjunction f (exchangeConstantRing V A)
          (exchangeConstantRing U A) (exchangeConstantIso f A)).counit.app K))
```

```lean
def diagonalPullIso :
    diagonal (A := A) V ⋙ exchangeConstantPull (A := A) f ≅
      pull (A := A) f ⋙ diagonal (A := A) U :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (ordinaryDiagonalPullIso (A := A) f) ≪≫
      Functor.mapDerivedCategoryCompIso _ _
```

```lean
def directLimitIso :
    rlim (A := A) U ⋙ push (A := A) f ≅
      exchangeConstantPush (A := A) f ⋙ rlim (A := A) V :=
  conjugateIsoEquiv
    ((proEtaleRingDerivedAdjunction f (exchangeConstantRing V A) (exchangeConstantRing U A)
      (exchangeConstantIso f A)).comp (diagonalAdjunction (A := A) U))
    ((diagonalAdjunction (A := A) V).comp
      (exchangeTowerAdjunction f (exchangeConstantRing V A) (exchangeConstantRing U A)
        (exchangeConstantIso f A))) (diagonalPullIso (A := A) f)
```

```lean
def reconstruction (K : D (A := A) V) :
    (completePull d f).obj K ≅
      (rlim (A := A) U).obj ((exchangeConstantPull (A := A) f).obj ((reduction d V).obj K)) :=
  (rlim (A := A) U).mapIso ((reductionPullIso d f).symm.app K)

variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}
```

```lean
def H (K : D (A := A) X) :
    (reduction d Y').obj ((pull (A := A) g).obj ((push (A := A) f).obj K)) ≅
      (exchangeConstantPull (A := A) g).obj
        ((exchangeConstantPush (A := A) f).obj ((reduction d X).obj K)) :=
  (reductionPullIso d g).symm.app _ ≪≫
    (exchangeConstantPull (A := A) g).mapIso (asIso (projection d f K))
```

## New

The same definitions and signatures above, with each command below placed after
the definitions it names. Only the remainder of this file sees these attributes.

```lean

attribute [local irreducible] reduction reductionCounit

attribute [local irreducible] ordinaryReductionPullInv

attribute [local irreducible] levelPullIso

attribute [local irreducible] ordinaryReductionPullIso

attribute [local irreducible] ReductionPullNormalized

attribute [local irreducible] reductionPullIso

attribute [local irreducible] projection

attribute [local irreducible] diagonalPullIso

attribute [local irreducible] directLimitIso

attribute [local irreducible] reconstruction

attribute [local irreducible] H

```

## Users

`tools/downstream.py Sheaf.Paper.ProEtaleConstantReductionTower --uses ...`
reports two live downstream modules. Its last-segment name search over-approximates
uses (the consumers also use generic interface declarations of the same names).
Both consumers compile unchanged. The quarantined importers are recorded too;
their source remains preserved and no signatures or global attributes change.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.ProEtaleConstantReductionTower` | B3 | Local elaboration only; three theorem proofs filled. |
| `Sheaf.Paper.CompletedProjectionCoherence` | D2 | None; unchanged source compiles. |
| `Sheaf.Paper.CompletedPullbackUnitTower` | V1 | None; unchanged source compiles. |
| `Sheaf.Paper.OrderedExchangeCoefficientComparison` | unclaimed | Quarantined; no interface change. |
| `Sheaf.Paper.ExchangeFunctoriality` | unclaimed | Quarantined; no interface change. |
| `Sheaf.Paper.SfCbcCompactSupportCompositionLimit` | unclaimed | Quarantined; no interface change. |
| `Sheaf.Paper.CompletedExchangeCoherence` | S9 | Quarantined; no interface change. |
| `Sheaf.Paper.SfCbcExtensionZeroCompletion` | unclaimed | Quarantined; no interface change. |

No target meaning is changed and no forced adaptations are included.

## Status

landed 20261021T002119-L-1487313 2026-10-21 (merge of deliver/B3/Sheaf.Paper.ProEtaleConstantReductionTower)
