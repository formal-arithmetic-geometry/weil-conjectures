# CompletedPullbackUnitTower.canonicalInverseImageData_existsUnique

## Reason

The delivery proves the existing normalized existence-and-uniqueness theorem. It adds
private helpers inside `section AlgebraicLift`, with explicit small-site variables,
section-scoped elaboration options, and a local instance attribute on three private
Prop-valued adjoint-inference lemmas. These declarations construct the actual lift,
transport its operations, normalize its units, and prove uniqueness.

Preflight's static command audit requires this record because of the new `variable`
and `attribute` commands. Both commands are inside `section AlgebraicLift`, which ends
before the existing public theorem. The instance attribute is explicitly `[local instance]`.
No public signature, public import, existing definition body, or exported instance changes.
Every new declaration is private and proved or explicitly constructed.

## Old

The existing theorem, verbatim:

```lean
theorem canonicalInverseImageData_existsUnique {T' T : Scheme.{t}} (g : T' ⟶ T) :
    letI := proEtaleModelBaseChange_isContinuous g
    ∃! F : ConstantCompletion.InverseImageData (inverse g),
      F.rings = transportedRingInverseImage g ∧
      (∀ O : Sheaf (proEtaleModelTopology T) CommRingCat.{t + 1},
        HEq (F.algebra O).ringUnderlying.hom (ringUnderlyingMap g O) ∧
        HEq (F.algebra O).modules (transportedModuleInverseImage g O) ∧
        ∀ M : ConstantCompletion.Mod O,
          HEq ((adjunction g).homEquiv _ _ ((F.algebra O).moduleUnderlying.inv.app M))
            ((ConstantCompletion.underlying O).map
              ((SheafOfModules.pullbackPushforwardAdjunction.{t + 1}
                (F := proEtaleModelBaseChange g) (J := proEtaleModelTopology T)
                (K := proEtaleModelTopology T')
                (R := siteModuleRings ((transportedRingInverseImage g).obj O))
                (transportedRingUnit g O)).unit.app M))) ∧
      ∀ B : CommRingCat.{t + 1},
        HEq (F.constants.hom.app B) (constantInverseImageMap g B) := by
  sorry
```

## New

The same signature, with a complete proof:

```lean
theorem canonicalInverseImageData_existsUnique {T' T : Scheme.{t}} (g : T' ⟶ T) :
    letI := proEtaleModelBaseChange_isContinuous g
    ∃! F : ConstantCompletion.InverseImageData (inverse g),
      F.rings = transportedRingInverseImage g ∧
      (∀ O : Sheaf (proEtaleModelTopology T) CommRingCat.{t + 1},
        HEq (F.algebra O).ringUnderlying.hom (ringUnderlyingMap g O) ∧
        HEq (F.algebra O).modules (transportedModuleInverseImage g O) ∧
        ∀ M : ConstantCompletion.Mod O,
          HEq ((adjunction g).homEquiv _ _ ((F.algebra O).moduleUnderlying.inv.app M))
            ((ConstantCompletion.underlying O).map
              ((SheafOfModules.pullbackPushforwardAdjunction.{t + 1}
                (F := proEtaleModelBaseChange g) (J := proEtaleModelTopology T)
                (K := proEtaleModelTopology T')
                (R := siteModuleRings ((transportedRingInverseImage g).obj O))
                (transportedRingUnit g O)).unit.app M))) ∧
      ∀ B : CommRingCat.{t + 1},
        HEq (F.constants.hom.app B) (constantInverseImageMap g B) := by
  let := proEtaleModelBaseChange_isContinuous g
  let : (AsSmall.down : proEtaleSiteModel T ⥤ T.ProEt).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{t, t + 1, t + 1} (C := T.ProEt)).inverse.IsEquivalence
  let : (AsSmall.up : T'.ProEt ⥤ proEtaleSiteModel T').IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{t, t + 1, t + 1} (C := T'.ProEt)).functor.IsEquivalence
  let : PreservesFiniteLimits (proEtaleModelBaseChange g) := by
    dsimp only [proEtaleModelBaseChange]
    infer_instance
  let : RepresentablyFlat (proEtaleModelBaseChange g) := modelFlat g
  exact algebraicData_existsUnique (proEtaleModelTopology T)
    (proEtaleModelTopology T') (proEtaleModelBaseChange g)
```

The inserted helper section's commands are scoped by `section AlgebraicLift` and
`end AlgebraicLift`. In particular the following attribute is local to that section:

```lean
attribute [local instance] setPush_rightAdjoint ringPush_rightAdjoint abelianPush_rightAdjoint
```

The private helper declarations and their complete proofs are in the delivered module.
The public theorem uses their specialized normalized existence theorem; the existing
public definition `canonicalInverseImageData` continues to refer only to this public theorem.

## Users

`python3 tools/downstream.py Sheaf.Paper.CompletedPullbackUnitTower --uses
inverse_finiteLimits canonicalInverseImageData_existsUnique` reports zero downstream
Lean modules, and only this module uses the two declarations. The DAG parents and unit
route remain intact; no node or module is withdrawn.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletedPullbackUnitTower | D8 | Two proof bodies completed; all public signatures and existing definitions unchanged; new helper context is private and section-scoped. |

No forced adaptations are necessary.

## Status

landed 20261020T211657-L-3487604 2026-10-20 (merge of deliver/D8/Sheaf.Paper.CompletedPullbackUnitTower)
