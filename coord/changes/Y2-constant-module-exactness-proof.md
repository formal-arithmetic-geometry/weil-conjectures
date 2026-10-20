# CategoryTheory.siteConstantModuleFunctorGeneral_exact

## Reason

The existing exactness theorem is needed by the coefficient-sized constant-realization
conservativity argument. The module is unclaimed. Its existing proof was `sorry`;
constant presheaves preserve limits and colimits sectionwise, and module sheafification
is exact. This proof completes the declaration without changing any statement,
definition, signature, visibility, import or attribute. No consumer adaptation is needed.

## Old

```lean
theorem siteConstantModuleFunctorGeneral_exact :
    (siteConstantModuleFunctorGeneral J R).Additive ∧
      PreservesFiniteLimits (siteConstantModuleFunctorGeneral J R) ∧
      PreservesFiniteColimits (siteConstantModuleFunctorGeneral J R) := by
  sorry
```

## New

```lean
theorem siteConstantModuleFunctorGeneral_exact :
    (siteConstantModuleFunctorGeneral J R).Additive ∧
      PreservesFiniteLimits (siteConstantModuleFunctorGeneral J R) ∧
      PreservesFiniteColimits (siteConstantModuleFunctorGeneral J R) := by
  let P := siteConstantModulePresheafGeneral (C := C) R
  have : PreservesFiniteLimits P := by
    constructor
    intro K _ _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun X ↦ hc)⟩
  have : PreservesFiniteColimits P := by
    constructor
    intro K _ _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun X ↦ hc)⟩
  let S := PresheafOfModules.sheafification
    (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R)))
  change (P ⋙ S).Additive ∧ PreservesFiniteLimits (P ⋙ S) ∧
    PreservesFiniteColimits (P ⋙ S)
  have : PreservesFiniteLimits (P ⋙ S) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (P ⋙ S) := comp_preservesFiniteColimits _ _
  refine ⟨?_, inferInstance, inferInstance⟩
  apply leftExactFunctor_le_additiveFunctor _ _
  rw [leftExactFunctor_iff]
  infer_instance
```

## Users

`tools/downstream.py Sheaf.CategoryTheory.SiteDerivedConstantModuleFunctor --uses
CategoryTheory.siteConstantModuleFunctorGeneral_exact` lists these six direct users
(236 modules import the module transitively). The theorem has a proposition as its
unchanged type, so replacing its proof cannot affect the meaning or type of a user.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.BoundedConstantChainMapLocal | unclaimed | Identical theorem type; proof completed; no adaptation. |
| Sheaf.CategoryTheory.ConstantRealizationReflectsIsomorphism | unclaimed | Identical theorem type; proof completed; no adaptation. |
| Sheaf.CategoryTheory.PerfectConstantDerivedMapLocal | unclaimed | Identical theorem type; proof completed; no adaptation. |
| Sheaf.CategoryTheory.PerfectConstantLocalChainRepresentative | unclaimed | Identical theorem type; proof completed; no adaptation. |
| Sheaf.CategoryTheory.PerfectConstantLocalNullHomotopy | unclaimed | Identical theorem type; proof completed; no adaptation. |
| Sheaf.CategoryTheory.SiteDerivedConstantModuleFunctor | unclaimed | Identical theorem type; proof completed; no adaptation. |

The new `Sheaf.CategoryTheory.ConstantRealizationReflectsIsomorphismGeneral` is also a
user in this packet and compiles against the completed theorem. Existing public data
and all existing consumers' source text remain verbatim.

## Status

landed 20261020T230849-L-622677 2026-10-20 (merge of deliver/Y2/Sheaf.Paper.WContractibleConstantReductionsML)
