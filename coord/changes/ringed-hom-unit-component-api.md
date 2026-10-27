# CategoryTheory.ringedHomUnitEvaluationIso

## Reason

Repeatedly expanding the concrete unit-evaluation isomorphism exposes the large
single-functor and Hom-projection construction. Add its specified component equation
as a proved API, together with its naturality consequence. A named proof of the
existing small-site sheaf-composition property
caches that instance locally in this module and in RingedKoszulSystem. All existing
definition bodies, signatures, reducibility attributes and imports are retained.
The new component statement requires the public HomComplexComponents import.
No adopted-source module is changed. The original evaluation construction and the
meaning of all target statements are unchanged. These two modules are unclaimed.

## Old

```lean
def ringedHomUnitEvaluationIso (M : ringedSiteComplex O) :
    homComplex (R := O) (ringedSiteRingComplex O) M ≅ M :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ @asIso _ _ _ _ (homComplexUnitEvaluation J O M n)
      (homComplex_unit_evaluation_isIso J O M n))
    (fun n m h ↦ homComplex_unit_evaluation_comm J O M n m h)
```

## New

```lean
/-- The forgetful functor preserves the sheaf condition on a small site.
Source: Mathlib, `CategoryTheory.Sites.Whiskering`.
(blueprint: def-weil-pbc-ringed-completion-unit).
Proof: use the existing instance; the named proof prevents repeated instance search
through the concrete sheaf category in the completion constructions. -/
theorem ringedCompletionHasSheafCompose {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) :
    J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) := by infer_instance

attribute [local instance 20000] ringedCompletionHasSheafCompose

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u})
variable [HasDerivedCategory.{w} (SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]

/-- Evaluation at one gives the canonical chain isomorphism from Hom of the ring complex.
Source: Stacks Project, sites-cohomology.tex, Section 08J7
(blueprint: def-weil-pbc-ringed-completion-unit). -/
def ringedHomUnitEvaluationIso (M : ringedSiteComplex O) :
    homComplex (R := O) (ringedSiteRingComplex O) M ≅ M :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ @asIso _ _ _ _ (homComplexUnitEvaluation J O M n)
      (homComplex_unit_evaluation_isIso J O M n))
    (fun n m h ↦ homComplex_unit_evaluation_comm J O M n m h)

section
omit [HasDerivedCategory.{w} (SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]

set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] homComplexFunctor

/-- The specified component of the canonical evaluation isomorphism.
Source: Stacks Project, sites-cohomology.tex, Section 08J7.
(blueprint: def-weil-pbc-ringed-completion-unit).
Proof: expose the isomorphism of components; its forward map is the specified
unit evaluation, independently of the inverse used by `asIso`. -/
theorem ringedHomUnitEvaluationIso_hom_f (M : ringedSiteComplex O) (n : ℤ) :
    (ringedHomUnitEvaluationIso O M).hom.f n = homComplexUnitEvaluation J O M n := by
  unfold ringedHomUnitEvaluationIso
  rfl

/-- Unit evaluation projects to source degree zero and evaluates at one.
Source: Stacks Project, sites-cohomology.tex, Section 08J7.
(blueprint: def-weil-pbc-ringed-completion-unit).
Proof: expose the specified component, then the definition of unit evaluation.
The preferred single functor and the ordinary single complex have identical underlying
functors. Thus their specified projections and degree-zero identifications agree. -/
theorem ringedHomUnitEvaluationIso_hom_f_projection (M : ringedSiteComplex O) (n : ℤ) :
    (ringedHomUnitEvaluationIso O M).hom.f n =
      homComplexπ (ringedSiteRingComplex O) M n 0 n (zero_add n) ≫
        SheafOfModules.homObjMap (R := O)
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0
            (SheafOfModules.unit
              ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))).inv (𝟙 _) ≫
          (SheafOfModules.homObjUnitIso (R := O) (M.X n)).hom := by
  unfold ringedHomUnitEvaluationIso homComplexUnitEvaluation
  rfl

/-- Canonical unit evaluation is natural in the target complex.
Source: Stacks Project, sites-cohomology.tex, Section 08J7.
(blueprint: def-weil-pbc-ringed-completion-unit).
Proof: compare chain maps degreewise, expose their specified evaluation components,
and apply naturality of degreewise evaluation at one. -/
theorem ringedHomUnitEvaluationIso_naturality {M N : ringedSiteComplex O} (f : M ⟶ N) :
    ((homComplexFunctor (R := O)).obj (op (ringedSiteRingComplex O))).map f ≫
        (ringedHomUnitEvaluationIso O N).hom =
      (ringedHomUnitEvaluationIso O M).hom ≫ f := by
  apply HomologicalComplex.hom_ext
  intro n
  change (((homComplexFunctor (R := O)).obj
      (op (ringedSiteRingComplex O))).map f).f n ≫
        (ringedHomUnitEvaluationIso O N).hom.f n =
      (ringedHomUnitEvaluationIso O M).hom.f n ≫ f.f n
  erw [ringedHomUnitEvaluationIso_hom_f O N n, ringedHomUnitEvaluationIso_hom_f O M n]
  exact homComplex_unit_evaluation_naturality J O f n

end
```

RingedKoszulSystem additionally installs the existing named proof:

```lean
attribute [local instance 20000] ringedCompletionHasSheafCompose
```

## Users

The textual users of ringedHomUnitEvaluationIso are listed below. The original
isomorphism remains reducible, so consumers that compile retain their proofs. The flat equivalence consumer exceeded
the limit (87.2 s); its private naturality proof uses the new API, and its final
unit calculation applies Iso.eq_comp_inv without substituting the large inverse.
Its elaboration is serialized with Elab.async false to avoid concurrent reductions;
this scheduling option leaves kernel checking and the mathematical interface unchanged.
The four new singleton comparison modules also use the instance proof; the endpoint
module uses the component equation. Consumer checks are recorded in report.md.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.CategoryTheory.RingedCechKoszulHomLimitComparison` | unclaimed | Local instance cache and proved naturality API; original took 63.4 s, adaptation passed in 25.0 s. |
| `Sheaf.CategoryTheory.RingedCompletionUnit` | unclaimed | Named instance proof and proved component API; 25.7 s. |
| `Sheaf.CategoryTheory.RingedHomTensorUnitNormalization` | unclaimed | Unchanged. |
| `Sheaf.CategoryTheory.RingedKoszulColimitHomOrdinaryLimit` | unclaimed | Unchanged. |
| `Sheaf.CategoryTheory.RingedKoszulFiniteEvaluation` | unclaimed | Unchanged. |
| `Sheaf.CategoryTheory.RingedKoszulSystem` | unclaimed | Install the named proof locally; 23.2 s. |
| `Sheaf.CategoryTheory.RingedNegativeKoszulFactorHomTensor` | unclaimed | Unchanged. |
| `Sheaf.CategoryTheory.RingedNegativeKoszulTransitions` | unclaimed | Unchanged. |
| `Sheaf.Paper.CoefficientHomAugmentation` | unclaimed | Unchanged. |
| `Sheaf.Paper.CoefficientHomUnit` | E6 | Unchanged. |
| `Sheaf.Paper.ExtendedCechCompletionModel` | unclaimed | Unchanged. |
| `Sheaf.Paper.ExtendedCechReflectorCore` | unclaimed | Unchanged. |
| `Sheaf.Paper.FlatRingedIdealCompleteEquivalence` | unclaimed | Local instance cache and proved naturality API in private proofs; signatures unchanged; compile accepted (61.0 s reported elapsed). |

## Status

landed 20261026T092722-L-3459472 2026-10-26 (merge of deliver/T9/Sheaf.Paper.PrincipalKoszulDualTowerComparison)
