# WeilConjectures.SemilinearSections.OpenSystems.restrictionSections

## Reason

The old OpenSystems interface permitted an independently chosen natural automorphism of
restrictionEvaluation at each finite coefficient level. Twisting extensionEvaluation by
the inverse mate preserves unit_evaluation and counit_evaluation, so those equations do
not enforce compatibility of restrictionEvaluation with strict quotient transitions.

For the identity open with l = 3, use the ordinary coefficient ring module tower and
identity coefficient transports. Twist restrictionEvaluation by +1 at level 0 and -1
at level 1 (and choose extensionEvaluation by the corresponding inverse mate). The
ordinaryRestrictionQuotient formula forces the inverse twists as the finite components
of f. These do not commute with reduction modulo 3. Thus the old interface admits data
for which the item statement is false. This is an interface normalization error, not a
reason to replace the theorem by a weaker assertion.

Add the actual same-section law already proved by openRestrictionEvaluationSections.
The two constructors of OpenSystems use precisely this comparison, so their existing
proofs supply the new field. No existing field, binder, or universe changes. File-local irreducibility keeps the
selected ordinary tensor evaluation abstract.
A proved private inverse and its triangle identity are reused in the existing
uniqueness proof to reduce repeated checking of the large concrete term. These
changes export no attributes and preserve every explicitly written declaration signature.
The Data declaration locally disables generation of injectivity and size lemmas: its
large generated machinery otherwise dominates compilation. Existing module imports and
all explicitly declared Data fields remain verbatim; direct importers are compiled to
check that none uses the omitted generated lemmas. This is
proof data specifying the already intended restriction map, not arbitrary chosen data.
The unclaimed direct consumer SemilinearTensorReductionCochain originally exceeded
60 seconds against the repaired interface (64 seconds). Its local
ordinaryEvaluationTensor unfolding control keeps the chosen unique comparison abstract
except where its section property is used; that proof unfolds it explicitly. This
exports no attribute and changes no consumer signature.
No Challenge target signature changes. Targets using the changed interface require the
usual renewed statement review; the concrete intended restriction construction is the
same. The definition node records the correction and all 67 DAG citers.

## Old

```lean
structure OpenSystems where
  /-- Actual extension by zero, determined up to unique adjunction-compatible iso. -/
  extension : Systems.{max c v, v, max c v r} (J.over U)
      (openRings.{c, v, r} J B U) (openTransitions.{c, v, r} J B τ U) ⥤ Systems.{c, v, max c v r}
        J B τ
  /-- Its universal property against the constructed restriction. -/
  ordinaryAdjunction : extension ⊣ openRestriction.{c, v, r} J B τ U
  /-- Extension is additive. -/
  [extensionAdditive : extension.Additive]
  /-- Extension is left exact. -/
  [extensionLimits : PreservesFiniteLimits extension]
  /-- Extension is right exact. -/
  [extensionColimits : PreservesFiniteColimits extension]
  /-- Levelwise actual direct-sum/sheafification extension. -/
  extensionEvaluation : ∀ n : ℕ,
    extension ⋙ evaluation.{c, v, max c v r} J B τ n ≅
      evaluation.{max c v, v, max c v r} (J.over U)
        (openRings.{c, v, r} J B U) (openTransitions.{c, v, r} J B τ U) n ⋙
          (@SheafOfModules.localizedSystemExtension.{c, v, r} C _ J
            (abelianSheafify.{c, v, max c v r} J)
            (locallyBijective.{c, v, max c v r} J) (B n) U)
  /-- Levelwise actual slice restriction. -/
  restrictionEvaluation : ∀ n : ℕ,
    openRestriction.{c, v, r} J B τ U ⋙ evaluation.{max c v, v, max c v r} (J.over U)
        (openRings.{c, v, r} J B U) (openTransitions.{c, v, r} J B τ U) n ≅
      evaluation.{c, v, max c v r} J B τ n ⋙
        SheafOfModules.localizedSystemRestriction.{c, v, r} (B n) U
  /-- Unit evaluation is the actual level unit, whose formula is the summand injection. -/
  unit_evaluation : ∀ (n : ℕ)
    (M : Systems.{max c v, v, max c v r} (J.over U)
      (openRings.{c, v, r} J B U) (openTransitions.{c, v, r} J B τ U)),
    (evaluation.{max c v, v, max c v r} (J.over U)
      (openRings.{c, v, r} J B U) (openTransitions.{c, v, r} J B τ U) n).map
        (ordinaryAdjunction.unit.app M) ≫
        (restrictionEvaluation n).hom.app (extension.obj M) ≫
        (SheafOfModules.localizedSystemRestriction.{c, v, r} (B n) U).map
          ((extensionEvaluation n).hom.app M) =
      ((@SheafOfModules.localizedSystemAdjunction.{c, v, r} C _ J
            (abelianSheafify.{c, v, max c v r} J)
            (locallyBijective.{c, v, max c v r} J) (B n) U)).unit.app
        ((evaluation.{max c v, v, max c v r} (J.over U)
          (openRings.{c, v, r} J B U) (openTransitions.{c, v, r} J B τ U) n).obj M)
  /-- Counit evaluation is the actual level counit. -/
  counit_evaluation : ∀ (n : ℕ) (N : Systems.{c, v, max c v r} J B τ),
    ((@SheafOfModules.localizedSystemExtension.{c, v, r} C _ J
            (abelianSheafify.{c, v, max c v r} J)
            (locallyBijective.{c, v, max c v r} J) (B n) U)).map
        ((restrictionEvaluation n).hom.app N) ≫
        ((@SheafOfModules.localizedSystemAdjunction.{c, v, r} C _ J
            (abelianSheafify.{c, v, max c v r} J)
            (locallyBijective.{c, v, max c v r} J) (B n) U)).counit.app
          ((evaluation.{c, v, max c v r} J B τ n).obj N) =
      (extensionEvaluation n).inv.app ((openRestriction.{c, v, r} J B τ U).obj N) ≫
        (evaluation.{c, v, max c v r} J B τ n).map (ordinaryAdjunction.counit.app N)
  /-- Ordinary unbounded derived j-shriek adjoint to derived j-star. -/
  adjunction : extension.mapDerivedCategory ⊣ (openRestriction.{c, v, r} J B τ U).mapDerivedCategory

  /-- The derived adjunction is exactly the localized ordinary Hom equivalence. -/
  transpose_model : ∀
    (P : CochainComplex (Systems.{max c v, v, max c v r} (J.over U)
      (openRings.{c, v, r} J B U) (openTransitions.{c, v, r} J B τ U)) ℤ)
    (Q : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ)
    (f : (extension.mapHomologicalComplex (.up ℤ)).obj P ⟶ Q),
    ((adjunction.homEquiv _ _)
      ((Functor.mapDerivedCategoryFactors extension).hom.app P ≫ DerivedCategory.Q.map f)) ≫
        (Functor.mapDerivedCategoryFactors (openRestriction.{c, v, r} J B τ U)).hom.app Q =
      DerivedCategory.Q.map
        (((ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv P Q) f)

```

## New

```lean
structure OpenSystems where
  /-- Actual extension by zero, determined up to unique adjunction-compatible iso. -/
  extension : Systems.{max c v, v, max c v r} (J.over U)
      (openRings.{c, v, r} J B U) (openTransitions.{c, v, r} J B τ U) ⥤ Systems.{c, v, max c v r}
        J B τ
  /-- Its universal property against the constructed restriction. -/
  ordinaryAdjunction : extension ⊣ openRestriction.{c, v, r} J B τ U
  /-- Extension is additive. -/
  [extensionAdditive : extension.Additive]
  /-- Extension is left exact. -/
  [extensionLimits : PreservesFiniteLimits extension]
  /-- Extension is right exact. -/
  [extensionColimits : PreservesFiniteColimits extension]
  /-- Levelwise actual direct-sum/sheafification extension. -/
  extensionEvaluation : ∀ n : ℕ,
    extension ⋙ evaluation.{c, v, max c v r} J B τ n ≅
      evaluation.{max c v, v, max c v r} (J.over U)
        (openRings.{c, v, r} J B U) (openTransitions.{c, v, r} J B τ U) n ⋙
          (@SheafOfModules.localizedSystemExtension.{c, v, r} C _ J
            (abelianSheafify.{c, v, max c v r} J)
            (locallyBijective.{c, v, max c v r} J) (B n) U)
  /-- Levelwise actual slice restriction. -/
  restrictionEvaluation : ∀ n : ℕ,
    openRestriction.{c, v, r} J B τ U ⋙ evaluation.{max c v, v, max c v r} (J.over U)
        (openRings.{c, v, r} J B U) (openTransitions.{c, v, r} J B τ U) n ≅
      evaluation.{c, v, max c v r} J B τ n ⋙
        SheafOfModules.localizedSystemRestriction.{c, v, r} (B n) U
  /-- Restriction evaluation retains the original section, at every coefficient level.
  Source: Stacks 03DJ, 0941 (blueprint: def-coef-semilinear-derived-calculus). -/
  restrictionSections : ∀ (n : ℕ)
    (N : Systems.{c, v, max c v r} J B τ) (V : (Over U)ᵒᵖ)
    (x : ((openRestriction.{c, v, r} J B τ U ⋙
      evaluation.{max c v, v, max c v r} (J.over U)
        (openRings.{c, v, r} J B U) (openTransitions.{c, v, r} J B τ U) n).obj N).val.obj V),
      HEq (((restrictionEvaluation n).hom.app N).val.app V x) x
  /-- Unit evaluation is the actual level unit, whose formula is the summand injection. -/
  unit_evaluation : ∀ (n : ℕ)
    (M : Systems.{max c v, v, max c v r} (J.over U)
      (openRings.{c, v, r} J B U) (openTransitions.{c, v, r} J B τ U)),
    (evaluation.{max c v, v, max c v r} (J.over U)
      (openRings.{c, v, r} J B U) (openTransitions.{c, v, r} J B τ U) n).map
        (ordinaryAdjunction.unit.app M) ≫
        (restrictionEvaluation n).hom.app (extension.obj M) ≫
        (SheafOfModules.localizedSystemRestriction.{c, v, r} (B n) U).map
          ((extensionEvaluation n).hom.app M) =
      ((@SheafOfModules.localizedSystemAdjunction.{c, v, r} C _ J
            (abelianSheafify.{c, v, max c v r} J)
            (locallyBijective.{c, v, max c v r} J) (B n) U)).unit.app
        ((evaluation.{max c v, v, max c v r} (J.over U)
          (openRings.{c, v, r} J B U) (openTransitions.{c, v, r} J B τ U) n).obj M)
  /-- Counit evaluation is the actual level counit. -/
  counit_evaluation : ∀ (n : ℕ) (N : Systems.{c, v, max c v r} J B τ),
    ((@SheafOfModules.localizedSystemExtension.{c, v, r} C _ J
            (abelianSheafify.{c, v, max c v r} J)
            (locallyBijective.{c, v, max c v r} J) (B n) U)).map
        ((restrictionEvaluation n).hom.app N) ≫
        ((@SheafOfModules.localizedSystemAdjunction.{c, v, r} C _ J
            (abelianSheafify.{c, v, max c v r} J)
            (locallyBijective.{c, v, max c v r} J) (B n) U)).counit.app
          ((evaluation.{c, v, max c v r} J B τ n).obj N) =
      (extensionEvaluation n).inv.app ((openRestriction.{c, v, r} J B τ U).obj N) ≫
        (evaluation.{c, v, max c v r} J B τ n).map (ordinaryAdjunction.counit.app N)
  /-- Ordinary unbounded derived j-shriek adjoint to derived j-star. -/
  adjunction : extension.mapDerivedCategory ⊣ (openRestriction.{c, v, r} J B τ U).mapDerivedCategory

  /-- The derived adjunction is exactly the localized ordinary Hom equivalence. -/
  transpose_model : ∀
    (P : CochainComplex (Systems.{max c v, v, max c v r} (J.over U)
      (openRings.{c, v, r} J B U) (openTransitions.{c, v, r} J B τ U)) ℤ)
    (Q : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ)
    (f : (extension.mapHomologicalComplex (.up ℤ)).obj P ⟶ Q),
    ((adjunction.homEquiv _ _)
      ((Functor.mapDerivedCategoryFactors extension).hom.app P ≫ DerivedCategory.Q.map f)) ≫
        (Functor.mapDerivedCategoryFactors (openRestriction.{c, v, r} J B τ U)).hom.app Q =
      DerivedCategory.Q.map
        (((ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv P Q) f)

```

## Users

The textual downstream query finds the following ten modules mentioning OpenSystems;
all other downstream modules use the same operations and projections. Every OpenSystems
parameter now includes its intended same-section normalization; the existing separate
normalization hypotheses remain verbatim and become redundant. Direct
importers of SemilinearDerivedCalculus are additionally compiled against the repair.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.BlockOpenExtensionAssembly` | unclaimed | Supply restrictionSections when updating restrictionEvaluation. |
| `Sheaf.Paper.BlockOpenExtensionTransitions` | unclaimed | Existing projections and signatures unchanged; no adaptation needed. |
| `Sheaf.Paper.OpenSystemUnitSections` | unclaimed | Existing projections and signatures unchanged; no adaptation needed. |
| `Sheaf.Paper.SemilinearDerivedCalculus` | unclaimed | Add proved-normalization field to the interface; no holes added. |
| `Sheaf.Paper.SemilinearDerivedSections` | unclaimed | Existing projections and signatures unchanged; no adaptation needed. |
| `Sheaf.Paper.SemilinearOperationsExistence` | unclaimed | Supply restrictionSections by the existing choose_spec proof. |
| `Sheaf.Paper.SemilinearTensorReductionCochain` | unclaimed | Keep ordinaryEvaluationTensor locally irreducible; unfold explicitly for its section law to improve the 64-second compile. No signature or exported attribute changes. |
| `Sheaf.Paper.SystemBlockRepetition` | unclaimed | Existing projections and signatures unchanged; no adaptation needed. |
| `Sheaf.SixFunctors.IntegralOpenReductionDefinitions` | unclaimed | Existing projections and signatures unchanged; no adaptation needed. |
| `Sheaf.SixFunctors.NormalizedOpenSections` | unclaimed | Existing projections and signatures unchanged; no adaptation needed. |
| `Sheaf.SixFunctors.OpenOperationModels` | unclaimed | Existing projections and signatures unchanged; no adaptation needed. |

## Status

landed 20261027T135439-L-3708468 2026-10-27 (merge of deliver/S8/Sheaf.Paper.OrdinaryOpenRestrictionQuotient)
