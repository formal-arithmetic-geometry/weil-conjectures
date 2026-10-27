# AlgebraicGeometry.Etale.smallModel_isIso_strictHenselization_baseChange_modelGlobalHomology

## Reason

Retire the module listed by coord/retire-items.tsv without conflating its small-model
statement with the adopted strictLocalization statement. The current item has zero
sorry. Its declaration collides by name with the adopted theorem when both modules
are imported. The 2026-10-21 restoration correctly preserved different mathematics,
but its unchanged name still prevents coexistence with the adopted API.

The current retirement row names the old closed-stalk consumer. That file is already
a withdrawn stub, and the current downstream.py census reports zero direct or
transitive Lean importers. The closed-stalk DAG parent still needs the original
small-model statement. Preserve it in StrictLocalSmallModel.BaseChangeModelGlobalHomology
with a smallModel_ name and attach its existing node there. No DAG node is removed.

A shorter proof is available: the canonical small-to-full colimit comparison is
already an isomorphism over S, by smallStrictHenselizationColimitIso_toBase. Compose
the supplied affine presentation with its spectrum isomorphism, transport the bottom
morphism of the same cartesian square, and apply the existing adopted model theorem.
This replaces all five private categorical helpers and the former small-model
continuity dependency. No adopted source file, definition, hypothesis, conclusion,
unit realization or target statement is changed.

## Old

Module: Sheaf.AlgebraicGeometry.StrictLocalBaseChangeModelGlobalHomology.
Its public signature, verbatim:

```lean
theorem isIso_strictHenselization_baseChange_modelGlobalHomology
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {A : Type u} [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    (eA : Spec (.of A) ≅ strictHenselizationScheme s)
    {X₀ : Scheme.{u}} (p₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (.of A))
    (sq₀ : IsPullback p₀ f₀ f (eA.hom ≫ strictHenselizationStructuralMap s))
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (n : ℤ) :
    IsIso ((Sheaf.Γ (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{u + 1}).map
      ((DerivedCategory.Plus.homologyFunctor _ n).map
        ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq₀.toCommSq).app K)))
```

It publicly imports StrictHenselizationStructuralMap, BaseChange.Derived and
Mathlib.RingTheory.Henselian from WeilConjectures. The private proof imports the
small-model canonical global-homology theorem, derived horizontal pasting, derived
comparison, injective homology, global sections, exact inverse-image homology and
the square API. The proof repeats the five private helpers from the adopted theorem.

## New

Module: Sheaf.AlgebraicGeometry.StrictLocalSmallModel.BaseChangeModelGlobalHomology.
The signature changes only its declaration name:

```lean
theorem smallModel_isIso_strictHenselization_baseChange_modelGlobalHomology
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {A : Type u} [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    (eA : Spec (.of A) ≅ strictHenselizationScheme s)
    {X₀ : Scheme.{u}} (p₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (.of A))
    (sq₀ : IsPullback p₀ f₀ f (eA.hom ≫ strictHenselizationStructuralMap s))
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (n : ℤ) :
    IsIso ((Sheaf.Γ (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{u + 1}).map
      ((DerivedCategory.Plus.homologyFunctor _ n).map
        ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq₀.toCommSq).app K)))
```

The three public imports are preserved. The two private imports are
WeilConjectures.AlgebraicGeometry.StrictLocalBaseChangeModelGlobalHomology and
Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberComparison. The complete proof
uses the canonical comparison, its structural-map equation and the adopted theorem.
The old module is explicitly withdrawn in deleted.txt.

The original node retains its natural-language statement and statement dependencies;
its Lean attachment changes to the new name and module. Its proof now records this
transport and its two actual dependencies. A new source attachment node,
src-weil-pbc-strict-localization-model-global-homology, records the exact already
proved adopted theorem with its full-model signature. It adds no Lean declaration
and no hole. The parent dependency on the original node remains valid.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeModelGlobalHomology | Q7 dispatch | Retired collision; original statement preserved under the smallModel_ name. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.BaseChangeModelGlobalHomology | Q7, new module | Complete transport proof with the original hypotheses and conclusion. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeClosedStalk | unclaimed, withdrawn stub | No current Lean import or call to adapt; its DAG parent still has exactly the needed small-model theorem through the unchanged node id. A complete temporary original-model consumer checks the renamed call. |

The actual downstream.py --uses census lists no importing modules; the old theorem's
own declaration is its only textual use in that closure. The similarly named adopted
closed-stalk theorem imports the adopted model theorem and is unchanged. No quarantined
consumer or rework row for the item is present. No held module is adapted.

The replacement compiles without warnings in 9.2 seconds. The full temporary
original-model closed-stalk consumer compiles in 5.6 seconds. Printed axioms for
the consumer, the replacement and the adopted model theorem are exactly propext,
Classical.choice and Quot.sound. The temporary source is outside the delivered
Lean tree, in scratchpad/ModelConsumer.lean.txt.

## Status

landed 20261023T170113-L-2065250 2026-10-23 (merge of deliver/Q7/Sheaf.AlgebraicGeometry.StrictLocalBaseChangeModelGlobalHomology)
