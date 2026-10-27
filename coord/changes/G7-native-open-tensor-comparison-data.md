# AlgebraicGeometry.ProEtaleWeilSheaf.NativeOpenTensorData

## Reason

Separate the native data declarations from their existence theorem so that the three
source steps can be stated in new modules without an import cycle. This is a verbatim
relocation and public reexport. No signature, field, universe, instance, attribute or
definition body changes. No existing source-library module changes.

## Old

In `Sheaf.Paper.NativeOpenDerivedTensor`:

```lean
/-- All normalizations of the native open tensor isomorphism. These are conclusions
of the theorem below, not extra hypotheses on the open immersion or its inputs.
The coefficient localization is the actual adic coefficient pullback used by upperStar.
Source: Stacks 0E8I, 0GL1, 03D8 and openTensorNormalization
(blueprint: lem-sf-native-open-derived-tensor). -/
structure NativeOpenTensorData where
  /-- The equivariant open adjunction. -/
  adj : extensionByZero k₀ l j ⊣ upperStar k₀ l j
  /-- Its unit is the ordinary unit on the geometric open. -/
  unit_forget : ∀ M, (adj.unit.app M).hom.f =
    (ProEtale.adicOpenImmersionLowerShriekAdjunction l
      (Scheme.Hom.geometricFiberMap j (comp_over j _))).unit.app M.carrier
  /-- Its counit is the ordinary counit, fixing the adjunction itself. -/
  counit_forget : ∀ N, (adj.counit.app N).hom.f =
    (ProEtale.adicOpenImmersionLowerShriekAdjunction l
      (Scheme.Hom.geometricFiberMap j (comp_over j _))).counit.app N.carrier
  /-- The open unit is invertible. -/
  unit_iso : ∀ M, IsIso (adj.unit.app M)
  /-- Restriction commutes with sheaf tensor. -/
  sheafRestriction : ∀ M N : ProEtaleWeilSheaf k₀ l Z,
    (upperStar k₀ l j).obj (tensor k₀ l Z N M) ≅
      tensor k₀ l U ((upperStar k₀ l j).obj N) ((upperStar k₀ l j).obj M)
  /-- Its underlying map is the canonical balanced tensor comparison. -/
  restriction_forget : ∀ M N, HEq ((sheafRestriction M N).hom.hom.f) (
    (ProEtale.adicUpperStarTensorLeftIso l
      (Scheme.Hom.geometricFiberMap j (comp_over j _)) N.carrier).hom.app M.carrier)
  /-- The generator-normalized, equivariant sheaf open tensor isomorphism. -/
  sheafGamma : ∀ (M : ProEtaleWeilSheaf k₀ l U) (N : ProEtaleWeilSheaf k₀ l Z),
    tensor k₀ l Z N ((extensionByZero k₀ l j).obj M) ≅
      (extensionByZero k₀ l j).obj (tensor k₀ l U ((upperStar k₀ l j).obj N) M)
  /-- Its inverse is the unit transpose, which fixes both maps uniquely. -/
  sheaf_inverse : ∀ M N, HEq (adj.homEquiv _ _ ((sheafGamma M N).inv)) (
    (tensorFunctor k₀ l U ((upperStar k₀ l j).obj N)).map (adj.unit.app M) ≫
      (sheafRestriction ((extensionByZero k₀ l j).obj M) N).inv)
  /-- Exact extension preserves categorical two-sided K-flatness. -/
  extension_kflat : ∀ P, NativeIsKFlat k₀ l U P → NativeIsKFlat k₀ l Z
    (((extensionByZero k₀ l j).mapHomologicalComplex (.up ℤ)).obj P)
  /-- Exact restriction preserves categorical two-sided K-flatness. -/
  restriction_kflat : ∀ T, NativeIsKFlat k₀ l Z T → NativeIsKFlat k₀ l U
    (((upperStar k₀ l j).mapHomologicalComplex (.up ℤ)).obj T)


/-- Chain and derived comparisons extending the normalized sheaf comparison.
Source: Stacks 0GL1 (blueprint: lem-sf-native-open-derived-tensor). -/
structure NativeOpenDerivedTensorData (sheaves : NativeOpenTensorData k₀ l j) where
  /-- The natural isomorphism on arbitrary ambient derived inputs. -/
  gamma : nativeOpenDerivedLeft k₀ l j ≅ nativeOpenDerivedRight k₀ l j
  /-- Derived restriction and tensor comparison. -/
  restriction : nativeDerivedTensor k₀ l Z ⋙ nativeOpenPull k₀ l j ≅
    (nativeOpenPull k₀ l j).prod (nativeOpenPull k₀ l j) ⋙ nativeDerivedTensor k₀ l U
  /-- The inverse is the open-unit transpose in the actual derived adjunction. -/
  inverse_unit : OpenTensorUnitNormalization
    (nativeOpenExtension k₀ l j) (nativeOpenPull k₀ l j)
    (nativeDerivedTensor k₀ l U) (nativeDerivedTensor k₀ l Z)
    sheaves.adj.mapExactDerivedCategory restriction gamma
  /-- Ordinary normalization and the equality after forgetting Frobenius. -/
  ordinary : Nonempty (OpenTensorForgetData
    (nativeOpenExtension k₀ l j) (nativeOpenPull k₀ l j)
    (ProEtale.adicOpenImmersionLowerShriek l
      (Scheme.Hom.geometricFiberMap j (comp_over j _))).mapDerivedCategory
    (ProEtale.adicUpperStar l
      (Scheme.Hom.geometricFiberMap j (comp_over j _))).mapDerivedCategory
    (nativeForget k₀ l U) (nativeForget k₀ l Z)
    (nativeDerivedTensor k₀ l U) (nativeDerivedTensor k₀ l Z)
    (nativeDerivedClosedComparison k₀ l U).ordinaryClosed.tensor
    (nativeDerivedClosedComparison k₀ l Z).ordinaryClosed.tensor
    (nativeOpenForgetExtension k₀ l j) (nativeOpenForgetPull k₀ l j)
    (nativeDerivedClosedComparison k₀ l U).tensorComparison
    (nativeDerivedClosedComparison k₀ l Z).tensorComparison
    (ProEtale.adicOpenImmersionLowerShriekAdjunction l
      (Scheme.Hom.geometricFiberMap j (comp_over j _))).mapExactDerivedCategory restriction gamma)

/-- Every operation and representative in the presentation is the actual native one.
HEq records equality of dependent presentations without imposing another tensor choice.
Source: Stacks 0GL1 (blueprint: lem-sf-native-open-derived-tensor). -/
def NativeOpenPresentationCompatibility (s : NativeOpenTensorData k₀ l j)
    (d : NativeOpenDerivedTensorData k₀ l j s)
    (c : OpenTensorPresentation (ProEtaleWeilSheaf k₀ l U) (ProEtaleWeilSheaf k₀ l Z)) :
    Prop :=
  HEq c.E (extensionByZero k₀ l j) ∧ HEq c.R (upperStar k₀ l j) ∧
  HEq c.SA (nativeOpenSheafTensor k₀ l U) ∧ HEq c.SB (nativeOpenSheafTensor k₀ l Z) ∧
  HEq c.TA (nativeTensorTotal k₀ l U) ∧ HEq c.TB (nativeTensorTotal k₀ l Z) ∧
  HEq c.DA (nativeDerivedTensor k₀ l U) ∧ HEq c.DB (nativeDerivedTensor k₀ l Z) ∧
  HEq c.flatA (NativeIsKFlat k₀ l U) ∧ HEq c.flatB (NativeIsKFlat k₀ l Z) ∧
  HEq c.modelA (nativeOpenTensorModel k₀ l U) ∧
  HEq c.modelB (nativeOpenTensorModel k₀ l Z) ∧
  HEq c.iA (nativeOpenTensorInsertion k₀ l U) ∧
  HEq c.iB (nativeOpenTensorInsertion k₀ l Z) ∧
  HEq c.sheafGamma s.sheafGamma ∧ HEq c.gamma d.gamma ∧
  HEq c.sheafRestriction s.sheafRestriction ∧ HEq c.restriction d.restriction
```

## New

The exact declarations above, including their docstrings and bodies, now occur in
`Sheaf.Paper.NativeOpenTensorComparisonData`. The old entry module has
`public import Sheaf.Paper.NativeOpenTensorComparisonData`; it exposes exactly the
same declarations and transitive public imports. The complete new definitions are:

```lean
/-- All normalizations of the native open tensor isomorphism. These are conclusions
of the theorem below, not extra hypotheses on the open immersion or its inputs.
The coefficient localization is the actual adic coefficient pullback used by upperStar.
Source: Stacks 0E8I, 0GL1, 03D8 and openTensorNormalization
(blueprint: lem-sf-native-open-derived-tensor). -/
structure NativeOpenTensorData where
  /-- The equivariant open adjunction. -/
  adj : extensionByZero k₀ l j ⊣ upperStar k₀ l j
  /-- Its unit is the ordinary unit on the geometric open. -/
  unit_forget : ∀ M, (adj.unit.app M).hom.f =
    (ProEtale.adicOpenImmersionLowerShriekAdjunction l
      (Scheme.Hom.geometricFiberMap j (comp_over j _))).unit.app M.carrier
  /-- Its counit is the ordinary counit, fixing the adjunction itself. -/
  counit_forget : ∀ N, (adj.counit.app N).hom.f =
    (ProEtale.adicOpenImmersionLowerShriekAdjunction l
      (Scheme.Hom.geometricFiberMap j (comp_over j _))).counit.app N.carrier
  /-- The open unit is invertible. -/
  unit_iso : ∀ M, IsIso (adj.unit.app M)
  /-- Restriction commutes with sheaf tensor. -/
  sheafRestriction : ∀ M N : ProEtaleWeilSheaf k₀ l Z,
    (upperStar k₀ l j).obj (tensor k₀ l Z N M) ≅
      tensor k₀ l U ((upperStar k₀ l j).obj N) ((upperStar k₀ l j).obj M)
  /-- Its underlying map is the canonical balanced tensor comparison. -/
  restriction_forget : ∀ M N, HEq ((sheafRestriction M N).hom.hom.f) (
    (ProEtale.adicUpperStarTensorLeftIso l
      (Scheme.Hom.geometricFiberMap j (comp_over j _)) N.carrier).hom.app M.carrier)
  /-- The generator-normalized, equivariant sheaf open tensor isomorphism. -/
  sheafGamma : ∀ (M : ProEtaleWeilSheaf k₀ l U) (N : ProEtaleWeilSheaf k₀ l Z),
    tensor k₀ l Z N ((extensionByZero k₀ l j).obj M) ≅
      (extensionByZero k₀ l j).obj (tensor k₀ l U ((upperStar k₀ l j).obj N) M)
  /-- Its inverse is the unit transpose, which fixes both maps uniquely. -/
  sheaf_inverse : ∀ M N, HEq (adj.homEquiv _ _ ((sheafGamma M N).inv)) (
    (tensorFunctor k₀ l U ((upperStar k₀ l j).obj N)).map (adj.unit.app M) ≫
      (sheafRestriction ((extensionByZero k₀ l j).obj M) N).inv)
  /-- Exact extension preserves categorical two-sided K-flatness. -/
  extension_kflat : ∀ P, NativeIsKFlat k₀ l U P → NativeIsKFlat k₀ l Z
    (((extensionByZero k₀ l j).mapHomologicalComplex (.up ℤ)).obj P)
  /-- Exact restriction preserves categorical two-sided K-flatness. -/
  restriction_kflat : ∀ T, NativeIsKFlat k₀ l Z T → NativeIsKFlat k₀ l U
    (((upperStar k₀ l j).mapHomologicalComplex (.up ℤ)).obj T)


/-- Chain and derived comparisons extending the normalized sheaf comparison.
Source: Stacks 0GL1 (blueprint: lem-sf-native-open-derived-tensor). -/
structure NativeOpenDerivedTensorData (sheaves : NativeOpenTensorData k₀ l j) where
  /-- The natural isomorphism on arbitrary ambient derived inputs. -/
  gamma : nativeOpenDerivedLeft k₀ l j ≅ nativeOpenDerivedRight k₀ l j
  /-- Derived restriction and tensor comparison. -/
  restriction : nativeDerivedTensor k₀ l Z ⋙ nativeOpenPull k₀ l j ≅
    (nativeOpenPull k₀ l j).prod (nativeOpenPull k₀ l j) ⋙ nativeDerivedTensor k₀ l U
  /-- The inverse is the open-unit transpose in the actual derived adjunction. -/
  inverse_unit : OpenTensorUnitNormalization
    (nativeOpenExtension k₀ l j) (nativeOpenPull k₀ l j)
    (nativeDerivedTensor k₀ l U) (nativeDerivedTensor k₀ l Z)
    sheaves.adj.mapExactDerivedCategory restriction gamma
  /-- Ordinary normalization and the equality after forgetting Frobenius. -/
  ordinary : Nonempty (OpenTensorForgetData
    (nativeOpenExtension k₀ l j) (nativeOpenPull k₀ l j)
    (ProEtale.adicOpenImmersionLowerShriek l
      (Scheme.Hom.geometricFiberMap j (comp_over j _))).mapDerivedCategory
    (ProEtale.adicUpperStar l
      (Scheme.Hom.geometricFiberMap j (comp_over j _))).mapDerivedCategory
    (nativeForget k₀ l U) (nativeForget k₀ l Z)
    (nativeDerivedTensor k₀ l U) (nativeDerivedTensor k₀ l Z)
    (nativeDerivedClosedComparison k₀ l U).ordinaryClosed.tensor
    (nativeDerivedClosedComparison k₀ l Z).ordinaryClosed.tensor
    (nativeOpenForgetExtension k₀ l j) (nativeOpenForgetPull k₀ l j)
    (nativeDerivedClosedComparison k₀ l U).tensorComparison
    (nativeDerivedClosedComparison k₀ l Z).tensorComparison
    (ProEtale.adicOpenImmersionLowerShriekAdjunction l
      (Scheme.Hom.geometricFiberMap j (comp_over j _))).mapExactDerivedCategory restriction gamma)

/-- Every operation and representative in the presentation is the actual native one.
HEq records equality of dependent presentations without imposing another tensor choice.
Source: Stacks 0GL1 (blueprint: lem-sf-native-open-derived-tensor). -/
def NativeOpenPresentationCompatibility (s : NativeOpenTensorData k₀ l j)
    (d : NativeOpenDerivedTensorData k₀ l j s)
    (c : OpenTensorPresentation (ProEtaleWeilSheaf k₀ l U) (ProEtaleWeilSheaf k₀ l Z)) :
    Prop :=
  HEq c.E (extensionByZero k₀ l j) ∧ HEq c.R (upperStar k₀ l j) ∧
  HEq c.SA (nativeOpenSheafTensor k₀ l U) ∧ HEq c.SB (nativeOpenSheafTensor k₀ l Z) ∧
  HEq c.TA (nativeTensorTotal k₀ l U) ∧ HEq c.TB (nativeTensorTotal k₀ l Z) ∧
  HEq c.DA (nativeDerivedTensor k₀ l U) ∧ HEq c.DB (nativeDerivedTensor k₀ l Z) ∧
  HEq c.flatA (NativeIsKFlat k₀ l U) ∧ HEq c.flatB (NativeIsKFlat k₀ l Z) ∧
  HEq c.modelA (nativeOpenTensorModel k₀ l U) ∧
  HEq c.modelB (nativeOpenTensorModel k₀ l Z) ∧
  HEq c.iA (nativeOpenTensorInsertion k₀ l U) ∧
  HEq c.iB (nativeOpenTensorInsertion k₀ l Z) ∧
  HEq c.sheafGamma s.sheafGamma ∧ HEq c.gamma d.gamma ∧
  HEq c.sheafRestriction s.sheafRestriction ∧ HEq c.restriction d.restriction
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.NativeOpenDerivedTensor | G7 | Publicly reexports the identical data; assembles the theorem from three source steps. |
| Sheaf.Paper.NativeCompactProjectionFormula | unclaimed in local claim records | Direct importer and user of all three data declarations; no adaptation. Compilation against the extraction is checked. |
| Sheaf.Paper.WeilCompactStructureTensorComparison | unclaimed in local claim records | Indirect importer and user of all three data declarations; no adaptation or change of meaning. |

`tools/downstream.py Sheaf.Paper.NativeOpenDerivedTensor --uses NativeOpenTensorData`
reports these three textual users and 99 transitive importers. All three declaration
names, signatures, visibility and bodies stay identical, so every transitive use has
the same meaning. The native data node's Lean attachment moves to the new module;
the theorem node retains only its theorem declaration, avoiding duplicate ownership.

## Status

landed 20261027T131454-L-2940282 2026-10-27 (merge of deliver/G7/Sheaf.Paper.NativeOpenDerivedTensor)
