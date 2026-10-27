# Ordered integration constructions

## Reason

Move the nine canonical constructions into a shared definition module, so unit normalization and the integration-before-transposition identity can state their separate mathematical conclusions without an import cycle. The original module publicly imports that module. This is a location and import-interface change; no signature, visibility or target meaning changes. The unit identification has a general
coefficient wrapper to prevent expensive concrete instance unfolding.

## Old

In `Sheaf.Paper.IntegrationTransposeComposition`:

```lean
/-- The tensor-twisted exact inverse image appearing in integration.
Source: cor-pur-vector-bundle-purity.proof.md, paragraph 2
(blueprint: lem-pur-integration-transpose-composition). -/
def object (f : X ⟶ Y) (W : DerivedCategoryModule A X)
    (K : DerivedCategoryModule A Y) : DerivedCategoryModule A X :=
  ((derivedTensor (ModuleCat.{u + 1} A) X).obj
    ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj K)).obj W

/-- Integration: inverse canonical projection, tensor the trace, then the unit constraint.
Source: cor-pur-vector-bundle-purity.proof.md, paragraph 2
(blueprint: lem-pur-integration-transpose-composition). -/
def integration (f : X ⟶ Y) [HasCompactification f]
    (W : DerivedCategoryModule A X)
    (t : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj W ⟶
      𝟙_ (DerivedCategoryModule A Y))
    (hP : ∀ K : DerivedCategoryModule A Y, IsIso (compactSupportProjectionMap A f W K))
    (K : DerivedCategoryModule A Y) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj (object f W K) ⟶ K :=
  @inv _ _ _ _ (compactSupportProjectionMap A f W K) (hP K) ≫
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj K).map t ≫
    (derivedTensorRightUnitor (ModuleCat.{u + 1} A) Y K).hom

/-- The transpose under the specified actual right adjoint, with no constructibility bound.
Source: cor-pur-vector-bundle-purity.proof.md, paragraph 2
(blueprint: lem-pur-integration-transpose-composition). -/
def gamma (f : X ⟶ Y) [HasCompactification f]
    (R : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X)
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⊣ R)
    (W : DerivedCategoryModule A X)
    (t : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj W ⟶
      𝟙_ (DerivedCategoryModule A Y))
    (hP : ∀ K : DerivedCategoryModule A Y, IsIso (compactSupportProjectionMap A f W K))
    (K : DerivedCategoryModule A Y) : object f W K ⟶ R.obj K :=
  adj.homEquiv _ _ (integration f W t hP K)

/-- The exact inverse-image unit constraint, transported through the canonical comparison.
Source: cor-pur-vector-bundle-purity.proof.md, paragraph 2, orientation at the unit
(blueprint: lem-pur-integration-transpose-composition). -/
def unitObjectIso (f : X ⟶ Y) (W : DerivedCategoryModule A X) :
    object f W (𝟙_ (DerivedCategoryModule A Y)) ≅ W :=
  ((derivedTensor (ModuleCat.{u + 1} A) X).mapIso
    ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm.app _ ≪≫
      leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f)).app W ≪≫
    derivedTensorLeftUnitor (ModuleCat.{u + 1} A) X W

/-- Orientation at the unit, whose domain is W after the canonical unit identification.
Source: cor-pur-vector-bundle-purity.proof.md, paragraph 2
(blueprint: lem-pur-integration-transpose-composition). -/
def orientation (f : X ⟶ Y) [HasCompactification f]
    (R : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X)
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⊣ R)
    (W : DerivedCategoryModule A X)
    (t : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj W ⟶
      𝟙_ (DerivedCategoryModule A Y))
    (hP : ∀ K : DerivedCategoryModule A Y, IsIso (compactSupportProjectionMap A f W K)) :
    W ⟶ R.obj (𝟙_ (DerivedCategoryModule A Y)) :=
  (unitObjectIso f W).inv ≫ gamma f R adj W t hP _

/-- The dualizing tensor map, defined wherever its canonical projection is invertible.
Source: cor-pur-vector-bundle-purity.proof.md, paragraph 2
(blueprint: lem-pur-integration-transpose-composition). -/
def theta (f : X ⟶ Y) [HasCompactification f]
    (R : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X)
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⊣ R)
    (L : DerivedCategoryModule A Y)
    (hP : IsIso (compactSupportProjectionMap A f (R.obj (𝟙_ _)) L)) :
    object f (R.obj (𝟙_ _)) L ⟶ R.obj L :=
  adj.homEquiv _ _
    (@inv _ _ _ _ (compactSupportProjectionMap A f (R.obj (𝟙_ _)) L) hP ≫
      ((derivedTensor (ModuleCat.{u + 1} A) Y).obj L).map (adj.counit.app (𝟙_ _)) ≫
      (derivedTensorRightUnitor (ModuleCat.{u + 1} A) Y L).hom)

/-- Exact pullback of tensor, using the published K-flat tensor comparison and exact descent.
Source: cor-pur-vector-bundle-purity.proof.md, paragraph 2, ordered tensor reassociation
(blueprint: lem-pur-integration-transpose-composition). -/
def pullTensorIso (f : X ⟶ Y) (K M : DerivedCategoryModule A Y) :
    (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj
      (((derivedTensor (ModuleCat.{u + 1} A) Y).obj K).obj M) ≅
      ((derivedTensor (ModuleCat.{u + 1} A) X).obj
        ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj K)).obj
          ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj M) :=
  (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm.app _ ≪≫
    leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f K M ≪≫
    ((derivedTensor (ModuleCat.{u + 1} A) X).mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).app K)).app _ ≪≫
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj _).mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).app M)

/-- Ordered reassociation a_K, with exact pullback composition and no block interchange.
Source: cor-pur-vector-bundle-purity.proof.md, paragraph 2
(blueprint: lem-pur-integration-transpose-composition). -/
def reassociation (f : X ⟶ Y) (g : Y ⟶ Z)
    (Wf : DerivedCategoryModule A X) (Wg : DerivedCategoryModule A Y)
    (K : DerivedCategoryModule A Z) :
    object (f ≫ g) (object f Wf Wg) K ≅ object f Wf (object g Wg K) :=
  ((derivedTensor (ModuleCat.{u + 1} A) X).mapIso
      ((unboundedEtaleUpperStarCompIso A f g).app K)).app _ ≪≫
    (derivedTensorAssociator (ModuleCat.{u + 1} A) X _ _ Wf).symm ≪≫
    ((derivedTensor (ModuleCat.{u + 1} A) X).mapIso
      (pullTensorIso f
        ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.obj K) Wg).symm).app Wf

/-- The adjunction-preserving right mate of the fixed proper/open compact-support compositor.
Source: cor-pur-vector-bundle-purity.proof.md, paragraph 2
(blueprint: lem-pur-integration-transpose-composition). -/
def rightMate [Finite A] (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact (f ≫ g)]
    (Rf : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X)
    (Rg : DerivedCategoryModule A Z ⥤ DerivedCategoryModule A Y)
    (Rh : DerivedCategoryModule A Z ⥤ DerivedCategoryModule A X)
    (adjf : rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⊣ Rf)
    (adjg : rightDerivedLowerShriek (ModuleCat.{u + 1} A) g ⊣ Rg)
    (adjh : rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g) ⊣ Rh) :
    Rh ≅ Rg ⋙ Rf :=
  adjh.rightAdjointUniq
    ((adjf.comp adjg).ofNatIsoLeft (unboundedEtaleLowerShriekCompIso A f g))
```

## New

Eight declarations above move verbatim to `Sheaf.Paper.IntegrationTransposeCompositionData`.
`unitObjectIso` keeps its signature and now specializes the irreducible general coefficient
wrapper `integrationUnitObjectIso`, whose body is exactly the former three-factor construction.
This avoids repeated concrete derived tensor instance comparisons during kernel checking.
The mathematical isomorphism and its domain and codomain do not change. The original module starts with:

```lean
public import Sheaf.Paper.IntegrationTransposeCompositionData
```

The new module carries the original public imports; the original module re-exports them. Before the performance repair, the byte-for-byte comparison of the nine definitions passed.
The performance repair changes only unitObjectIso to call the generic wrapper; its unfolded
body is the former expression. No adopted-source module changes.

The performance wrapper and the specializing definition are:

```lean
/-- Unit identification for an arbitrary coefficient category, packaged before specialization.
Source: cor-pur-vector-bundle-purity.proof.md paragraph 2.
(blueprint: def-pur-integration-transpose-data). -/
@[irreducible]
def integrationUnitObjectIso
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B] [UpperStarPreservesFlat B]
    {V T : Scheme.{u}} (f : V ⟶ T)
    (W : _root_.DerivedCategory (Sheaf V.smallEtaleTopology B)) :
    ((derivedTensor B V).obj ((upperStar B f).mapDerivedCategory.obj (𝟙_ _))).obj W ≅ W :=
  ((derivedTensor B V).mapIso
    ((leftDerivedUpperStarIsoMapDerivedCategory B f).symm.app _ ≪≫
      leftDerivedUpperStarUnitIso B f)).app W ≪≫ derivedTensorLeftUnitor B V W

def unitObjectIso (f : X ⟶ Y) (W : DerivedCategoryModule A X) :
    object f W (𝟙_ (DerivedCategoryModule A Y)) ≅ W :=
  integrationUnitObjectIso (ModuleCat.{u + 1} A) f W
```

The second general coefficient wrapper packages the coefficient-first projection. Its
specialization is proved equal to the existing map in `IntegrationUnitNormalization`.

```lean
/-- Coefficient-first canonical projection, packaged over a general coefficient category.
Source: cor-pur-vector-bundle-purity.proof.md paragraph 2.
(blueprint: def-pur-integration-transpose-data). -/
@[irreducible]
def integrationProjection
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B] [UpperStarPreservesFlat B]
    {FC : B → B → Type (u + 1)} {CC : B → Type (u + 1)}
    [∀ (P Q : B), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} B FC]
    [(CategoryTheory.forget B).ReflectsIsomorphisms]
    [CategoryTheory.Limits.PreservesFilteredColimitsOfSize.{u + 1, u + 1}
      (CategoryTheory.forget B)]
    [∀ T : Scheme.{u}, T.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget B)]
    {V T : Scheme.{u}} (f : V ⟶ T) [HasCompactification f]
    (W : _root_.DerivedCategory (Sheaf V.smallEtaleTopology B))
    (K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology B)) :
    ((derivedTensor B T).obj K).obj ((rightDerivedLowerShriek B f).obj W) ⟶
      (rightDerivedLowerShriek B f).obj
        (((derivedTensor B V).obj ((upperStar B f).mapDerivedCategory.obj K)).obj W) :=
  ((derivedTensorSymmetry B T).hom.app K).app ((rightDerivedLowerShriek B f).obj W) ≫
    ((projectionMap B f).app W).app K ≫
    (rightDerivedLowerShriek B f).map (((derivedTensor B V).obj W).map
      ((leftDerivedUpperStarIsoMapDerivedCategory B f).hom.app K)) ≫
    (rightDerivedLowerShriek B f).map (((derivedTensorSymmetry B V).inv.app
      ((upperStar B f).mapDerivedCategory.obj K)).app W)

```

## Users

Ran `tools/downstream.py Sheaf.Paper.IntegrationTransposeComposition --uses object integration gamma unitObjectIso orientation theta pullTensorIso reassociation rightMate` and inspected the hits.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegrationTransposeComposition | K6 | Same names and defining terms via public import. |
| Sheaf.Paper.AffineOrderedIntegrationTransposes | unclaimed | No adaptation: imports and mathematical statements stay valid through the public re-export. |
| Sheaf.Paper.ChartTargetOpenDescent | unclaimed | No adaptation: imports and mathematical statements stay valid through the public re-export. |
| Sheaf.Paper.CompositionModelOrientationDescent | unclaimed | No adaptation: imports and mathematical statements stay valid through the public re-export. |

The new modules `Sheaf.Paper.IntegrationUnitNormalization` and `Sheaf.Paper.IteratedIntegration` import the definition module directly. No other group-held module is adapted. The existing target statements have exactly the same meanings because their canonical constructions are preserved.

## Status

landed 20261025T013218-L-3940996 2026-10-25 (merge of deliver/K6/Sheaf.Paper.IntegrationTransposeComposition)
