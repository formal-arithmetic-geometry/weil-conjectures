# AlgebraicGeometry.ProEtale.CompactificationBProjection presentation

## Reason

Move the 17 existing definitions, with identical names, signatures and bodies, to
Sheaf.Paper.CompactificationBProjectionData. The domain and ordinary-square lemmas
must use those definitions and the original theorem must import those lemmas;
leaving the definitions in the original module would create an import cycle.
The completed projection theorem keeps its exact signature. No mathematical
object or target meaning changes.

## Old

The following definitions were declared in
Sheaf.Paper.CompactificationBProjectionReduction:

```lean
/-- The published signed tensor symmetry on an ordinary integral tensor presentation.
Source: blueprint direct-image proof (3), tensor order
(blueprint: lem-pur-compactification-b-projection-reduction). -/
def integralSymmetry (T : Scheme.{u})
    (a : Scheme.ProEtaleTensorModel T ((PurCompactSupport.completed l E).ring T)) :=
  SheafOfModules.derivedTensorSymmetry.{u + 1, u, u + 2} ((PurCompactSupport.completed l E).ring T)
    ({ tensor := a.tensor, representative := a.representative } :
      SheafOfModules.ShiftedTensorModel.{u + 1, u, u + 2}
        ((PurCompactSupport.completed l E).ring T))

/-- The actual coefficient ring sheaf on the ell-power sequence site.
Source: blueprint direct-image proof (3)
(blueprint: lem-pur-compactification-b-projection-reduction). -/
abbrev systemRing (T : Scheme.{u}) :=
  SemilinearSections.systemRing (Scheme.ProEt.topology T)
    (VaryingRing.coefficients (rings l E) T)
    (VaryingRing.coefficientTransition (rings l E) (transitions l E) T)

/-- Forget only termwise flatness in the existing resolving category.
Source: Stacks 06YU, blueprint direct-image proof (3)
(blueprint: lem-pur-compactification-b-projection-reduction). -/
def resolvingInclusion (T : Scheme.{u}) :
    (SheafOfModules.shiftedTensorResolving (systemRing l E T)).FullSubcategory ⥤
    ObjectProperty.FullSubcategory
      (CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (J := coefficientSequenceTopology (Scheme.ProEt.topology T))
        (R := systemRing l E T)) where
  obj P := ⟨P.obj, P.property.1⟩
  map f := ⟨f.hom⟩

/-- The same system tensor on flat-term K-flat representatives.
Source: blueprint direct-image proof (3), signed tensor
(blueprint: lem-pur-compactification-b-projection-reduction). -/
def systemTensorModel (m : DescentModels l E) (T : Scheme.{u}) :
    SheafOfModules.ShiftedTensorModel.{u + 1, u, u + 2} (systemRing l E T) where
  tensor := (m.systems T).closed.tensor
  representative := Functor.isoWhiskerLeft
    ((resolvingInclusion l E T).prod (resolvingInclusion l E T))
    (m.systems T).tensorModels.comparison

/-- The canonical Koszul symmetry of the entire-system tensor.
Source: blueprint direct-image proof (3)
(blueprint: lem-pur-compactification-b-projection-reduction). -/
def systemSymmetry (m : DescentModels l E) (T : Scheme.{u}) :=
  SheafOfModules.derivedTensorSymmetry.{u + 1, u, u + 2}
    (systemRing l E T) (systemTensorModel l E m T)

variable (m : DescentModels l E)

/-- The coefficient-first ordinary inner tensor; completing it also completes
its pullback factor, with the canonical completion-unit identification.
Source: blueprint direct-image proof (3)
(blueprint: lem-pur-compactification-b-projection-reduction). -/
def ordinaryInner {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : CompleteProjectionDescent.Integral l E Y)
    (M : CompleteProjectionDescent.Integral l E X) :=
  (m.integral.tensor X).ordinary.tensor.obj ((ringedPull l E f).obj K, M)

/-- The coefficient-first ordinary source tensor.
Source: blueprint direct-image proof (3)
(blueprint: lem-pur-compactification-b-projection-reduction). -/
def ordinarySource {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : CompleteProjectionDescent.Integral l E Y)
    (M : CompleteProjectionDescent.Integral l E X) :=
  (m.integral.tensor Y).ordinary.tensor.obj (K, (integralImage l E c).obj M)

/-- The displayed D uses the published completed pullback and completed tensor.
Source: blueprint direct-image proof (3)
(blueprint: lem-pur-compactification-b-projection-reduction). -/
def completedInner {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : CompleteProjectionDescent.Integral l E Y)
    (M : CompleteProjectionDescent.Integral l E X) :=
  (integralCompletedTensor l E X).obj ((integralDerivedPullback l E f).obj K, M)

/-- The displayed completed source tensor, with the separately derived compact support.
Source: blueprint direct-image proof (3)
(blueprint: lem-pur-compactification-b-projection-reduction). -/
def completedSource {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : CompleteProjectionDescent.Integral l E Y)
    (M : CompleteProjectionDescent.Integral l E X) :=
  (integralCompletedTensor l E Y).obj (K, (integralImage l E c).obj M)

/-- The actual map from the ordinary inner tensor to D, using the normalized
completion comparisons for tensor and pullback.
Source: blueprint direct-image proof (3)
(blueprint: lem-pur-compactification-b-projection-reduction). -/
def innerUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : CompleteProjectionDescent.Integral l E Y)
    (M : CompleteProjectionDescent.Integral l E X) :=
  ((m.integral.tensor X).chi l E).app ((ringedPull l E f).obj K, M) ≫
    (integralCompletedTensor l E X).map
      (Prod.mkHom (((m.integral.pull f).unit l E).app K) (𝟙 M))

/-- The tensor quotient-unit comparison to the displayed completed source.
Source: blueprint direct-image proof (3)
(blueprint: lem-pur-compactification-b-projection-reduction). -/
def sourceUnit {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : CompleteProjectionDescent.Integral l E Y)
    (M : CompleteProjectionDescent.Integral l E X) :=
  ((m.integral.tensor Y).chi l E).app (K, (integralImage l E c).obj M)

/-- Proper counit/open unit projection with its two specified tensor symmetries.
Source: blueprint tower-gamma proof (2), tensor transpose
(blueprint: lem-pur-compactification-b-projection-reduction). -/
def ordinaryAlpha {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : CompleteProjectionDescent.Integral l E Y)
    (M : CompleteProjectionDescent.Integral l E X) :=
  (integralSymmetry l E Y (m.integral.tensor Y).ordinary).hom.app
      (K, (integralImage l E c).obj M) ≫
    ringedCompactificationProjection l E m.integral m.openIntegral c M K ≫
    (integralImage l E c).map
      ((integralSymmetry l E X (m.integral.tensor X).ordinary).hom.app
        (M, (ringedPull l E f).obj K))

/-- The same coefficient-first projection on whole systems.
Source: blueprint tower-gamma proof (2)
(blueprint: lem-pur-compactification-b-projection-reduction). -/
def systemAlpha {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : CompleteProjectionDescent.System l E Y)
    (M : CompleteProjectionDescent.System l E X)
    (hOpen : IsIso (systemOpenInverse l E m c.i M
      ((VaryingRing.G (rings l E) (transitions l E) c.g).obj K))) :=
  (systemSymmetry l E m Y).hom.app (K, (systemImage l E c).obj M) ≫
    systemProjection l E m c M K hOpen ≫
    (systemImage l E c).map ((systemSymmetry l E m X).hom.app
      (M, (VaryingRing.G (rings l E) (transitions l E) f).obj K))

/-- The actual completed projection, across the source and inner completion units.
Source: blueprint direct-image proof (3), completed adjunction normalization
(blueprint: lem-pur-compactification-b-projection-reduction). -/
def alpha {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : CompleteProjectionDescent.Integral l E Y)
    (M : CompleteProjectionDescent.Integral l E X)
    (v : ordinarySource l E m c K M ≅
      completedSource l E c K M)
    (h : ordinaryInner l E m f K M ≅
      completedInner l E f K M) :=
  v.inv ≫ ordinaryAlpha l E m c K M ≫ (integralImage l E c).map h.hom

/-- Simultaneous reduction of the completed inner tensor and pullback.
Source: blueprint direct-image proof (3), quotient augmentation coordinates
(blueprint: lem-pur-compactification-b-projection-reduction). -/
def q {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : CompleteProjectionDescent.Integral l E Y)
    (M : CompleteProjectionDescent.Integral l E X)
    (h : ordinaryInner l E m f K M ≅
      completedInner l E f K M) :=
  (red l E m X).map h.inv ≫
    (m.tensor X).hom.app ((ringedPull l E f).obj K, M) ≫
    (m.systems X).closed.tensor.map (Prod.mkHom ((m.pull f).hom.app K) (𝟙 _))

/-- Simultaneous source reduction, followed by identity tensor the pinned b_M.
Source: blueprint direct-image proof (2)--(3)
(blueprint: lem-pur-compactification-b-projection-reduction). -/
def s {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (AX : SpNormalizedEquivalence l E X (m.abelian X) (m.red X))
    (AZ : SpNormalizedEquivalence l E c.Z (m.abelian c.Z) (m.red c.Z))
    (AY : SpNormalizedEquivalence l E Y (m.abelian Y) (m.red Y))
    (K : CompleteProjectionDescent.Integral l E Y)
    (M : CompleteProjectionDescent.Integral l E X)
    (v : ordinarySource l E m c K M ≅
      completedSource l E c K M) :=
  (red l E m Y).map v.inv ≫
    (m.tensor Y).hom.app (K, (integralImage l E c).obj M) ≫
    (m.systems Y).closed.tensor.map
      (Prod.mkHom (𝟙 _) (reconstruction l E m c AX AZ AY M))

/-- Normalized constructible membership transported through the canonical
strict-system/sequence-site equivalence, retaining its full derived morphisms.
Source: blueprint direct-image proof (1)
(blueprint: lem-pur-compactification-b-projection-reduction). -/
def normalized (T : Scheme.{u}) (N : CompleteProjectionDescent.System l E T) : Prop :=
  spNormalizedConstructibleTorTowers l E T (m.abelian T)
    ((derivedTowerEquivalence l E T (m.abelian T)).inverse.obj N)

```

## New

The exact same signatures and bodies, reproduced above, are declared in
Sheaf.Paper.CompactificationBProjectionData and publicly re-exported by
Sheaf.Paper.CompactificationBProjectionReduction. Only their blueprint tags
change to the new definition node. The original public import list is narrowed
to the presentation, finite-field datum, finite-Tor categories and smoothness.
The presentation imports CompleteProjectionMateDescent and
ShiftedTensorMorphismCalculus publicly. The split lemmas are private proof
imports of the original module.

## Users

When the split was first delivered, `tools/downstream.py` reported no downstream
modules. Since then three modules have landed that use the moved names
(innerUnit, sourceUnit, alpha, q, s) through
`public import Sheaf.Paper.CompactificationBProjectionReduction`:

- Sheaf.Paper.TowerPurityRealizedData (direct importer; claimed by nobody)
- Sheaf.Paper.TowerPurityRealizedNormalization (through TowerPurityRealizedData; claimed by nobody)
- Sheaf.Paper.TowerPurityRealizedTranspose (through TowerPurityRealizedData; claimed by nobody)

They need no adaptation: the original module re-exports all 17 names, with
identical signatures and bodies, through its public import of
Sheaf.Paper.CompactificationBProjectionData. The independent review compiled all
three, unchanged, against the delivered modules (lcompile, exit 0, 2026-10-26).
The DAG still attaches the completed projection theorem to the original module;
the new definition node attaches all 17 moved names to their new module.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompactificationBProjectionReduction | Z7 | Exact definitions re-exported; proof uses two strict subclaims. |
| Sheaf.Paper.CompactificationBProjectionData | Z7 (new) | Owns unchanged coordinates and signed symmetries. |
| Sheaf.Paper.CompactificationBProjectionDomains | Z7 (new) | Uses coordinates for membership and unit assertions. |
| Sheaf.Paper.CompactificationBOrdinaryProjectionSquare | Z7 (new) | Uses ordinary coordinates for a smaller square. |

## Status

landed 20261026T022728-L-405116 2026-10-26 (merge of deliver/A3/Sheaf.Paper.CompactificationBProjectionReduction)
