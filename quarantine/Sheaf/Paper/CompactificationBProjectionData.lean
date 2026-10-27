/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.Paper.CompleteProjectionMateDescent
public import Sheaf.Paper.ShiftedTensorMorphismCalculus

/-! # Coordinates for compactification projection reduction

Source: current blueprint, integral-adjunction-direct-image.proof.md (1)--(3)
and tower-geometric-gamma.proof.md (2)
(blueprint: def-pur-compactification-b-projection-data).

These are the original projection coordinates, moved without changing any
signature or body. The maps live in derived categories of entire systems.
Reconstruction is reduction of compactificationLimit followed by its actual
counit. The completion units and signed tensor symmetries retain their published
quotient and total-complex normalizations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures WeilConjectures.IntegralSystemRealization

namespace AlgebraicGeometry.ProEtale.CompactificationBProjection
open CompleteProjectionDescent

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The published signed tensor symmetry on an ordinary integral tensor presentation.
Source: blueprint direct-image proof (3), tensor order
(blueprint: def-pur-compactification-b-projection-data). -/
def integralSymmetry (T : Scheme.{u})
    (a : Scheme.ProEtaleTensorModel T ((PurCompactSupport.completed l E).ring T)) :=
  SheafOfModules.derivedTensorSymmetry.{u + 1, u, u + 2} ((PurCompactSupport.completed l E).ring T)
    ({ tensor := a.tensor, representative := a.representative } :
      SheafOfModules.ShiftedTensorModel.{u + 1, u, u + 2}
        ((PurCompactSupport.completed l E).ring T))

/-- The actual coefficient ring sheaf on the ell-power sequence site.
Source: blueprint direct-image proof (3)
(blueprint: def-pur-compactification-b-projection-data). -/
abbrev systemRing (T : Scheme.{u}) :=
  SemilinearSections.systemRing (Scheme.ProEt.topology T)
    (VaryingRing.coefficients (rings l E) T)
    (VaryingRing.coefficientTransition (rings l E) (transitions l E) T)

/-- Forget only termwise flatness in the existing resolving category.
Source: Stacks 06YU, blueprint direct-image proof (3)
(blueprint: def-pur-compactification-b-projection-data). -/
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
(blueprint: def-pur-compactification-b-projection-data). -/
def systemTensorModel (m : DescentModels l E) (T : Scheme.{u}) :
    SheafOfModules.ShiftedTensorModel.{u + 1, u, u + 2} (systemRing l E T) where
  tensor := (m.systems T).closed.tensor
  representative := Functor.isoWhiskerLeft
    ((resolvingInclusion l E T).prod (resolvingInclusion l E T))
    (m.systems T).tensorModels.comparison

/-- The canonical Koszul symmetry of the entire-system tensor.
Source: blueprint direct-image proof (3)
(blueprint: def-pur-compactification-b-projection-data). -/
def systemSymmetry (m : DescentModels l E) (T : Scheme.{u}) :=
  SheafOfModules.derivedTensorSymmetry.{u + 1, u, u + 2}
    (systemRing l E T) (systemTensorModel l E m T)

variable (m : DescentModels l E)

/-- The coefficient-first ordinary inner tensor; completing it also completes
its pullback factor, with the canonical completion-unit identification.
Source: blueprint direct-image proof (3)
(blueprint: def-pur-compactification-b-projection-data). -/
def ordinaryInner {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : CompleteProjectionDescent.Integral l E Y)
    (M : CompleteProjectionDescent.Integral l E X) :=
  (m.integral.tensor X).ordinary.tensor.obj ((ringedPull l E f).obj K, M)

/-- The coefficient-first ordinary source tensor.
Source: blueprint direct-image proof (3)
(blueprint: def-pur-compactification-b-projection-data). -/
def ordinarySource {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : CompleteProjectionDescent.Integral l E Y)
    (M : CompleteProjectionDescent.Integral l E X) :=
  (m.integral.tensor Y).ordinary.tensor.obj (K, (integralImage l E c).obj M)

/-- The displayed D uses the published completed pullback and completed tensor.
Source: blueprint direct-image proof (3)
(blueprint: def-pur-compactification-b-projection-data). -/
def completedInner {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : CompleteProjectionDescent.Integral l E Y)
    (M : CompleteProjectionDescent.Integral l E X) :=
  (integralCompletedTensor l E X).obj ((integralDerivedPullback l E f).obj K, M)

/-- The displayed completed source tensor, with the separately derived compact support.
Source: blueprint direct-image proof (3)
(blueprint: def-pur-compactification-b-projection-data). -/
def completedSource {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : CompleteProjectionDescent.Integral l E Y)
    (M : CompleteProjectionDescent.Integral l E X) :=
  (integralCompletedTensor l E Y).obj (K, (integralImage l E c).obj M)

/-- The actual map from the ordinary inner tensor to D, using the normalized
completion comparisons for tensor and pullback.
Source: blueprint direct-image proof (3)
(blueprint: def-pur-compactification-b-projection-data). -/
def innerUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : CompleteProjectionDescent.Integral l E Y)
    (M : CompleteProjectionDescent.Integral l E X) :=
  ((m.integral.tensor X).chi l E).app ((ringedPull l E f).obj K, M) ≫
    (integralCompletedTensor l E X).map
      (Prod.mkHom (((m.integral.pull f).unit l E).app K) (𝟙 M))

/-- The tensor quotient-unit comparison to the displayed completed source.
Source: blueprint direct-image proof (3)
(blueprint: def-pur-compactification-b-projection-data). -/
def sourceUnit {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : CompleteProjectionDescent.Integral l E Y)
    (M : CompleteProjectionDescent.Integral l E X) :=
  ((m.integral.tensor Y).chi l E).app (K, (integralImage l E c).obj M)

/-- Proper counit/open unit projection with its two specified tensor symmetries.
Source: blueprint tower-gamma proof (2), tensor transpose
(blueprint: def-pur-compactification-b-projection-data). -/
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
(blueprint: def-pur-compactification-b-projection-data). -/
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
(blueprint: def-pur-compactification-b-projection-data). -/
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
(blueprint: def-pur-compactification-b-projection-data). -/
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
(blueprint: def-pur-compactification-b-projection-data). -/
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
(blueprint: def-pur-compactification-b-projection-data). -/
def normalized (T : Scheme.{u}) (N : CompleteProjectionDescent.System l E T) : Prop :=
  spNormalizedConstructibleTorTowers l E T (m.abelian T)
    ((derivedTowerEquivalence l E T (m.abelian T)).inverse.obj N)

end AlgebraicGeometry.ProEtale.CompactificationBProjection
