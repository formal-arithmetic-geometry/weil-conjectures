/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Standing.StandingExceptionalBaseChangeCompared
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessFiniteComparison
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteExceptionalComposition
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessTheorem
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.ProperBaseChange.IntegralFinitePullbackComposition
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.CompUnit
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided

import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange
import WeilConjectures.EtaleCohomology.Purity.Smooth.SectionInvariantCtf
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import WeilConjectures.AlgebraicGeometry.Tensor.TensorMateBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsCoherence
import all WeilConjectures.AlgebraicGeometry.Section.SectionExceptionalFibreCoherence
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement

/-! # Smooth exceptional base-change and tensor pasting

Source: main-20261015, thm-pur-composition-coherence.proof.md, Step 1,
remaining smooth-base-change constituents
(blueprint: lem-pur-smooth-exceptional-tensor-pasting).

All equations are in the canonical etale-origin coordinates of the recorded
cohomological-smoothness definition. Their images under comparison pullback are
morphisms on the small pro-etale site. Every Dctf object has such a representative;
canonical pullback, tensor and compact-support comparisons identify the displayed
maps with the specified counit transposes. No orientation is selected.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u uA
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.SmoothExceptionalPasting

-- Keep the published sheaf tensor structure opaque during type comparison.
attribute [local instance high] SymmetricCategory.toBraidedCategory
  HomologicalComplex.monoidalCategory
attribute [local irreducible] Sheaf.monoidalCategory
  _root_.DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
attribute [local instance 20000] Etale.sheafMonoidalCategory
  Etale.sheafBraidedCategory Etale.sheafMonoidalClosed
  Sheaf.monoidalPreadditive instMonoidalCategoryHomologicalComplexIntUp_weilConjectures
set_option backward.defeqAttrib.useBackward true

/-- The existing ordinary etale derived category, used only as coordinates for nu^*.
Source: main-20261015, thm-pur-composition-coherence, Step 1
(blueprint: lem-pur-smooth-exceptional-tensor-pasting). -/
abbrev D (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u}) : Type (u + 2) :=
  _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))

/-- The recorded derived pullback in etale-origin coordinates.
Source: main-20261015, thm-pur-composition-coherence, Step 1
(blueprint: lem-pur-smooth-exceptional-tensor-pasting). -/
abbrev L (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) : D Λ Y ⥤ D Λ X :=
  (Etale.upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor

/-- The recorded exceptional inverse image in etale-origin coordinates.
Source: main-20261015, thm-pur-composition-coherence, Step 1
(blueprint: lem-pur-smooth-exceptional-tensor-pasting). -/
abbrev R (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] : D Λ Y ⥤ D Λ X :=
  Etale.rightDerivedUpperShriek Λ f

/-- The canonical comparison inverse image to the actual small pro-etale site.
Source: main-20261015, thm-pur-composition-coherence, Step 1
(blueprint: lem-pur-smooth-exceptional-tensor-pasting). -/
abbrev V (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u}) :
    D Λ X ⥤ _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :=
  (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory

/-- The existing finite-Tor domain, tested on the comparison image. This quantifies
all representatives of all pro-etale Dctf objects, with no selected origin witness.
Source: main-20261015, thm-pur-composition-coherence, Step 1
(blueprint: lem-pur-smooth-exceptional-tensor-pasting). -/
abbrev Ctf (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (X : Scheme.{u}) (K : D Λ X) : Prop :=
  DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
    ((V Λ X).obj K)

/-- sigma = c_Lambda inverse after theta and symmetry. The recorded etale theta
has source omega_f tensor f^*M, so its ordering has already absorbed the symmetry
in the node's definition. In particular there is no extra choice of a compositor.
Source: main-20261015, thm-pur-composition-coherence, Step 1
(blueprint: lem-pur-smooth-exceptional-tensor-pasting). -/
def sigma (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact (f ≫ g)] :
    ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj
      (Etale.dualizingComplex Λ f)).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor.obj
          (Etale.dualizingComplex Λ g)) ⟶
      Etale.dualizingComplex Λ (f ≫ g) :=
  Etale.dualizingComplexTensorMap Λ f
      (Etale.dualizingComplex Λ g) ≫
    (WeilConjectures.PurityFiniteSetting.finiteExceptionalComposition
      Λ f g).inv.app (𝟙_ _)

/-- The single-square assertions: unit normalization, invertibility at K, and
the existing exact tensor/base-change equation. Nagata is derived from the field
hypotheses inside this definition; it is not a new assumption.
Source: main-20261015, thm-pur-composition-coherence.proof.md, Step 1
(blueprint: lem-pur-smooth-exceptional-tensor-pasting). -/
def squareClause
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X₁ X Y₁ Y : Scheme.{u}}
    [X₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₁ ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₁ ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (h : X ⟶ Y) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (h₁ : X₁ ⟶ Y₁) [h₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated h₁] [LocallyOfFiniteType h₁] [QuasiCompact h₁]
    (u₁ : X₁ ⟶ X) [u₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated u₁] [LocallyOfFiniteType u₁] [QuasiCompact u₁]
    (v : Y₁ ⟶ Y) [v.IsOver (Spec (.of P.field.k))]
    [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    (sq : IsPullback u₁ h₁ h v) (K : D Λ Y) : Prop :=
  letI := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of P.field.k))
  letI := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of P.field.k))
  letI := LocallyOfFiniteType.isLocallyNoetherian (Y₁ ↘ Spec (.of P.field.k))
  letI := QuasiCompact.compactSpace_of_compactSpace (Y₁ ↘ Spec (.of P.field.k))
  IsIso ((V Λ X₁).map ((Etale.rightDerivedUpperShriekBaseChangeMap Λ sq).app K)) ∧
    (V Λ X₁).map
      ((Etale.rightDerivedUpperShriekBaseChangeMap Λ sq).app (𝟙_ _) ≫
        (R Λ h₁).map (Etale.leftDerivedUpperStarUnitIso
          (ModuleCat.{u + 1} Λ) v).hom) =
      (V Λ X₁).map (Etale.dualizingComplexBaseChangeMap Λ sq) ∧
    smoothTensorBaseChangeCoherence Λ sq K

/-- Smooth exceptional base change, its value at the unit, and tensor compatibility.
K ranges over every etale representative of an object of pro-etale Dctf.
Source: main-20261015, thm-pur-composition-coherence.proof.md, Step 1
(blueprint: lem-pur-smooth-exceptional-tensor-pasting).

Proof: Finite type and quasi-compactness over the coefficient field give
Noetherian schemes and the Nagata compactifications. The finite compared
invertible exponent lets us apply the proved smooth exceptional base-change
isomorphism theorem. Comparison pullback preserves that isomorphism. Its value
at the coefficient unit is the specified beta by definition. The final tensor
identity is exactly the existing tensorMateBaseChange dependency. No orientation
or additional representative is chosen. -/
theorem smoothExceptionalTensorPasting
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X₁ X Y₁ Y : Scheme.{u}}
    [X₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₁ ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₁ ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (h : X ⟶ Y) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (h₁ : X₁ ⟶ Y₁) [h₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated h₁] [LocallyOfFiniteType h₁] [QuasiCompact h₁]
    (u₁ : X₁ ⟶ X) [u₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated u₁] [LocallyOfFiniteType u₁] [QuasiCompact u₁]
    (v : Y₁ ⟶ Y) [v.IsOver (Spec (.of P.field.k))]
    [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    (sq : IsPullback u₁ h₁ h v) (K : D P.Coefficient Y)
    (d d₁ : ℕ) [SmoothOfRelativeDimension d h] [SmoothOfRelativeDimension d₁ h₁]
    (_hK : Ctf P.Coefficient Y K) :
    squareClause P P.Coefficient h h₁ u₁ v sq K := by
  let := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of P.field.k))
  let := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of P.field.k))
  let : IsNoetherian Y := { }
  let := LocallyOfFiniteType.isLocallyNoetherian (Y₁ ↘ Spec (.of P.field.k))
  let := QuasiCompact.compactSpace_of_compactSpace (Y₁ ↘ Spec (.of P.field.k))
  let : IsNoetherian Y₁ := { }
  let := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of P.field.k))
  let := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of P.field.k))
  let : IsNoetherian X := { }
  let := LocallyOfFiniteType.isLocallyNoetherian (X₁ ↘ Spec (.of P.field.k))
  let := QuasiCompact.compactSpace_of_compactSpace (X₁ ↘ Spec (.of P.field.k))
  let : IsNoetherian X₁ := { }
  let := P.finiteComparedInvertibleExponent (X ↘ Spec (.of P.field.k))
  have := Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension
    P.Coefficient h d sq
  refine ⟨?_, ?_, ?_⟩
  · infer_instance
  · rfl
  · exact (tensorMateBaseChange P sq (HasCompactification.compactification h)).2.2 K _hK

attribute [local irreducible] Etale.upperStar
  HasDerivedCategory.ofIsGrothendieckAbelian

private theorem exceptional_base_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian X'']
    [IsNoetherian Y] [IsNoetherian Y'] [IsNoetherian Y'']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {v : Y' ⟶ Y} {w : Y'' ⟶ Y'} {v' : X' ⟶ X} {w' : X'' ⟶ X'}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
    [QuasiCompact f'] [QuasiCompact f'']
    (sq₁ : IsPullback v' f' f v) (sq₂ : IsPullback w' f'' f' w)
    (K : D A Y)
    (z : X'' ⟶ X) (b : Y'' ⟶ Y)
    (hz : z = w' ≫ v') (hb : b = w ≫ v)
    (sq : IsPullback z f'' f b) :
    (Etale.rightDerivedUpperShriekBaseChangeMap A sq).app K =
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w' v' z hz).hom.app
        ((Etale.rightDerivedUpperShriek A f).obj K) ≫
      (Etale.upperStar (ModuleCat.{u + 1} A) w').leftDerivedFunctor.map
        ((Etale.rightDerivedUpperShriekBaseChangeMap A sq₁).app K) ≫
      (Etale.rightDerivedUpperShriekBaseChangeMap A sq₂).app
        ((Etale.upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.obj K) ≫
      (Etale.rightDerivedUpperShriek A f'').map
        ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w v b hb).inv.app K) := by
  subst hz hb
  exact Etale.exceptional_base_comp A sq₁ sq₂ K

/-- Successive changes of base, with both pullback compositors displayed.
This is B_(h,vw) = B_(h1,w) after u2^* B_(h,v).
Source: main-20261015, thm-pur-composition-coherence.proof.md, Step 1
(blueprint: lem-pur-smooth-exceptional-tensor-pasting). -/
def basePastingClause
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X₂ X₁ X Y₂ Y₁ Y : Scheme.{u}}
    [X₂.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₂ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₂ ↘ Spec (.of P.field.k))]
    [X₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₁ ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y₂.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₂ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₂ ↘ Spec (.of P.field.k))]
    [Y₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₁ ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (h : X ⟶ Y) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (h₁ : X₁ ⟶ Y₁) [h₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated h₁] [LocallyOfFiniteType h₁] [QuasiCompact h₁]
    (h₂ : X₂ ⟶ Y₂) [h₂.IsOver (Spec (.of P.field.k))]
    [IsSeparated h₂] [LocallyOfFiniteType h₂] [QuasiCompact h₂]
    (u₁ : X₁ ⟶ X) [u₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated u₁] [LocallyOfFiniteType u₁] [QuasiCompact u₁]
    (u₂ : X₂ ⟶ X₁) [u₂.IsOver (Spec (.of P.field.k))]
    [IsSeparated u₂] [LocallyOfFiniteType u₂] [QuasiCompact u₂]
    (v : Y₁ ⟶ Y) [v.IsOver (Spec (.of P.field.k))]
    [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    (w : Y₂ ⟶ Y₁) [w.IsOver (Spec (.of P.field.k))]
    [IsSeparated w] [LocallyOfFiniteType w] [QuasiCompact w]
    (sq : IsPullback u₁ h₁ h v) (sq₁ : IsPullback u₂ h₂ h₁ w) (K : D Λ Y) : Prop :=
  letI := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of P.field.k))
  letI := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of P.field.k))
  letI := LocallyOfFiniteType.isLocallyNoetherian (Y₁ ↘ Spec (.of P.field.k))
  letI := QuasiCompact.compactSpace_of_compactSpace (Y₁ ↘ Spec (.of P.field.k))
  letI := LocallyOfFiniteType.isLocallyNoetherian (Y₂ ↘ Spec (.of P.field.k))
  letI := QuasiCompact.compactSpace_of_compactSpace (Y₂ ↘ Spec (.of P.field.k))
  (V Λ X₂).map
      ((Etale.rightDerivedUpperShriekBaseChangeMap Λ (sq₁.paste_horiz sq)).app K ≫
        (R Λ h₂).map ((Etale.leftDerivedUpperStarComp
          (ModuleCat.{u + 1} Λ) w v).hom.app K)) =
    (V Λ X₂).map
      ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) u₂ u₁).hom.app
          ((R Λ h).obj K) ≫
        (L Λ u₂).map ((Etale.rightDerivedUpperShriekBaseChangeMap Λ sq).app K) ≫
        (Etale.rightDerivedUpperShriekBaseChangeMap Λ sq₁).app ((L Λ v).obj K))

/-- Pasting along the direction of base change, including all pullback comparisons.
Source: main-20261015, thm-pur-composition-coherence.proof.md, Step 1
(blueprint: lem-pur-smooth-exceptional-tensor-pasting).

Proof: Use the proved horizontal exceptional-base-change calculation from
SectionExceptionalFibreCoherence, with the canonical composite arrows. This is
the mate of the normalized compact-support exchange-pasting equation. Compose
with the target pullback compositor, cancel its inverse, and apply the specified
comparison functor. The resulting equation has exactly the displayed sources
and targets. -/
theorem smoothExceptionalBasePasting
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X₂ X₁ X Y₂ Y₁ Y : Scheme.{u}}
    [X₂.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₂ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₂ ↘ Spec (.of P.field.k))]
    [X₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₁ ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y₂.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₂ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₂ ↘ Spec (.of P.field.k))]
    [Y₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₁ ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (h : X ⟶ Y) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (h₁ : X₁ ⟶ Y₁) [h₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated h₁] [LocallyOfFiniteType h₁] [QuasiCompact h₁]
    (h₂ : X₂ ⟶ Y₂) [h₂.IsOver (Spec (.of P.field.k))]
    [IsSeparated h₂] [LocallyOfFiniteType h₂] [QuasiCompact h₂]
    (u₁ : X₁ ⟶ X) [u₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated u₁] [LocallyOfFiniteType u₁] [QuasiCompact u₁]
    (u₂ : X₂ ⟶ X₁) [u₂.IsOver (Spec (.of P.field.k))]
    [IsSeparated u₂] [LocallyOfFiniteType u₂] [QuasiCompact u₂]
    (v : Y₁ ⟶ Y) [v.IsOver (Spec (.of P.field.k))]
    [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    (w : Y₂ ⟶ Y₁) [w.IsOver (Spec (.of P.field.k))]
    [IsSeparated w] [LocallyOfFiniteType w] [QuasiCompact w]
    (sq : IsPullback u₁ h₁ h v) (sq₁ : IsPullback u₂ h₂ h₁ w) (K : D P.Coefficient Y)
    (d d₁ d₂ : ℕ) [SmoothOfRelativeDimension d h]
    [SmoothOfRelativeDimension d₁ h₁] [SmoothOfRelativeDimension d₂ h₂]
    (_hK : Ctf P.Coefficient Y K) :
    basePastingClause P P.Coefficient h h₁ h₂ u₁ u₂ v w sq sq₁ K := by
  let := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of P.field.k))
  let := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of P.field.k))
  let : IsNoetherian X := { }
  let := LocallyOfFiniteType.isLocallyNoetherian (X₁ ↘ Spec (.of P.field.k))
  let := QuasiCompact.compactSpace_of_compactSpace (X₁ ↘ Spec (.of P.field.k))
  let : IsNoetherian X₁ := { }
  let := LocallyOfFiniteType.isLocallyNoetherian (X₂ ↘ Spec (.of P.field.k))
  let := QuasiCompact.compactSpace_of_compactSpace (X₂ ↘ Spec (.of P.field.k))
  let : IsNoetherian X₂ := { }
  let := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of P.field.k))
  let := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of P.field.k))
  let : IsNoetherian Y := { }
  let := LocallyOfFiniteType.isLocallyNoetherian (Y₁ ↘ Spec (.of P.field.k))
  let := QuasiCompact.compactSpace_of_compactSpace (Y₁ ↘ Spec (.of P.field.k))
  let : IsNoetherian Y₁ := { }
  let := LocallyOfFiniteType.isLocallyNoetherian (Y₂ ↘ Spec (.of P.field.k))
  let := QuasiCompact.compactSpace_of_compactSpace (Y₂ ↘ Spec (.of P.field.k))
  let : IsNoetherian Y₂ := { }
  apply congrArg ((V P.Coefficient X₂).map)
  rw [exceptional_base_comp P.Coefficient sq sq₁ K
    (u₂ ≫ u₁) (w ≫ v) rfl rfl (sq₁.paste_horiz sq)]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

private lemma identity_exchange_of_pasting
    {D E : Type*} [Category D] [Category E]
    (F : D ⥤ E) (I : D ⥤ D) (J : E ⥤ E)
    (C : F ⋙ J ⟶ I ⋙ F) [IsIso C]
    (e : I ≅ 𝟭 D) (d : J ≅ 𝟭 E) (δ : I ≅ I ⋙ I) (ε : J ≅ J ⋙ J)
    (hδ : δ.hom ≫ Functor.whiskerLeft I e.hom = 𝟙 _)
    (hε : ε.hom ≫ Functor.whiskerLeft J d.hom = 𝟙 _)
    (hp : ∀ K, C.app K = ε.hom.app (F.obj K) ≫ J.map (C.app K) ≫
      C.app (I.obj K) ≫ F.map (δ.inv.app K)) :
    C ≫ Functor.whiskerRight e.hom F ≫ (Functor.leftUnitor F).hom =
      Functor.whiskerLeft F d.hom ≫ (Functor.rightUnitor F).hom := by
  exact Etale.identity_exchange_of_pasting F I J C e d δ ε hδ hε hp

/-- The identity-square normalization with canonical derived identity pullbacks.
Source: main-20261015, thm-pur-composition-coherence.proof.md, Step 1
(blueprint: lem-pur-smooth-exceptional-tensor-pasting). -/
def identityClause
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (h : X ⟶ Y) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (K : D Λ Y) : Prop :=
  letI := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of P.field.k))
  letI := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of P.field.k))
  (V Λ X).map
      ((Etale.rightDerivedUpperShriekBaseChangeMap Λ
        (IsPullback.of_id_fst (f := h))).app K ≫
        (R Λ h).map ((Etale.leftDerivedUpperStarId
          (ModuleCat.{u + 1} Λ) Y).hom.app K)) =
    (V Λ X).map ((Etale.leftDerivedUpperStarId
      (ModuleCat.{u + 1} Λ) X).hom.app ((R Λ h).obj K))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The identity-base-change value of B is the identity after canonical normalization.
Source: main-20261015, thm-pur-composition-coherence.proof.md, Step 1
(blueprint: lem-pur-smooth-exceptional-tensor-pasting).

Proof: Apply the proved identity_exchange_of_pasting calculation to horizontal
pasting of the identity square. Invertibility and the canonical pullback
composition/identity equations normalize this exchange. Evaluate the resulting
natural-transformation equality at K and apply the comparison functor. -/
theorem smoothExceptionalIdentityPasting
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (h : X ⟶ Y) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (K : D P.Coefficient Y) (d : ℕ) [SmoothOfRelativeDimension d h]
    (_hK : Ctf P.Coefficient Y K) : identityClause P P.Coefficient h K := by
  let := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of P.field.k))
  let := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of P.field.k))
  let : IsNoetherian X := { }
  let := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of P.field.k))
  let := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of P.field.k))
  let : IsNoetherian Y := { }
  let := P.finiteComparedInvertibleExponent (X ↘ Spec (.of P.field.k))
  let sq := IsPullback.of_id_fst (f := h)
  have := Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension
    P.Coefficient h d sq
  have hc := identity_exchange_of_pasting (R P.Coefficient h)
    (L P.Coefficient (𝟙 Y)) (L P.Coefficient (𝟙 X))
    (Etale.rightDerivedUpperShriekBaseChangeMap P.Coefficient sq)
    (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) Y)
    (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) X)
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      (𝟙 Y) (𝟙 Y) (𝟙 Y) (Category.id_comp _).symm)
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      (𝟙 X) (𝟙 X) (𝟙 X) (Category.id_comp _).symm)
    (by
      ext M
      exact Etale.leftDerivedUpperStarComp_id_left_hom_app
        (ModuleCat.{u + 1} P.Coefficient) (𝟙 Y) M)
    (by
      ext M
      exact Etale.leftDerivedUpperStarComp_id_left_hom_app
        (ModuleCat.{u + 1} P.Coefficient) (𝟙 X) M)
    (fun M ↦ exceptional_base_comp P.Coefficient sq sq M
      (z := 𝟙 X) (b := 𝟙 Y) (hz := (Category.id_comp _).symm)
      (hb := (Category.id_comp _).symm) (sq := sq))
  apply congrArg ((V P.Coefficient X).map)
  have hcK := NatTrans.congr_app hc K
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app] at hcK
  erw [Category.comp_id, Category.comp_id] at hcK
  exact hcK

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

private theorem compact_exchange_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' Z Z' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    [IsNoetherian Z] [IsNoetherian Z']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y ⟶ Z} {g' : Y' ⟶ Z'}
    {a : X' ⟶ X} {b : Y' ⟶ Y} {c : Z' ⟶ Z}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [QuasiCompact f'] [QuasiCompact g'] [QuasiCompact (f' ≫ g')]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [HasCompactification f'] [HasCompactification g'] [HasCompactification (f' ≫ g')]
    (sqf : IsPullback a f' f b) (sqg : IsPullback b g' g c) :
    Adjunction.ExchangeCompCompatible
      (Etale.rightDerivedLowerShriekBaseChangeMap A sqf)
      (Etale.rightDerivedLowerShriekBaseChangeMap A sqg)
      (Etale.rightDerivedLowerShriekBaseChangeMap A (sqf.paste_vert sqg))
      (Etale.unboundedEtaleLowerShriekCompIso A f g).symm
      (Etale.unboundedEtaleLowerShriekCompIso A f' g').symm := by
  constructor
  intro M
  let e := Etale.unboundedEtaleLowerShriekCompIso A f g
  let e' := Etale.unboundedEtaleLowerShriekCompIso A f' g'
  let Ja := Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) a
  let Jb := Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) b
  let Jc := Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) c
  let F := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f
  let G' := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) g'
  let H' := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f' ≫ g')
  have h := congr_app (Etale.unboundedEtaleCompactSupport_baseChange_composition
    A sqf sqg (sqf.paste_vert sqg)) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Etale.unboundedEtaleCompactSupportBaseChange, Functor.map_comp, Category.assoc] at h
  have h' : (L A c).map (e.hom.app M) ≫
      (Etale.rightDerivedLowerShriekBaseChangeMap A (sqf.paste_vert sqg)).app M =
      (Etale.rightDerivedLowerShriekBaseChangeMap A sqg).app (F.obj M) ≫
        G'.map ((Etale.rightDerivedLowerShriekBaseChangeMap A sqf).app M) ≫
          e'.hom.app ((L A a).obj M) := by
    apply (cancel_epi (Jc.inv.app ((F ⋙
      Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).obj M))).mp
    apply (cancel_mono (H'.map (Ja.hom.app M))).mp
    simp only [Category.assoc]
    erw [← reassoc_of% (Jc.inv.naturality (e.hom.app M))]
    erw [← e'.hom.naturality (Ja.hom.app M)]
    simp only [Functor.comp_map]
    simp only [← Functor.map_comp_assoc] at h
    erw [Iso.hom_inv_id_app_assoc] at h
    simpa only [Functor.map_comp, Category.assoc, F, G', H', Ja, Jc, e, e',
      Functor.comp_obj] using h
  change (L A c).map (e.inv.app M) ≫ _ = _ ≫ e'.inv.app _
  apply (cancel_epi ((L A c).map (e.hom.app M))).mp
  apply (cancel_mono (e'.hom.app ((L A a).obj M))).mp
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  exact h'.symm

private theorem rightAdjointUniq_ofNatIsoLeft_hom
    {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R R' : D ⥤ C} (adj : L ⊣ R) (adj' : L' ⊣ R') (e : L ≅ L') :
    (Adjunction.rightAdjointUniq (adj.ofNatIsoLeft e) adj').hom =
      conjugateEquiv adj adj' e.inv := by
  ext X
  simp only [Adjunction.rightAdjointUniq, conjugateIsoEquiv_apply_hom,
    conjugateEquiv_apply_app, Adjunction.ofNatIsoLeft_counit,
    NatTrans.comp_app, Functor.map_comp, Iso.refl_hom, NatTrans.id_app,
    Functor.whiskerLeft_app]
  erw [R'.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exceptional_tower_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' Z Z' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    [IsNoetherian Z] [IsNoetherian Z']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y ⟶ Z} {g' : Y' ⟶ Z'}
    {a : X' ⟶ X} {b : Y' ⟶ Y} {c : Z' ⟶ Z}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [QuasiCompact f'] [QuasiCompact g'] [QuasiCompact (f' ≫ g')]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [HasCompactification f'] [HasCompactification g'] [HasCompactification (f' ≫ g')]
    (sqf : IsPullback a f' f b) (sqg : IsPullback b g' g c) (K : D A Z) :
    (Etale.rightDerivedUpperShriekBaseChangeMap A (sqf.paste_vert sqg)).app K ≫
        (WeilConjectures.PurityFiniteSetting.finiteExceptionalComposition A f' g').hom.app
          ((L A c).obj K) =
      (L A a).map
          ((WeilConjectures.PurityFiniteSetting.finiteExceptionalComposition A f g).hom.app K) ≫
        (Etale.rightDerivedUpperShriekBaseChangeMap A sqf).app ((R A g).obj K) ≫
          (R A f').map ((Etale.rightDerivedUpperShriekBaseChangeMap A sqg).app K) := by
  have := Etale.isIso_rightDerivedLowerShriekBaseChangeMap A sqf
  have := Etale.isIso_rightDerivedLowerShriekBaseChangeMap A sqg
  have := Etale.isIso_rightDerivedLowerShriekBaseChangeMap A (sqf.paste_vert sqg)
  have h := Adjunction.mateEquiv_inv_comp_rightAdjointUniq
    (Etale.rightDerivedUpperShriekAdjunction _ f)
    (Etale.rightDerivedUpperShriekAdjunction _ g)
    (Etale.rightDerivedUpperShriekAdjunction _ (f ≫ g))
    (Etale.rightDerivedUpperShriekAdjunction _ f')
    (Etale.rightDerivedUpperShriekAdjunction _ g')
    (Etale.rightDerivedUpperShriekAdjunction _ (f' ≫ g'))
    (Etale.rightDerivedLowerShriekBaseChangeMap A sqf)
    (Etale.rightDerivedLowerShriekBaseChangeMap A sqg)
    (Etale.rightDerivedLowerShriekBaseChangeMap A (sqf.paste_vert sqg))
    (Etale.unboundedEtaleLowerShriekCompIso A f g).symm
    (Etale.unboundedEtaleLowerShriekCompIso A f' g').symm
    (compact_exchange_comp A sqf sqg) K
  simp only [rightAdjointUniq_ofNatIsoLeft_hom, Iso.symm_inv] at h
  simpa only [Etale.rightDerivedUpperShriekBaseChangeMap,
    WeilConjectures.PurityFiniteSetting.finiteExceptionalComposition,
    conjugateIsoEquiv_apply_hom] using h.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem beta_tower_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' Z Z' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    [IsNoetherian Z] [IsNoetherian Z']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y ⟶ Z} {g' : Y' ⟶ Z'}
    {a : X' ⟶ X} {b : Y' ⟶ Y} {c : Z' ⟶ Z}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [QuasiCompact f'] [QuasiCompact g'] [QuasiCompact (f' ≫ g')]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [HasCompactification f'] [HasCompactification g'] [HasCompactification (f' ≫ g')]
    (sqf : IsPullback a f' f b) (sqg : IsPullback b g' g c) :
    Etale.dualizingComplexBaseChangeMap A (sqf.paste_vert sqg) =
      (L A a).map
          ((WeilConjectures.PurityFiniteSetting.finiteExceptionalComposition A f g).hom.app
            (𝟙_ _)) ≫
        (Etale.rightDerivedUpperShriekBaseChangeMap A sqf).app
          (Etale.dualizingComplex A g) ≫
        (R A f').map (Etale.dualizingComplexBaseChangeMap A sqg) ≫
        (WeilConjectures.PurityFiniteSetting.finiteExceptionalComposition A f' g').inv.app
          (𝟙_ _) := by
  let e' := WeilConjectures.PurityFiniteSetting.finiteExceptionalComposition A f' g'
  dsimp only [Etale.dualizingComplex, Etale.dualizingComplexBaseChangeMap]
  apply (cancel_mono (e'.hom.app (𝟙_ _))).mp
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app, Category.comp_id]
  erw [e'.hom.naturality
    (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) c).hom]
  erw [reassoc_of% (exceptional_tower_comp A sqf sqg (𝟙_ _))]
  simp only [Functor.comp_map, Functor.map_comp]

section ThetaNaturality
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local semireducible] Sheaf.monoidalCategory
  _root_.DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

private theorem theta_naturality_of_isIso
    {A : Type uA} [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [Etale.UpperStarPreservesFlat A]
    {FC : A → A → Type*} {CC : A → Type (u + 1)}
    [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    [IsIso (Etale.projectionMap A f)]
    {G : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (adj : Etale.rightDerivedLowerShriek A f ⊣ G)
    {K K' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)} (g : K ⟶ K') :
    ((Etale.derivedTensor A X).obj (G.obj (𝟙_ _))).map
        ((Etale.upperStar A f).leftDerivedFunctor.map g) ≫
        Etale.lowerShriekRightAdjointUnitTensorMap adj K' =
      Etale.lowerShriekRightAdjointUnitTensorMap adj K ≫ G.map g := by
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory
    (Sheaf X.smallEtaleTopology A)
  have : ∀ M N, IsIso (((Etale.projectionMap A f).app M).app N) :=
    fun M N ↦ by infer_instance
  have h := Adjunction.projectionTensorMap_naturality_right adj
    (fun M N ↦ ((Etale.projectionMap A f).app M).app N)
    (Etale.projectionMap_app_app_naturality_right f) (𝟙_ _) g
  dsimp only [Etale.lowerShriekRightAdjointUnitTensorMap]
  rw [← Category.assoc]
  erw [h]
  simp only [Category.assoc, ← Functor.map_comp]
  exact congrArg (fun k ↦ _ ≫ G.map k)
    (leftUnitor_naturality g)

end ThetaNaturality

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem theta_naturality
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    {K M : D A Y} (q : K ⟶ M) :
    ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
        (Etale.dualizingComplex A f)).map ((L A f).map q) ≫
      Etale.dualizingComplexTensorMap A f M =
    Etale.dualizingComplexTensorMap A f K ≫ (R A f).map q := by
  exact theta_naturality_of_isIso f (Etale.rightDerivedUpperShriekAdjunction A f) q

/-- The exceptional and dualizing tensor-composition equations for two towers.
The tensor source is first compared by monoidality and by the pullback square;
all three dualizing comparisons are the specified unit values of B.
Source: main-20261015, thm-pur-composition-coherence.proof.md, Step 1
(blueprint: lem-pur-smooth-exceptional-tensor-pasting). -/
def towerClause
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X₁ X Y₁ Y Z₁ Z : Scheme.{u}}
    [X₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₁ ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₁ ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z₁ ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (g : Y ⟶ Z) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (a : X₁ ⟶ Y₁) [a.IsOver (Spec (.of P.field.k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (b : Y₁ ⟶ Z₁) [b.IsOver (Spec (.of P.field.k))]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (u₁ : X₁ ⟶ X) [u₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated u₁] [LocallyOfFiniteType u₁] [QuasiCompact u₁]
    (v : Y₁ ⟶ Y) [v.IsOver (Spec (.of P.field.k))]
    [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    (w : Z₁ ⟶ Z) [w.IsOver (Spec (.of P.field.k))]
    [IsSeparated w] [LocallyOfFiniteType w] [QuasiCompact w]
    (sqf : IsPullback u₁ a f v) (sqg : IsPullback v b g w) (K : D Λ Z) : Prop :=
  letI := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of P.field.k))
  letI := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of P.field.k))
  letI := LocallyOfFiniteType.isLocallyNoetherian (Y₁ ↘ Spec (.of P.field.k))
  letI := QuasiCompact.compactSpace_of_compactSpace (Y₁ ↘ Spec (.of P.field.k))
  letI := LocallyOfFiniteType.isLocallyNoetherian (Z ↘ Spec (.of P.field.k))
  letI := QuasiCompact.compactSpace_of_compactSpace (Z ↘ Spec (.of P.field.k))
  letI := LocallyOfFiniteType.isLocallyNoetherian (Z₁ ↘ Spec (.of P.field.k))
  letI := QuasiCompact.compactSpace_of_compactSpace (Z₁ ↘ Spec (.of P.field.k))
  (V Λ X₁).map
      ((Etale.rightDerivedUpperShriekBaseChangeMap Λ
          (sqf.paste_vert sqg)).app K ≫
        (WeilConjectures.PurityFiniteSetting.finiteExceptionalComposition
          Λ a b).hom.app ((L Λ w).obj K)) =
    (V Λ X₁).map
      ((L Λ u₁).map ((WeilConjectures.PurityFiniteSetting.finiteExceptionalComposition
          Λ f g).hom.app K) ≫
        (Etale.rightDerivedUpperShriekBaseChangeMap Λ sqf).app ((R Λ g).obj K) ≫
        (R Λ a).map ((Etale.rightDerivedUpperShriekBaseChangeMap Λ sqg).app K)) ∧
    (V Λ X₁).map
      ((L Λ u₁).map (sigma Λ f g) ≫
        Etale.dualizingComplexBaseChangeMap Λ (sqf.paste_vert sqg)) =
    (V Λ X₁).map
      ((Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) u₁
          (Etale.dualizingComplex Λ f)
          ((L Λ f).obj
            (Etale.dualizingComplex Λ g))).hom ≫
        ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X₁).map
          (Etale.dualizingComplexBaseChangeMap Λ sqf)).app _ ≫
        ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X₁).obj
          (Etale.dualizingComplex Λ a)).map
          (Etale.derivedSquareUpperStarIsoInvApp
              (ModuleCat.{u + 1} Λ) sqf.toCommSq
              (Etale.dualizingComplex Λ g) ≫
            (L Λ a).map (Etale.dualizingComplexBaseChangeMap Λ sqg)) ≫
        sigma Λ a b)

private theorem map_iso_cancel
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {S B T : C} (e : B ≅ T) (p : S ⟶ T) {U : D} (q : F.obj T ⟶ U) :
    F.map (p ≫ e.inv) ≫ F.map e.hom ≫ q = F.map p ≫ q := by
  rw [← F.map_comp_assoc]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem map_comp_congr
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {S T U : C} {p p' : S ⟶ T} (h : F.map p = F.map p') (q : T ⟶ U) :
    F.map (p ≫ q) = F.map (p' ≫ q) := by
  simpa only [Functor.map_comp] using congrArg (fun z ↦ z ≫ F.map q) h

/-- Exceptional composition pasting and its orientation-free sigma specialization.
Source: main-20261015, thm-pur-composition-coherence.proof.md, Step 1
(blueprint: lem-pur-smooth-exceptional-tensor-pasting).

Proof: The specified unbounded compact-support compositor intertwines the
compact-support exchanges. Invert this equation and apply adjunction mate
pasting. The right-adjoint uniqueness comparison is the specified exceptional
compositor, giving the first equation. Evaluate it at the coefficient unit to
identify the beta maps. Apply tensorMateBaseChange at omega_g, which has finite
Tor amplitude by the proved smooth-dualizing result. Naturality of theta follows
from projectionTensorMap_naturality_right and leftUnitor_naturality. Substitute
these equations and cancel the compositors to obtain the sigma identity.
No twist, Tate line or orientation is used. -/
theorem smoothExceptionalTowerPasting
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X₁ X Y₁ Y Z₁ Z : Scheme.{u}}
    [X₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₁ ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₁ ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z₁ ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (g : Y ⟶ Z) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (a : X₁ ⟶ Y₁) [a.IsOver (Spec (.of P.field.k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (b : Y₁ ⟶ Z₁) [b.IsOver (Spec (.of P.field.k))]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (u₁ : X₁ ⟶ X) [u₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated u₁] [LocallyOfFiniteType u₁] [QuasiCompact u₁]
    (v : Y₁ ⟶ Y) [v.IsOver (Spec (.of P.field.k))]
    [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    (w : Z₁ ⟶ Z) [w.IsOver (Spec (.of P.field.k))]
    [IsSeparated w] [LocallyOfFiniteType w] [QuasiCompact w]
    (sqf : IsPullback u₁ a f v) (sqg : IsPullback v b g w) (K : D P.Coefficient Z)
    (df dg da db : ℕ) [SmoothOfRelativeDimension df f]
    [SmoothOfRelativeDimension dg g] [SmoothOfRelativeDimension da a]
    [SmoothOfRelativeDimension db b] (_hK : Ctf P.Coefficient Z K) :
    towerClause P P.Coefficient f g a b u₁ v w sqf sqg K := by
  let := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of P.field.k))
  let := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of P.field.k))
  let : IsNoetherian X := { }
  let := LocallyOfFiniteType.isLocallyNoetherian (X₁ ↘ Spec (.of P.field.k))
  let := QuasiCompact.compactSpace_of_compactSpace (X₁ ↘ Spec (.of P.field.k))
  let : IsNoetherian X₁ := { }
  let := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of P.field.k))
  let := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of P.field.k))
  let : IsNoetherian Y := { }
  let := LocallyOfFiniteType.isLocallyNoetherian (Y₁ ↘ Spec (.of P.field.k))
  let := QuasiCompact.compactSpace_of_compactSpace (Y₁ ↘ Spec (.of P.field.k))
  let : IsNoetherian Y₁ := { }
  let := LocallyOfFiniteType.isLocallyNoetherian (Z ↘ Spec (.of P.field.k))
  let := QuasiCompact.compactSpace_of_compactSpace (Z ↘ Spec (.of P.field.k))
  let : IsNoetherian Z := { }
  let := LocallyOfFiniteType.isLocallyNoetherian (Z₁ ↘ Spec (.of P.field.k))
  let := QuasiCompact.compactSpace_of_compactSpace (Z₁ ↘ Spec (.of P.field.k))
  let : IsNoetherian Z₁ := { }
  constructor
  · exact congrArg ((V P.Coefficient X₁).map)
      (exceptional_tower_comp P.Coefficient sqf sqg K)
  · let := P.finiteComparedInvertibleExponent (Y ↘ Spec (.of P.field.k))
    have hω : Ctf P.Coefficient Y
        (Etale.dualizingComplex P.Coefficient g) :=
      DerivedCategory.constructibleFiniteTor_mapDerivedCategory P.Coefficient
        (Etale.boundedConstructibleFiniteTor_dualizingComplex P.Coefficient dg g)
    have ht := (tensorMateBaseChange P sqf
      (HasCompactification.compactification f)).2.2 _ hω
    have hb := beta_tower_comp P.Coefficient sqf sqg
    have hc : (L P.Coefficient u₁).map (sigma P.Coefficient f g) ≫
        Etale.dualizingComplexBaseChangeMap P.Coefficient (sqf.paste_vert sqg) =
        (L P.Coefficient u₁).map (Etale.dualizingComplexTensorMap P.Coefficient f
          (Etale.dualizingComplex P.Coefficient g)) ≫
        (Etale.rightDerivedUpperShriekBaseChangeMap P.Coefficient sqf).app _ ≫
        (R P.Coefficient a).map (Etale.dualizingComplexBaseChangeMap P.Coefficient sqg) ≫
        (WeilConjectures.PurityFiniteSetting.finiteExceptionalComposition
          P.Coefficient a b).inv.app (𝟙_ _) := by
      rw [hb]
      exact map_iso_cancel _
        ((WeilConjectures.PurityFiniteSetting.finiteExceptionalComposition
          P.Coefficient f g).app (𝟙_ _)) _ _
    rw [hc]
    have hs := map_comp_congr (V P.Coefficient X₁) ht
      ((R P.Coefficient a).map (Etale.dualizingComplexBaseChangeMap P.Coefficient sqg) ≫
        (WeilConjectures.PurityFiniteSetting.finiteExceptionalComposition
          P.Coefficient a b).inv.app (𝟙_ _))
    simp only [Category.assoc] at hs
    refine hs.trans ?_
    apply congrArg ((V P.Coefficient X₁).map)
    dsimp only [sigma]
    simp only [Functor.map_comp, Category.assoc]
    erw [← reassoc_of% (theta_naturality P.Coefficient a
      (Etale.dualizingComplexBaseChangeMap P.Coefficient sqg))]
    rfl

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance 20000] instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures
  CochainComplex.Monoidal.braidedCategory
  _root_.DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  _root_.DerivedCategory.laxMonoidalQh
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 100] HomologicalComplex.monoidalCategory

attribute [local semireducible] Sheaf.monoidalCategory
  _root_.DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

/-- The Koszul symmetry of the existing etale derived tensor, with its canonical
braided structure made explicit to avoid a file-local instance.
Source: main-20261015, thm-pur-composition-coherence, Step 1
(blueprint: lem-pur-smooth-exceptional-tensor-pasting). -/
def symmetry
    (A : Type uA) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((Etale.derivedTensor A X).obj K).obj M ≅ ((Etale.derivedTensor A X).obj M).obj K :=
  @BraidedCategory.braiding _ _ _ (_root_.DerivedCategory.braidedCategory' _) K M

/-- Associativity, symmetry and unit equations for specified tensor comparison maps.
This is a shared expression for the four chain equations below, with no extra hypotheses.
Source: main-20261015, thm-pur-composition-coherence, Step 1
(blueprint: lem-pur-smooth-exceptional-tensor-pasting). -/
def tensorComparisonCoherence
    {C E : Type*} [Category C] [Category E] [MonoidalCategory C] [MonoidalCategory E]
    (F : C ⥤ E) (δ : ∀ K M, F.obj (K ⊗ M) ⟶ F.obj K ⊗ F.obj M)
    (η : F.obj (𝟙_ C) ⟶ 𝟙_ E)
    (s : ∀ K M : C, K ⊗ M ≅ M ⊗ K) (t : ∀ K M : E, K ⊗ M ≅ M ⊗ K) : Prop :=
  (∀ K M N, F.map (α_ K M N).hom ≫ δ K (M ⊗ N) ≫ (𝟙 _ ⊗ₘ δ M N) =
    δ (K ⊗ M) N ≫ (δ K M ⊗ₘ 𝟙 _) ≫ (α_ (F.obj K) (F.obj M) (F.obj N)).hom) ∧
  (∀ K M, F.map (s K M).hom ≫ δ M K = δ K M ≫ (t (F.obj K) (F.obj M)).hom) ∧
  (∀ K, F.map (λ_ K).hom = δ (𝟙_ C) K ≫ (η ⊗ₘ 𝟙 _) ≫ (λ_ (F.obj K)).hom) ∧
  (∀ K, F.map (ρ_ K).hom = δ K (𝟙_ C) ≫ (𝟙 _ ⊗ₘ η) ≫ (ρ_ (F.obj K)).hom)

/-- The four tensor coherence equations evaluated at specified objects.
Source: main-20261015, thm-pur-composition-coherence, Step 1
(blueprint: lem-pur-smooth-exceptional-tensor-pasting). -/
def tensorComparisonCoherenceAt
    {C E : Type*} [Category C] [Category E] [MonoidalCategory C] [MonoidalCategory E]
    (F : C ⥤ E) (δ : ∀ K M, F.obj (K ⊗ M) ⟶ F.obj K ⊗ F.obj M)
    (η : F.obj (𝟙_ C) ⟶ 𝟙_ E)
    (s : ∀ K M : C, K ⊗ M ≅ M ⊗ K) (t : ∀ K M : E, K ⊗ M ≅ M ⊗ K)
    (K M N : C) : Prop :=
  (F.map (α_ K M N).hom ≫ δ K (M ⊗ N) ≫ (𝟙 _ ⊗ₘ δ M N) =
    δ (K ⊗ M) N ≫ (δ K M ⊗ₘ 𝟙 _) ≫ (α_ (F.obj K) (F.obj M) (F.obj N)).hom) ∧
  (F.map (s K M).hom ≫ δ M K = δ K M ≫ (t (F.obj K) (F.obj M)).hom) ∧
  (F.map (λ_ K).hom = δ (𝟙_ C) K ≫ (η ⊗ₘ 𝟙 _) ≫ (λ_ (F.obj K)).hom) ∧
  (F.map (ρ_ K).hom = δ K (𝟙_ C) ≫ (𝟙 _ ⊗ₘ η) ≫ (ρ_ (F.obj K)).hom)

/-- All canonical reassociations used in the pasting equations. The final equality
is the localization square identifying the derived tensor comparison with the
usual total-complex comparison. It is stated for every homotopy representative,
hence in particular for the flat-term K-flat ones used to compute derived tensor.
Source: main-20261015, thm-pur-composition-coherence, Step 1
(blueprint: lem-pur-smooth-exceptional-tensor-pasting). -/
def reassociationClause
    (A : Type uA) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    [Etale.UpperStarPreservesFlat A]
    {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (K M N : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A)) : Prop :=
  tensorComparisonCoherenceAt (Etale.upperStar A h).leftDerivedFunctor
    (fun K M ↦ ((Etale.leftDerivedUpperStarTensorComparison A h).app K).app M)
    (Etale.leftDerivedUpperStarUnitIso A h).hom
    (fun K M ↦ symmetry A Z K M) (fun K M ↦ symmetry A Y K M) K M N ∧
  (Etale.leftDerivedUpperStarComp A f (g ≫ h)
      ((f ≫ g) ≫ h) (Category.assoc f g h)).hom.app K ≫
      ((Etale.upperStar A f).leftDerivedFunctor).map ((Etale.leftDerivedUpperStarComp
        A g h).hom.app K) =
    (Etale.leftDerivedUpperStarComp A (f ≫ g) h).hom.app K ≫
      (Etale.leftDerivedUpperStarComp A f g).hom.app
        (((Etale.upperStar A h).leftDerivedFunctor).obj K) ∧
  (∀ B C : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A),
    ((Etale.leftDerivedUpperStarTensorComparison A (f ≫ g)).app B).app C ≫
        ((Etale.leftDerivedUpperStarComp A f g).hom.app B ⊗ₘ
          (Etale.leftDerivedUpperStarComp A f g).hom.app C) =
      (Etale.leftDerivedUpperStarComp A f g).hom.app (B ⊗ C) ≫
        (Etale.upperStar A f).leftDerivedFunctor.map
          (((Etale.leftDerivedUpperStarTensorComparison A g).app B).app C) ≫
        ((Etale.leftDerivedUpperStarTensorComparison A f).app _).app _) ∧
  (∀ C D : HomotopyCategory (Sheaf Z.smallEtaleTopology A) (.up ℤ),
    ((Etale.leftDerivedUpperStarTensorComparison A h).app
        (_root_.DerivedCategory.Qh.obj C)).app (_root_.DerivedCategory.Qh.obj D) ≫
        ((Etale.upperStar A h).leftDerivedFunctorCounit.app C ⊗ₘ
          (Etale.upperStar A h).leftDerivedFunctorCounit.app D) ≫
        Functor.LaxMonoidal.μ _root_.DerivedCategory.Qh
          (((Etale.upperStar A h).mapHomotopyCategory (.up ℤ)).obj C)
          (((Etale.upperStar A h).mapHomotopyCategory (.up ℤ)).obj D) =
      (Etale.upperStar A h).leftDerivedFunctor.map
          (Functor.LaxMonoidal.μ _root_.DerivedCategory.Qh C D) ≫
        (Etale.upperStar A h).leftDerivedFunctorCounit.app (C ⊗ D) ≫
        _root_.DerivedCategory.Qh.map
          (Functor.OplaxMonoidal.δ
            ((Etale.upperStar A h).mapHomotopyCategory (.up ℤ)) C D)) ∧
  (∀ C : HomotopyCategory (Sheaf Y.smallEtaleTopology A) (.up ℤ),
    (Etale.leftDerivedUpperStarComp A f g).hom.app (_root_.DerivedCategory.Qh.obj C) ≫
        (Etale.upperStar A f).leftDerivedFunctor.map
          ((Etale.upperStar A g).leftDerivedFunctorCounit.app C) ≫
        (Etale.upperStar A f).leftDerivedFunctorCounit.app
          (((Etale.upperStar A g).mapHomotopyCategory (.up ℤ)).obj C) =
      (Etale.upperStar A (f ≫ g)).leftDerivedFunctorCounit.app C ≫
        _root_.DerivedCategory.Qh.map
          (Functor.mapHomotopyCategoryCompHom (Etale.upperStar A g)
            (Etale.upperStar A f) (Etale.upperStar A (f ≫ g))
            (Etale.upperStarComp A f g (f ≫ g) rfl) C))

/-- The actual canonical comparison of total tensor complexes.
Source: main-20261015, thm-pur-composition-coherence, Step 1
(blueprint: lem-pur-smooth-exceptional-tensor-pasting). -/
def chainTensorComparison
    (A : Type uA) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K M : CochainComplex (Sheaf Y.smallEtaleTopology A) ℤ) :=
  ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
    (Etale.upperStar A f)).app K).app M

/-- Compatibility of three successive complex comparison maps.
Source: main-20261015, thm-pur-composition-coherence, Step 1
(blueprint: lem-pur-smooth-exceptional-tensor-pasting). -/
def complexThreefoldComparisonCoherence
    {C0 C1 C2 C3 : Type*} [Category C0] [Category C1] [Category C2] [Category C3]
    [Preadditive C0] [Preadditive C1] [Preadditive C2] [Preadditive C3]
    (F : C0 ⥤ C1) (G : C1 ⥤ C2) (H : C2 ⥤ C3)
    (FG : C0 ⥤ C2) (GH : C1 ⥤ C3) (T : C0 ⥤ C3)
    [F.Additive] [G.Additive] [H.Additive] [FG.Additive] [GH.Additive] [T.Additive]
    (eFG : FG ⟶ F ⋙ G) (eGH : GH ⟶ G ⋙ H)
    (e1 : T ⟶ FG ⋙ H) (e2 : T ⟶ F ⋙ GH)
    : Prop :=
  ∀ K : CochainComplex C0 ℤ,
    Functor.mapHomologicalComplexCompNatTrans FG H T e1 K ≫
        (H.mapHomologicalComplex (.up ℤ)).map
          (Functor.mapHomologicalComplexCompNatTrans F G FG eFG K) =
      Functor.mapHomologicalComplexCompNatTrans F GH T e2 K ≫
        Functor.mapHomologicalComplexCompNatTrans G H GH eGH
          ((F.mapHomologicalComplex (.up ℤ)).obj K)

/-- Chain-map reassociation, signed symmetry, unit and threefold composition.
No representative is chosen: these are equalities of actual chain maps, hence
also on the flat-term K-flat representatives used by derived tensor.
Source: main-20261015, thm-pur-composition-coherence, Step 1
(blueprint: lem-pur-smooth-exceptional-tensor-pasting). -/
def chainReassociationClause
    (A : Type uA) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) : Prop :=
  let F := (Etale.upperStar A h).mapHomologicalComplex (.up ℤ)
  tensorComparisonCoherence F (Functor.OplaxMonoidal.δ F)
    (Functor.OplaxMonoidal.η F)
    (fun K M ↦ β_ K M)
    (fun K M ↦ β_ K M) ∧
  complexThreefoldComparisonCoherence
    (Etale.upperStar A h) (Etale.upperStar A g) (Etale.upperStar A f)
    (Etale.upperStar A (g ≫ h)) (Etale.upperStar A (f ≫ g))
    (Etale.upperStar A ((f ≫ g) ≫ h))
    (Etale.upperStarComp A g h (g ≫ h) rfl).hom
    (Etale.upperStarComp A f g (f ≫ g) rfl).hom
    (Etale.upperStarComp A f (g ≫ h) ((f ≫ g) ≫ h) (Category.assoc f g h)).hom
    (Etale.upperStarComp A (f ≫ g) h ((f ≫ g) ≫ h) rfl).hom

section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem tensor_coherence_of_oplax
    {C E : Type*} [Category C] [Category E] [MonoidalCategory C] [MonoidalCategory E]
    (F : C ⥤ E) [F.OplaxMonoidal]
    (s : ∀ K M : C, K ⊗ M ≅ M ⊗ K) (t : ∀ K M : E, K ⊗ M ≅ M ⊗ K)
    (hb : ∀ K M, F.map (s K M).hom ≫ Functor.OplaxMonoidal.δ F M K =
      Functor.OplaxMonoidal.δ F K M ≫ (t (F.obj K) (F.obj M)).hom) :
    tensorComparisonCoherence F (Functor.OplaxMonoidal.δ F)
      (Functor.OplaxMonoidal.η F) s t := by
  refine ⟨?_, hb, ?_, ?_⟩
  · intro K M N
    simpa only [id_tensorHom, tensorHom_id] using
      (Functor.OplaxMonoidal.associativity F K M N).symm
  · intro K
    simpa only [tensorHom_id] using (Functor.OplaxMonoidal.left_unitality_hom F K).symm
  · intro K
    simpa only [id_tensorHom] using (Functor.OplaxMonoidal.right_unitality_hom F K).symm

private theorem map_complex_tensor_coherence
    {C E : Type*} [Category C] [Category E] [Abelian C] [Abelian E]
    [HasColimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} E]
    [MonoidalCategory C] [MonoidalCategory E]
    [MonoidalPreadditive C] [MonoidalPreadditive E]
    [BraidedCategory C] [BraidedCategory E] [MonoidalClosed C] [MonoidalClosed E]
    (G : C ⥤ E) [G.Additive] [G.Monoidal] [PreservesColimitsOfSize.{0, 0} G]
    (hb : ∀ K M, G.map (β_ K M).hom ≫ Functor.OplaxMonoidal.δ G M K =
      Functor.OplaxMonoidal.δ G K M ≫ (β_ (G.obj K) (G.obj M)).hom) :
    tensorComparisonCoherence (G.mapHomologicalComplex (.up ℤ))
      (Functor.OplaxMonoidal.δ (G.mapHomologicalComplex (.up ℤ)))
      (Functor.OplaxMonoidal.η (G.mapHomologicalComplex (.up ℤ)))
      (fun K M ↦ β_ K M) (fun K M ↦ β_ K M) := by
  apply tensor_coherence_of_oplax
  intro K M
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  simpa only [Functor.mapCochainComplex_δ, Functor.whiskeringLeft₂,
    Functor.whiskeringLeft, Functor.whiskeringRight, Functor.comp_obj, curriedTensor] using
    Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans_braiding G hb K M

private theorem tensor_coherence_at_of_whisker
    {C E : Type*} [Category C] [Category E] [MonoidalCategory C] [MonoidalCategory E]
    (F : C ⥤ E) (δ : ∀ K M, F.obj (K ⊗ M) ⟶ F.obj K ⊗ F.obj M)
    (η : F.obj (𝟙_ C) ⟶ 𝟙_ E)
    (s : ∀ K M : C, K ⊗ M ≅ M ⊗ K) (t : ∀ K M : E, K ⊗ M ≅ M ⊗ K)
    (K M N : C)
    (ha : δ (K ⊗ M) N ≫ δ K M ▷ F.obj N ≫
        (α_ (F.obj K) (F.obj M) (F.obj N)).hom =
      F.map (α_ K M N).hom ≫ δ K (M ⊗ N) ≫ F.obj K ◁ δ M N)
    (hb : F.map (s K M).hom ≫ δ M K = δ K M ≫ (t (F.obj K) (F.obj M)).hom)
    (hl : δ (𝟙_ C) K ≫ η ▷ F.obj K ≫ (λ_ (F.obj K)).hom = F.map (λ_ K).hom)
    (hr : δ K (𝟙_ C) ≫ F.obj K ◁ η ≫ (ρ_ (F.obj K)).hom = F.map (ρ_ K).hom) :
    tensorComparisonCoherenceAt F δ η s t K M N := by
  refine ⟨?_, hb, ?_, ?_⟩
  · simpa only [id_tensorHom, tensorHom_id] using ha.symm
  · simpa only [tensorHom_id] using hl.symm
  · simpa only [id_tensorHom] using hr.symm

private theorem map_complex_threefold
    {C0 C1 C2 C3 : Type*} [Category C0] [Category C1] [Category C2] [Category C3]
    [Preadditive C0] [Preadditive C1] [Preadditive C2] [Preadditive C3]
    (F : C0 ⥤ C1) (G : C1 ⥤ C2) (H : C2 ⥤ C3)
    (FG : C0 ⥤ C2) (GH : C1 ⥤ C3) (T : C0 ⥤ C3)
    [F.Additive] [G.Additive] [H.Additive] [FG.Additive] [GH.Additive] [T.Additive]
    (eFG : FG ⟶ F ⋙ G) (eGH : GH ⟶ G ⋙ H)
    (e1 : T ⟶ FG ⋙ H) (e2 : T ⟶ F ⋙ GH)
    (hc : ∀ X, e1.app X ≫ H.map (eFG.app X) = e2.app X ≫ eGH.app (F.obj X))
    : complexThreefoldComparisonCoherence F G H FG GH T eFG eGH e1 e2 := by
  intro K
  ext n : 1
  simpa only [HomologicalComplex.comp_f, Functor.mapHomologicalComplexCompNatTrans_f,
    Functor.mapHomologicalComplex_map_f, Functor.mapHomologicalComplex_obj_X,
    Functor.comp_obj] using hc (K.X n)

attribute [local irreducible] reassociationClause chainReassociationClause

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem reassociation_pasting
    (A : Type uA) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
    {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (K M N : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    reassociationClause A f g h K M N ∧ chainReassociationClause A f g h := by
  constructor
  · unfold reassociationClause
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · apply tensor_coherence_at_of_whisker
      · exact Etale.leftDerivedUpperStarTensorComparison_associativity A h K M N
      · simpa only [symmetry, Etale.leftDerivedUpperStar_δ_eq] using
          Etale.leftDerivedUpperStar_map_braiding_hom_δ A h K M
      · exact Etale.leftDerivedUpperStarTensorComparison_leftUnitor_hom A h K
      · exact Etale.leftDerivedUpperStarTensorComparison_rightUnitor_hom A h K
    · exact Etale.leftDerivedUpperStarComp_assoc'_app A f g h (f ≫ g) (g ≫ h)
        ((f ≫ g) ≫ h) rfl rfl rfl K
    · intro B C
      exact Etale.leftDerivedUpperStarTensorComparison_comp A f g (f ≫ g) rfl B C
    · intro C D
      exact Etale.leftDerivedUpperStarTensorComparison_app_app_comp A h C D
    · intro C
      exact Etale.leftDerivedUpperStarComp_hom_app_Qh_obj_comp_counit A f g (f ≫ g) rfl C
  · unfold chainReassociationClause
    constructor
    · exact map_complex_tensor_coherence (Etale.upperStar A h)
        (Etale.upperStar_map_braiding_hom_δ A h)
    · apply map_complex_threefold
      intro T
      simpa only [NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app] using
        NatTrans.congr_app (Etale.upperStarComp_assoc'
          A f g h (f ≫ g) (g ≫ h) ((f ≫ g) ≫ h) rfl rfl rfl) T

end

/-- Reassociation, Koszul symmetry, unit and threefold-pullback coherence,
with the actual total-tensor representative normalization.
Source: main-20261015, thm-pur-composition-coherence.proof.md, Step 1
(blueprint: lem-pur-smooth-exceptional-tensor-pasting).

Proof: Work first over a general coefficient category. The proved source
pullback laws give the derived associativity, braiding and unit fields. The
source compositor equations give composition associativity and tensor
compatibility. Their proved counit equations are the two localization fields.
For complexes, the induced oplax monoidal functor gives associativity and the
unit laws, and its proved braiding compatibility gives the signed symmetry.
The cochain delta and eta are exactly the recorded total tensor comparison and
inverse unit isomorphism. The threefold compositor equality follows degreewise
from upperStarComp_assoc'. Assemble these equations and specialize to
the actual coefficient module category. No representative or orientation is chosen. -/
theorem smoothExceptionalReassociationPasting
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (K M N : D P.Coefficient Z) :
    reassociationClause (ModuleCat.{u + 1} P.Coefficient) f g h K M N ∧
      chainReassociationClause (ModuleCat.{u + 1} P.Coefficient) f g h := by
  exact reassociation_pasting (ModuleCat.{u + 1} P.Coefficient) f g h K M N

end AlgebraicGeometry.ProEtale.SmoothExceptionalPasting
