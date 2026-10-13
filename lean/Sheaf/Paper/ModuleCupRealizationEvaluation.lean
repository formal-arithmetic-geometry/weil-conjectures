/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.Paper.ModuleCupResolutionRealization
import Sheaf.Paper.ModuleCupNaiveDerivedCompatibility

/-! # Evaluating a realized pairing after derived global sections

Source: Stacks Project, Section 20.31, Tags 0FKU and 0FKV.
(blueprint: lem-sc-module-cup-realization-evaluation)
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

variable {X : Scheme.{u}}
  [HasDerivedCategory.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

local instance cupEvaluationMonoidalCategory :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf
local instance cupEvaluationSymmetricCategory :
    SymmetricCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.symmetricCategory X.sheaf
local instance cupEvaluationHasColimitsOfSize :
    HasColimitsOfSize.{0, 0} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  hasColimitsOfSizeShrink.{0, 0, u} _
local instance cupEvaluationMonoidalPreadditive :
    MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
local instance cupEvaluationMonoidalClosed :
    MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
local instance cupEvaluationHasFunctorialFlatResolution : Abelian.HasFunctorialFlatResolution
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  schemeModule_hasFunctorialFlatResolution X
local instance cupEvaluationIsGrothendieckAbelian : IsGrothendieckAbelian.{u}
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)

/-- The global evaluation diagram, before comparing two resolution pairings.
Source: Stacks Project, Section 20.31 (0FKU), Lemmas 20.31.1 and 20.31.3 and
its global specialization immediately following the proof.
(blueprint: lem-sc-module-cup-realization-evaluation)
Proof: represent classes in H^p(X,F) and H^q(X,G) as morphisms from
O_X[-p] and O_X[-q] to F[0] and G[0]. Tensor these morphisms, identify the
tensor of the shifted units with O_X[-p-q], and postcompose with the supplied
morphism f. This defines evaluation, bilinear by additivity and O_X(X)-linearity
of derived tensor and of the cohomology/Hom comparison. It is defined for every
f, without any normalization hypothesis on H-zero(f). For a cochain realization
t, apply moduleCup_naive_derived_compatibility to the integer extensions of the
left and right resolutions. Postcompose its commutative diagram with Q(t) and
the inverse localized target augmentation. Naturality transports through the
input augmentations. The tensor-summand formula for the naive map and
D.Realizes t identify its value on the two given cocycles with D.pair p q.
The comparison K to the supplied injective resolution extends the augmentation
by D.over, so its map on cohomology is exactly D.class; D.computes makes the
comparison invertible. Extension by zero and its homology isomorphisms identify
the integer and nonnegative computations. Taking H^(p+q) in the diagram gives
the stated evaluation formula. This step does not compare derived maps arising
from different pairings and does not assume equality of any input classes. -/
theorem moduleCup_realization_evaluation (F G : X.Modules) (p q : ℕ) :
    ∃ evaluation :
      (((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F) ⊗
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ⟶
          (DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj (F ⊗ G)) →
        (RingedSpace.moduleCohomology X.toRingedSpace p).obj F →ₗ[Γ(X, ⊤)]
          (RingedSpace.moduleCohomology X.toRingedSpace q).obj G →ₗ[Γ(X, ⊤)]
            (RingedSpace.moduleCohomology X.toRingedSpace (p + q)).obj (F ⊗ G),
      ∀ (D : CupResolutionPairing F G)
        (t : D.left.integerComplex ⊗ D.right.integerComplex ⟶ D.target.integerComplex)
        (_ht : D.Realizes t)
        (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
        (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K)
        (c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K),
        c.val = D.pair p q ⊤ a.val b.val →
          evaluation (D.derivedMap t) (D.left.class p a) (D.right.class q b) =
            D.target.class (p + q) c := by sorry

end
end AlgebraicGeometry.Scheme.Modules
