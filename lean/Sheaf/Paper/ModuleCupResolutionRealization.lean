/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.Paper.ModuleCupResolutionData
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.Paper.ModuleCupCanonicalHZeroIdentification
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Sheaf.Paper.ModuleCupHZeroIdentification

/-! # Realizing a resolution pairing in the derived category

Source: Stacks Project, Section 20.31, Tags 0FKU and 0FKV.
(blueprint: lem-sc-module-cup-resolution-realization)
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

variable {X : Scheme.{u}}
  [HasDerivedCategory.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

@[instance_reducible] local instance cupRealizationMonoidalCategory :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf
@[instance_reducible] local instance cupRealizationSymmetricCategory :
    SymmetricCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.symmetricCategory X.sheaf
local instance cupRealizationHasColimitsOfSize :
    HasColimitsOfSize.{0, 0} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  hasColimitsOfSizeShrink.{0, 0, u} _
local instance cupRealizationMonoidalPreadditive :
    MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
@[instance_reducible] local instance cupRealizationMonoidalClosed :
    MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
local instance cupRealizationHasFunctorialFlatResolution : Abelian.HasFunctorialFlatResolution
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  schemeModule_hasFunctorialFlatResolution X
local instance cupRealizationIsGrothendieckAbelian : IsGrothendieckAbelian.{u}
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)

local instance cupRealizationDerivedMonoidal :
    Functor.HasDerivedMonoidalCategory
      (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)))
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)) :=
  DerivedCategory.hasDerivedMonoidalCategory _

@[instance_reducible] local instance cupRealizationQLax :
    Functor.LaxMonoidal
      (DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))) :=
  inferInstance

/-- Extend a nonnegative resolution to integer degrees by zero. -/
abbrev CupAcyclicResolution.integerComplex {F : X.Modules} (D : CupAcyclicResolution F) :
    CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ :=
  D.K.extend ComplexShape.embeddingUpNat

/-- The localized augmentation, with the extended single complex identified with F[0]. -/
def CupAcyclicResolution.derivedAugmentation {F : X.Modules} (D : CupAcyclicResolution F) :
    DerivedCategory.Q.obj ((CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F) ⟶
      DerivedCategory.Q.obj D.integerComplex :=
  DerivedCategory.Q.map
    ((HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0 0 rfl).inv ≫
      HomologicalComplex.extendMap D.augmentation ComplexShape.embeddingUpNat)

/-- An augmentation is inverted by the derived localization. -/
instance CupAcyclicResolution.derivedAugmentation_isIso
    {F : X.Modules} (D : CupAcyclicResolution F) : IsIso D.derivedAugmentation := by
  let : QuasiIso D.augmentation := D.quasiIso
  unfold CupAcyclicResolution.derivedAugmentation
  rw [Functor.map_comp]
  infer_instance

/-- The section formula for the cochain morphism realizing the bilinear pairing.
It specifies all nonzero tensor summands; extension by zero supplies the others. -/
def CupResolutionPairing.Realizes {F G : X.Modules} (D : CupResolutionPairing F G)
    (t : D.left.integerComplex ⊗ D.right.integerComplex ⟶ D.target.integerComplex) : Prop :=
  ∀ (p q : ℕ) (V : X.Opens) (a : Γ(D.left.K.X p, V)) (b : Γ(D.right.K.X q, V)),
    ((HomologicalComplex.ιTensorObj D.left.integerComplex D.right.integerComplex
        (p : ℤ) (q : ℤ) ((p + q : ℕ) : ℤ) (by omega) ≫ t.f (p + q) ≫
      (D.target.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).hom).val.app (op V)
        (tmulSection
          ((D.left.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).inv.val.app (op V) a)
          ((D.right.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).inv.val.app (op V) b)))
      = D.pair p q V a b

/-- The derived morphism attached to a cochain realization. This is an explicit
composite of localized augmentations and the canonical tensor comparison. -/
def CupResolutionPairing.derivedMap {F G : X.Modules} (D : CupResolutionPairing F G)
    (t : D.left.integerComplex ⊗ D.right.integerComplex ⟶ D.target.integerComplex) :
    DerivedCategory.Q.obj ((CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F) ⊗
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ⟶
        DerivedCategory.Q.obj ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj (F ⊗ G)) :=
  (D.left.derivedAugmentation ⊗ₘ D.right.derivedAugmentation) ≫
    Functor.LaxMonoidal.μ DerivedCategory.Q D.left.integerComplex D.right.integerComplex ≫
    DerivedCategory.Q.map t ≫ inv D.target.derivedAugmentation

/-- Every resolution pairing has a cochain realization, and its derived morphism
has the same H-zero map as the canonical derived-to-ordinary tensor comparison.
Source: Stacks Project, Section 20.31 (0FKU), construction preceding Lemma 20.31.3,
and Tag 06YH, the degree-zero calculation for derived tensor.
(blueprint: lem-sc-module-cup-resolution-realization)
Proof: the tensor universal property sheafifies the restriction-compatible
sectionwise bilinear maps in each bidegree. On the direct-sum total tensor,
assemble these maps using the coproduct universal property. The signed Leibniz
condition is precisely the cochain-map equation, including degree zero and the
zero terms in negative degrees. This constructs t with the displayed section
formula. Transport through the localized augmentations and precompose with the
lax tensor comparison of Q, giving D.derivedMap t. To compute H-zero, use a
nonpositive flat model for F[0]. The tensor augmentation identifies its H-zero
with the ordinary tensor by right exactness, as in
moduleCup_hzero_identification. The transport formula in
moduleCup_canonical_hzero_identification identifies this calculation with the
canonical comparison. Naturality of the lax comparison and D.augmentation_pair
say that the H-zero map is the identity on F tensor G under this identification.
This gives the displayed equality; no statement comparing two resolutions or
positive-degree cohomology products is used. -/
theorem moduleCup_resolution_realization {F G : X.Modules} (D : CupResolutionPairing F G) :
    let F₀ := (CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F
    let G₀ := (CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G
    let canonical := Functor.LaxMonoidal.μ DerivedCategory.Q F₀ G₀ ≫
      DerivedCategory.Q.map (DerivedCategory.moduleCup_singleTensorIso
        (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)) F G).hom
    ∃ t : D.left.integerComplex ⊗ D.right.integerComplex ⟶ D.target.integerComplex,
      D.Realizes t ∧
        (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map (D.derivedMap t) =
          (DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map canonical := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
