/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Submission.WeilConjectures.Algebra.Homology.RingTensorCohomology
public import Mathlib.RingTheory.Localization.Basic
import Submission.WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Submission.WeilConjectures.Algebra.Homology.MixedTotalTensor
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import Submission.WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import Submission.WeilConjectures.Algebra.Homology.KFlatScalarExtensionCounit
import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Submission.WeilConjectures.Algebra.Homology.MixedTensorUnderlyingHomology
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.BaseChange

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # The characterized first-factor localization morphism

Source: Stacks Project, More on Algebra, Tag 06Y6; perfect.tex, Tag 0DJ8.
(blueprint: lem-pc-first-localization-map).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory
open scoped TensorProduct ChangeOfRings

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace RingTensorCohomology

variable (R A Aq : Type u) [CommRing R] [CommRing A] [CommRing Aq]
  [Algebra R A] [Algebra A Aq] [Algebra R Aq] [IsScalarTower R A Aq]

/-- The localization unit on the underlying R-complex. It sends x to 1 tensor x.
Source: Stacks Project, Tag 06Y6 (blueprint: lem-pc-first-localization-map). -/
noncomputable def firstLocalizationUnit
    (Q : CochainComplex (ModuleCat.{u} A) ℤ) :
    (restrict R A).obj Q ⟶ (restrict R Aq).obj ((extend A Aq).obj Q) where
  f j := (ModuleCat.restrictScalars (algebraMap R A)).map
    ((ModuleCat.extendRestrictScalarsAdj (algebraMap A Aq)).unit.app (Q.X j)) ≫
    (ModuleCat.restrictScalarsComp'App (algebraMap R A) (algebraMap A Aq)
      (algebraMap R Aq) (IsScalarTower.algebraMap_eq R A Aq)
      (((extend A Aq).obj Q).X j)).inv
  comm' j k hjk := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (ModuleCat.extendScalars (algebraMap A Aq)).map (Q.d j k)
        ((1 : Aq) ⊗ₜ[A,algebraMap A Aq] x) =
      (1 : Aq) ⊗ₜ[A,algebraMap A Aq] (Q.d j k x)
    rw [ModuleCat.ExtendScalars.map_tmul]

variable (B D : Type u) [CommRing B] [CommRing D] [Algebra R B]
  [Algebra (A ⊗[R] B) D] [Algebra (Aq ⊗[R] B) D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]

/-- Apply derived tensor and cohomology to the first-factor unit, using the unique
counit-compatible comparison of derived functors.
Source: Stacks Project, Tag 06Y6 (blueprint: lem-pc-first-localization-map). -/
noncomputable def firstLocalizationCohomologyMap
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R Aq B ((extend A Aq).obj Q) D)
    (i : ℤ) :
    (ModuleCat.restrictScalars.{u}
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).obj
        (L.cohomology i) ⟶
    (ModuleCat.restrictScalars.{u}
      (Algebra.TensorProduct.includeRight : B →ₐ[R] Aq ⊗[R] B).toRingHom).obj
        (K.cohomology i) := by
  let _ := L.universal
  let _ := K.universal
  let ζ := Functor.leftDerivedNatIso L.derived K.derived L.counit K.counit
    (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)) (Iso.refl _)
  exact (L.cohomologyIso i).hom ≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
      (L.derived.map (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map
          (firstLocalizationUnit R A Aq Q))) ≫
        ζ.hom.app (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
            ((restrict R Aq).obj ((extend A Aq).obj Q))))) ≫
    (K.cohomologyIso i).inv

/-- The generator formula fixes the localization morphism uniquely.
Source: Stacks Project, Tag 06Y6 (blueprint: lem-pc-first-localization-map). -/
def IsFirstLocalizationMap
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R Aq B ((extend A Aq).obj Q) D)
    (i : ℤ)
    (e : (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (L.cohomology i) ⟶
      (ModuleCat.extendScalars (algebraMap (Aq ⊗[R] B) D)).obj (K.cohomology i)) : Prop :=
  ∀ x : L.cohomology i,
    e ((1 : D) ⊗ₜ[A ⊗[R] B,algebraMap (A ⊗[R] B) D] x) =
      (1 : D) ⊗ₜ[Aq ⊗[R] B,algebraMap (Aq ⊗[R] B) D]
        (firstLocalizationCohomologyMap R A Aq B D Q L K i x)

/-- Equality on the scalar-extension generators proves uniqueness; in particular the
existence theorem below determines data, rather than an arbitrary witness.
Source: Stacks Project, Tag 06Y6 (blueprint: lem-pc-first-localization-map). -/
theorem IsFirstLocalizationMap.ext
    {Q : CochainComplex (ModuleCat.{u} A) ℤ}
    {L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D}
    {K : ModuleCat.BaseDerivedTensorCohomologyModel R Aq B ((extend A Aq).obj Q) D}
    {i : ℤ}
    {e e' : (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (L.cohomology i) ⟶
      (ModuleCat.extendScalars (algebraMap (Aq ⊗[R] B) D)).obj (K.cohomology i)}
    (he : IsFirstLocalizationMap R A Aq B D Q L K i e)
    (he' : IsFirstLocalizationMap R A Aq B D Q L K i e') : e = e' := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  exact (he x).trans (he' x).symm

variable [Algebra A D] [Algebra B D] [Algebra Aq D]
  [tAD : IsScalarTower A (A ⊗[R] B) D] [tBD : IsScalarTower B (A ⊗[R] B) D]
  [tAqD : IsScalarTower Aq (Aq ⊗[R] B) D] [tBqD : IsScalarTower B (Aq ⊗[R] B) D]
  [tAAqD : IsScalarTower A Aq D]

end RingTensorCohomology
