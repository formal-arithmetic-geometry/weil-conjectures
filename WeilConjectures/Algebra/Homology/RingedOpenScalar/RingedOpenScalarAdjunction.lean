/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-! # Scalar restriction and normalized slice extension

Source: Stacks Project, Modules on Sites, Tags 03DI, 03CY and 03DJ
(blueprint: lem-cbc-ringed-open-scalar-adjunction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe c v r w t h
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules
namespace RingedOpenScalar

section EquationCalculus

variable {A B C D : Type t} [Category.{h} A] [Category.{h} B]
  [Category.{h} C] [Category.{h} D]
  {JS : A ⥤ C} {JR : B ⥤ D} {rU : A ⥤ B} {rT : C ⥤ D}
  {qS : C ⥤ A} {qR : D ⥤ B}
  (e : JS ⋙ rT ≅ rU ⋙ JR) (d : rT ⋙ qR ≅ qS ⋙ rU)
  (adjS : JS ⊣ qS) (adjR : JR ⊣ qR)

variable [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [JS.Additive] [JR.Additive] [rU.Additive] [rT.Additive] [qS.Additive] [qR.Additive]

variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
  [PreservesFiniteLimits JS] [PreservesFiniteColimits JS]
  [PreservesFiniteLimits JR] [PreservesFiniteColimits JR]
  [PreservesFiniteLimits rU] [PreservesFiniteColimits rU]
  [PreservesFiniteLimits rT] [PreservesFiniteColimits rT]
  [PreservesFiniteLimits qS] [PreservesFiniteColimits qS]
  [PreservesFiniteLimits qR] [PreservesFiniteColimits qR]

end EquationCalculus

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  {R S : Sheaf J CommRingCat.{max c v r}} (U : C) (a : R ⟶ S)

@[irreducible] private def presheafComparison :
    extensionByZeroPresheaf.{max c v r} (rings.{c, v, r} S) U ⋙
        PresheafOfModules.restrictScalars
          ((sheafCompose J
            (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map a).hom ≅
      sliceScalars.{c, v, r} U a ⋙
        extensionByZeroPresheaf.{max c v r} (rings.{c, v, r} R) U := by
  let b := ((sheafCompose J
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map a).hom
  let P := extensionByZeroPresheaf.{max c v r} (rings.{c, v, r} S) U ⋙
    PresheafOfModules.restrictScalars b
  let Q := sliceScalars.{c, v, r} U a ⋙
    extensionByZeroPresheaf.{max c v r} (rings.{c, v, r} R) U
  refine NatIso.ofComponents (fun N ↦ PresheafOfModules.isoMk (fun V ↦
    { hom := ModuleCat.ofHom (X := (P.obj N).obj V) (Y := (Q.obj N).obj V)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
      inv := ModuleCat.ofHom (X := (Q.obj N).obj V) (Y := (P.obj N).obj V)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
      hom_inv_id := by ext x; rfl
      inv_hom_id := by ext x; rfl })
    (by intro V W f; ext x; rfl)) ?_
  intro N M f
  ext V x
  rfl

@[irreducible] private def sheafComparisonInv
    (N : SheafOfModules.{max c v r} ((rings.{c, v, r} S).over U)) :
    (localizedSystemExtension.{c, v, r} R U).obj
        ((sliceScalars.{c, v, r} U a).obj N) ⟶
      (scalars.{c, v, r} a).obj ((localizedSystemExtension.{c, v, r} S U).obj N) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 (rings.{c, v, r} R).obj)).symm
    ((presheafComparison.{c, v, r} U a).inv.app N ≫
      (PresheafOfModules.restrictScalars
        ((sheafCompose J
          (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map a).hom).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 (rings.{c, v, r} S).obj)).unit.app
          ((extensionByZeroPresheaf.{max c v r} (rings.{c, v, r} S) U).obj N)))

@[irreducible] private def sheafComparison :
    localizedSystemExtension.{c, v, r} S U ⋙ scalars.{c, v, r} a ≅
      sliceScalars.{c, v, r} U a ⋙ localizedSystemExtension.{c, v, r} R U := by
  have (N : SheafOfModules.{max c v r} ((rings.{c, v, r} S).over U)) :
      IsIso (sheafComparisonInv.{c, v, r} U a N) :=
    sheafComparisonInv_isIso.{c, v, r} U a N
  exact (NatIso.ofComponents (fun N ↦ asIso (sheafComparisonInv.{c, v, r} U a N))
    (by
      intro N M f
      apply (toSheaf.{max c v r} (rings.{c, v, r} R)).map_injective
      simp only [Functor.map_comp, asIso_hom, sheafComparisonInv_underlying]
      let F := presheafToSheaf J AddCommGrpCat.{max c v r}
      let T := PresheafOfModules.toPresheaf.{max c v r} (rings.{c, v, r} R).obj
      change F.map (T.map ((sliceScalars.{c, v, r} U a ⋙
          extensionByZeroPresheaf.{max c v r} (rings.{c, v, r} R) U).map f)) ≫
          F.map (T.map ((presheafComparison.{c, v, r} U a).inv.app M)) =
        F.map (T.map ((presheafComparison.{c, v, r} U a).inv.app N)) ≫
          F.map (T.map ((extensionByZeroPresheaf.{max c v r} (rings.{c, v, r} S) U ⋙
            PresheafOfModules.restrictScalars
              ((sheafCompose J
                (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map a).hom).map f))
      rw [← F.map_comp, ← F.map_comp, ← T.map_comp, ← T.map_comp]
      exact congrArg (fun g ↦ F.map (T.map g))
        ((presheafComparison.{c, v, r} U a).inv.naturality f))).symm

end RingedOpenScalar
end SheafOfModules
