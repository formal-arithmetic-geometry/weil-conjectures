/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import WeilConjectures.AlgebraicGeometry.KInjectiveMayerVietorisData
import Sheaf.AlgebraicGeometry.OpenImageDirectImageComparisonRestriction

/-! # Ordinary direct-image comparison squares for Mayer--Vietoris

Source: Stacks Project, Cohomology, Tags 08BV and 08FE.
(blueprint: lem-pc-mayer-vietoris-direct-image-chain-squares).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

set_option autoImplicit false
set_option synthInstance.maxSize 2048

noncomputable section
namespace AlgebraicGeometry

attribute [local irreducible] schemeOpenModuleAdjunction
  schemeOpenModuleImageRestriction RingedSpace.moduleDirectImage

private theorem imageUnitSquare
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (P : C ⥤ C) (Q : D ⥤ D)
    (α : P ⋙ F ⟶ F ⋙ Q) (η : 𝟭 C ⟶ P) (ε : 𝟭 D ⟶ Q)
    (h : ∀ M, F.map (η.app M) ≫ α.app M = ε.app (F.obj M))
    {A : C} {B : D} (f : F.obj A ⟶ B) :
    f ≫ ε.app B = F.map (η.app A) ≫ (α.app A ≫ Q.map f) := by
  exact (ε.naturality f).trans
    ((congrArg (fun k ↦ k ≫ Q.map f) (h A).symm).trans (Category.assoc _ _ _))

private theorem imageRestrictionSquare
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (P P' : C ⥤ C) (Q Q' : D ⥤ D)
    (α : P ⋙ F ⟶ F ⋙ Q) (β : P' ⋙ F ⟶ F ⋙ Q')
    (ρ : P ⟶ P') (σ : Q ⟶ Q')
    (h : ∀ M, α.app M ≫ σ.app (F.obj M) = F.map (ρ.app M) ≫ β.app M)
    {A : C} {B : D} (f : F.obj A ⟶ B) :
    (α.app A ≫ Q.map f) ≫ σ.app B =
      F.map (ρ.app A) ≫ (β.app A ≫ Q'.map f) := by
  exact ((Category.assoc _ _ _).trans
    (congrArg (fun k ↦ α.app A ≫ k) (σ.naturality f))).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun k ↦ k ≫ Q'.map f) (h A)).trans (Category.assoc _ _ _)))

set_option backward.isDefEq.respectTransparency.types false in
private def openImageComparisonMap
    (X Y : Scheme.{u}) (h : X ⟶ Y) (U : Y.Opens)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (J : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (f : ((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I ⟶ J) :
    ((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (schemeOpenModuleImageComplex X (h ⁻¹ᵁ U) I) ⟶
        schemeOpenModuleImageComplex Y U J where
  f n := (schemeOpenImageDirectImageComparison h U).hom.app (I.X n) ≫
    (schemeOpenModuleImage Y U).map (f.f n)
  comm' i j _ := by
    change ((schemeOpenImageDirectImageComparison h U).hom.app (I.X i) ≫
      (schemeOpenModuleImage Y U).map (f.f i)) ≫
      (schemeOpenModuleImage Y U).map (J.d i j) =
      (RingedSpace.moduleDirectImage h.toLRSHom.toShHom).map
        ((schemeOpenModuleImage X (h ⁻¹ᵁ U)).map (I.d i j)) ≫
      ((schemeOpenImageDirectImageComparison h U).hom.app (I.X j) ≫
        (schemeOpenModuleImage Y U).map (f.f j))
    rw [Category.assoc, ← Functor.map_comp]
    have hf : f.f i ≫ J.d i j =
        (RingedSpace.moduleDirectImage h.toLRSHom.toShHom).map (I.d i j) ≫ f.f j :=
      f.comm i j
    rw [hf, Functor.map_comp, ← Category.assoc]
    exact congrArg (fun k ↦ k ≫ (schemeOpenModuleImage Y U).map (f.f j))
      ((schemeOpenImageDirectImageComparison h U).hom.naturality (I.d i j)).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- A supplied chain map out of direct image extends to the three open terms,
commuting with the two units and the two unsigned restrictions.
Source: Stacks Project, Tag 08BV (lemma-exact-sequence-j-star), displayed complex;
Tag 08FE (lemma-restrict-direct-image-open), the underived sectionwise identity.
(blueprint: lem-pc-mayer-vietoris-direct-image-chain-squares).

Proof: Assemble the ordinary open-image comparison isomorphism from the fixed
underived open-composition and open-restriction isomorphisms. Its compatibility
with the open unit is schemeOpenImageDirectImageComparison_unit. Compatibility
with nested restriction follows by cancelling the direct image of the larger
open unit: after restriction to the smaller open it is invertible. This uses
fully faithful open direct image, the triangle identity and the nested
restriction comparison. Precomposition reduces both composites to the smaller
open unit. Apply the ordinary comparison termwise to I and compose with the
open-image functor applied to f. Naturality of the comparison proves that these
are chain maps. Naturality of the open unit and the nested restriction, together
with the two ordinary compatibility identities, proves the four equations in
each degree. Use the opens U, V and U intersect V; inverse image preserves their
intersection. No cover, injectivity or derived resolution is used. Empty and
repeated opens and zero complexes satisfy the same functorial identities. -/
theorem schemeMV_directImage_chain_squares
    (X Y : Scheme.{u}) (h : X ⟶ Y) (U V : Y.Opens)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (J : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (f : ((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I ⟶ J) :
    let F := (RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
      (ComplexShape.up ℤ)
    ∃ (a : F.obj (schemeOpenModuleImageComplex X (h ⁻¹ᵁ U) I) ⟶
        schemeOpenModuleImageComplex Y U J)
      (b : F.obj (schemeOpenModuleImageComplex X (h ⁻¹ᵁ V) I) ⟶
        schemeOpenModuleImageComplex Y V J)
      (c : F.obj (schemeOpenModuleImageComplex X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)) I) ⟶
        schemeOpenModuleImageComplex Y (U ⊓ V) J),
      f ≫ schemeOpenModuleImageComplexUnit Y U J =
        F.map (schemeOpenModuleImageComplexUnit X (h ⁻¹ᵁ U) I) ≫ a ∧
      f ≫ schemeOpenModuleImageComplexUnit Y V J =
        F.map (schemeOpenModuleImageComplexUnit X (h ⁻¹ᵁ V) I) ≫ b ∧
      a ≫ schemeOpenModuleImageComplexRestriction Y (homOfLE inf_le_left) J =
        F.map (schemeOpenModuleImageComplexRestriction X (homOfLE inf_le_left) I) ≫ c ∧
      b ≫ schemeOpenModuleImageComplexRestriction Y (homOfLE inf_le_right) J =
        F.map (schemeOpenModuleImageComplexRestriction X (homOfLE inf_le_right) I) ≫ c := by
  let a := openImageComparisonMap X Y h U I J f
  let b := openImageComparisonMap X Y h V I J f
  let c := openImageComparisonMap X Y h (U ⊓ V) I J f
  refine ⟨a, b, c, ?_, ?_, ?_, ?_⟩
  · apply HomologicalComplex.Hom.ext
    funext n
    exact imageUnitSquare (RingedSpace.moduleDirectImage h.toLRSHom.toShHom)
      (schemeOpenModuleImage X (h ⁻¹ᵁ U)) (schemeOpenModuleImage Y U)
      (schemeOpenImageDirectImageComparison h U).hom
      (schemeOpenModuleAdjunction X (h ⁻¹ᵁ U)).unit
      (schemeOpenModuleAdjunction Y U).unit
      (schemeOpenImageDirectImageComparison_unit X Y h U) (f.f n)
  · apply HomologicalComplex.Hom.ext
    funext n
    exact imageUnitSquare (RingedSpace.moduleDirectImage h.toLRSHom.toShHom)
      (schemeOpenModuleImage X (h ⁻¹ᵁ V)) (schemeOpenModuleImage Y V)
      (schemeOpenImageDirectImageComparison h V).hom
      (schemeOpenModuleAdjunction X (h ⁻¹ᵁ V)).unit
      (schemeOpenModuleAdjunction Y V).unit
      (schemeOpenImageDirectImageComparison_unit X Y h V) (f.f n)
  · apply HomologicalComplex.Hom.ext
    funext n
    exact imageRestrictionSquare (RingedSpace.moduleDirectImage h.toLRSHom.toShHom)
      (schemeOpenModuleImage X (h ⁻¹ᵁ U)) (schemeOpenModuleImage X (h ⁻¹ᵁ (U ⊓ V)))
      (schemeOpenModuleImage Y U) (schemeOpenModuleImage Y (U ⊓ V))
      (schemeOpenImageDirectImageComparison h U).hom
      (schemeOpenImageDirectImageComparison h (U ⊓ V)).hom
      (schemeOpenModuleImageRestriction X
        (homOfLE (inf_le_left : (h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V) ≤ h ⁻¹ᵁ U)))
      (schemeOpenModuleImageRestriction Y (homOfLE (inf_le_left : U ⊓ V ≤ U)))
      (schemeOpenImageDirectImageComparison_restriction X Y h
        (homOfLE (inf_le_left : U ⊓ V ≤ U))) (f.f n)
  · apply HomologicalComplex.Hom.ext
    funext n
    exact imageRestrictionSquare (RingedSpace.moduleDirectImage h.toLRSHom.toShHom)
      (schemeOpenModuleImage X (h ⁻¹ᵁ V)) (schemeOpenModuleImage X (h ⁻¹ᵁ (U ⊓ V)))
      (schemeOpenModuleImage Y V) (schemeOpenModuleImage Y (U ⊓ V))
      (schemeOpenImageDirectImageComparison h V).hom
      (schemeOpenImageDirectImageComparison h (U ⊓ V)).hom
      (schemeOpenModuleImageRestriction X
        (homOfLE (inf_le_right : (h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V) ≤ h ⁻¹ᵁ V)))
      (schemeOpenModuleImageRestriction Y (homOfLE (inf_le_right : U ⊓ V ≤ V)))
      (schemeOpenImageDirectImageComparison_restriction X Y h
        (homOfLE (inf_le_right : U ⊓ V ≤ V))) (f.f n)

end AlgebraicGeometry
