/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.SymmetricAlgebraSheafConstruction
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.QuasiCoherentSymmetricAlgebraAffine
public import WeilConjectures.AlgebraicGeometry.VectorBundleZeroSection.VectorBundleZeroSection
public import WeilConjectures.AlgebraicGeometry.TraceFormula.DthFittingSmoothLocus

/-! # The relative tangent bundle of a smooth morphism

Source: current blueprint, sec-smooth-purity/sk-lem-diag-reg, order 2347;
Stacks Project, Constructions, Tags 01M2, 01LW and 01LX
(blueprint: pur9-dg-def-tangent).

The total space is relative Spec of the constructed symmetric algebra of the relative
Kähler differentials. We reuse the general structure-algebra anti-equivalence and
augmentation from VectorBundleZeroSection, without its constant-rank bundle wrappers.
No Noetherian hypothesis or global choice of relative dimension is required.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.RelativeTangentBundle

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]

/-- The symmetric algebra of Ω_{X/Y}, equipped with its quasi-coherence.
Source: blueprint pur9-dg-def-tangent; Stacks Tags 01UM, 01CL and 01M2
(blueprint: pur9-dg-def-tangent). -/
def algebraObject : ObjectProperty.FullSubcategory
    (fun A : X.CommAlgebraSheaf ↦ A.toModule.IsQuasicoherent) :=
  ⟨SymmetricAlgebraSheaf.algebra f.relativeDifferentials,
    (quasiCoherentSymmetricAlgebra_affine_comparison X f.relativeDifferentials).1⟩

/-- Relative Spec_X Sym(Ω_{X/Y}) as an affine scheme over X.
Source: blueprint pur9-dg-def-tangent; Stacks Tags 01M2 and 01LX
(blueprint: pur9-dg-def-tangent). -/
def over : ObjectProperty.FullSubcategory (fun Z : Over X ↦ IsAffineHom Z.hom) :=
  ((VectorBundleZeroSection.antiEquivalence X).inverse.obj (algebraObject f)).unop

/-- The relative tangent bundle T_{X/Y} = Spec_X Sym(Ω_{X/Y}).
Source: blueprint pur9-dg-def-tangent; Stacks Tag 01M2
(blueprint: pur9-dg-def-tangent). -/
def scheme : Scheme.{u} := (over f).obj.left

/-- The structural projection π : T_{X/Y} → X.
Source: blueprint pur9-dg-def-tangent; Stacks Tags 01M2 and 01LX
(blueprint: pur9-dg-def-tangent). -/
def projection : scheme f ⟶ X := (over f).obj.hom

/-- The unique algebra map Sym(Ω_{X/Y}) → O_X killing the degree-one generators.
This is the existing symmetric-algebra augmentation, specialized to relative differentials.
Source: blueprint pur9-dg-def-tangent; Stacks Tags 01CL and 01M2
(blueprint: pur9-dg-def-tangent). -/
def augmentation : SymmetricAlgebraSheaf.algebra f.relativeDifferentials ⟶
    Under.mk (𝟙 X.sheaf) :=
  VectorBundleZeroSection.augmentation X f.relativeDifferentials

/-- The augmentation's fully faithful inverse image, with source the identity X-scheme.
The counit identifies the structure algebra of the relative spectrum with Sym(Ω_{X/Y}).
Source: blueprint pur9-dg-def-tangent; Stacks Tags 01LX and 01M2
(blueprint: pur9-dg-def-tangent). -/
def zeroSectionOver : VectorBundleZeroSection.baseObject X ⟶ over f :=
  ((VectorBundleZeroSection.antiEquivalence X).functor.preimage
    (((VectorBundleZeroSection.antiEquivalence X).counitIso.app (algebraObject f)).hom ≫
      ObjectProperty.homMk
        (VectorBundleZeroSection.augmentationToBase X f.relativeDifferentials))).unop

/-- The zero section z : X → T_{X/Y}, contravariantly induced by the augmentation.
Source: blueprint pur9-dg-def-tangent; Stacks Tags 01LX and 01M2
(blueprint: pur9-dg-def-tangent). -/
def zeroSection : X ⟶ scheme f := (zeroSectionOver f).hom.left

/-- The symmetric algebra identified with the direct-image structure algebra of π.
Source: blueprint pur9-dg-def-tangent; Stacks Tag 01LX
(blueprint: pur9-dg-def-tangent). -/
def algebraIso : SymmetricAlgebraSheaf.algebra f.relativeDifferentials ≅
    Under.mk (⟨(projection f).c⟩ : X.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} (projection f).base).obj (scheme f).sheaf) :=
  ((ObjectProperty.ι (fun A : X.CommAlgebraSheaf ↦ A.toModule.IsQuasicoherent)).mapIso
    ((VectorBundleZeroSection.antiEquivalence X).counitIso.app (algebraObject f))).symm

/-- The affine comparison with Spec Sym_{O_X(U)}(Ω_{X/Y}(U)), induced by the
sheafification unit and the relative-spectrum algebra identification.
Source: blueprint pur9-dg-def-tangent; Stacks Tags 01CL and 01LX
(blueprint: pur9-dg-def-tangent). -/
def affineChart (U : X.affineOpens) :
    ((projection f) ⁻¹ᵁ U.1).toScheme ⟶
      Spec (.of (SymmetricAlgebraSheaf.sections f.relativeDifferentials (op U.1))) :=
  ((projection f) ⁻¹ᵁ U.1).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom
      (((algebraIso f).hom.right.hom.app (op U.1)).hom.comp
        (SymmetricAlgebraSheaf.sectionMap f.relativeDifferentials (op U.1))))

/-- The augmentation induces an X-morphism, hence π ∘ z = id_X.
Source: blueprint pur9-dg-def-tangent; Stacks Tags 01LX and 01M2
(blueprint: pur9-dg-def-tangent).

Proof: zeroSectionOver is a morphism from the identity X-scheme to the relative spectrum
in the category of schemes over X. Its defining over-category equation is exactly
zeroSection ≫ projection = 𝟙 X. -/
theorem zeroSection_comp_projection : zeroSection f ≫ projection f = 𝟙 X := by
  exact Over.w (zeroSectionOver f).hom

/-- Restriction of the zero section over an open U ⊆ X. The over-category equation
ensures its image lies in π⁻¹(U).
Source: blueprint pur9-dg-def-tangent; Stacks Tag 01LX
(blueprint: pur9-dg-def-tangent). -/
def zeroSectionRestricted (U : X.Opens) :
    U.toScheme ⟶ ((projection f) ⁻¹ᵁ U).toScheme :=
  (zeroSection f).resLE ((projection f) ⁻¹ᵁ U) U
    (by rw [← Scheme.Hom.comp_preimage, zeroSection_comp_projection f]; simp)

private theorem zeroSectionOver_map :
    (VectorBundleZeroSection.antiEquivalence X).functor.map (zeroSectionOver f).op =
      ((VectorBundleZeroSection.antiEquivalence X).counitIso.app (algebraObject f)).hom ≫
        ObjectProperty.homMk
          (VectorBundleZeroSection.augmentationToBase X f.relativeDifferentials) :=
  (VectorBundleZeroSection.antiEquivalence X).functor.map_preimage _

private theorem zeroSection_pullback (U : X.Opens) :
    (algebraIso f).hom.right.hom.app (op U) ≫
      (zeroSection f).appLE ((projection f) ⁻¹ᵁ U) U
        (by rw [← Scheme.Hom.comp_preimage, zeroSection_comp_projection f]; simp) =
      (augmentation f).right.hom.app (op U) := by
  have hn := congrArg (fun t ↦ t.hom.right.hom.app (op U)) (zeroSectionOver_map f)
  simp only [ObjectProperty.FullSubcategory.comp_hom, Under.comp_right,
    TopCat.Sheaf.comp_app] at hn
  change (zeroSection f).appLE ((projection f) ⁻¹ᵁ U) U _ =
    ((VectorBundleZeroSection.antiEquivalence X).counitIso.app
      (algebraObject f)).hom.hom.right.hom.app (op U) ≫ (augmentation f).right.hom.app (op U) at hn
  have hc := congrArg (fun t ↦ t.hom.right.hom.app (op U))
    ((VectorBundleZeroSection.antiEquivalence X).counitIso.app (algebraObject f)).inv_hom_id
  simp only [ObjectProperty.FullSubcategory.comp_hom, Under.comp_right,
    TopCat.Sheaf.comp_app, ObjectProperty.FullSubcategory.id_hom, Under.id_right,
    TopCat.Sheaf.id_app] at hc
  change ((VectorBundleZeroSection.antiEquivalence X).counitIso.app
    (algebraObject f)).inv.hom.right.hom.app (op U) ≫ _ = _
  rw [hn, ← Category.assoc, hc, Category.id_comp]

-- Use the equivalence API without unfolding the chosen quasi-inverse.

/-- The relative-spectrum affine comparison is an isomorphism, identifies the structural
projection with the scalar inclusion, and identifies the restricted zero section with
Spec of the augmentation fixing scalars and killing all degree-one generators.
Source: blueprint pur9-dg-def-tangent; Stacks Tags 01CL, 01LX and 01M2
(blueprint: pur9-dg-def-tangent).

Proof: the affine comparison for the symmetric algebra supplies the bijective
sheafification unit on U (lem-weil-pbc-quasi-coherent-symmetric-algebra-affine).
The relative-spectrum theorem (lem-weil-pbc-affine-morphism-relative-spec, parts 2--3)
therefore makes this chart invertible. The under-category equation for algebraIso
identifies scalar inclusion with projection. Full faithfulness identifies the pullback
along zeroSection with the augmentation. The core universal property
(lem-weil-pbc-quasi-coherent-symmetric-algebra-core), specialized to the zero linear map,
identifies this augmentation on affine sections with SymmetricAlgebra.algebraMapInv:
both fix constants and kill degree-one generators. Functoriality of Spec gives the
last equation under the canonical affine identification of U. -/
theorem affineChart_spec (U : X.affineOpens) :
    IsIso (affineChart f U) ∧
      (affineChart f U ≫
        Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.obj (op U.1))
          (SymmetricAlgebraSheaf.sections f.relativeDifferentials (op U.1)))) ≫
            U.2.isoSpec.inv = (projection f) ∣_ U.1) ∧
      (zeroSectionRestricted f U.1 ≫ affineChart f U =
        U.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
          (SymmetricAlgebra.algebraMapInv (R := X.presheaf.obj (op U.1))
            (M := f.relativeDifferentials.val.obj (op U.1))).toRingHom)) := by
  have hsec : IsIso (CommRingCat.ofHom
      (SymmetricAlgebraSheaf.sectionMap f.relativeDifferentials (op U.1))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ((quasiCoherentSymmetricAlgebra_affine_comparison X f.relativeDifferentials).2 U)
  have : IsAffineHom (projection f) := (over f).property
  have : IsIso (((projection f) ⁻¹ᵁ U.1).toSpecΓ) :=
    (U.2.preimage (projection f)).isoSpec.isIso_hom
  have : IsIso ((algebraIso f).hom.right.hom) := by infer_instance
  have : IsIso ((algebraIso f).hom.right.hom.app (op U.1)) := by infer_instance
  refine ⟨?_, ?_⟩
  · change IsIso (((projection f) ⁻¹ᵁ U.1).toSpecΓ ≫
      Spec.map (CommRingCat.ofHom
        (SymmetricAlgebraSheaf.sectionMap f.relativeDifferentials (op U.1)) ≫
          (algebraIso f).hom.right.hom.app (op U.1)))
    infer_instance
  · constructor
    · have hscalar : CommRingCat.ofHom (algebraMap (X.presheaf.obj (op U.1))
          (SymmetricAlgebraSheaf.sections f.relativeDifferentials (op U.1))) ≫
          CommRingCat.ofHom (SymmetricAlgebraSheaf.sectionMap f.relativeDifferentials (op U.1)) ≫
          (algebraIso f).hom.right.hom.app (op U.1) = (projection f).app U.1 := by
        exact congrArg (fun q ↦ q.hom.app (op U.1)) (Under.w (algebraIso f).hom)
      change (((projection f) ⁻¹ᵁ U.1).toSpecΓ ≫
        Spec.map (CommRingCat.ofHom
          (SymmetricAlgebraSheaf.sectionMap f.relativeDifferentials (op U.1)) ≫
          (algebraIso f).hom.right.hom.app (op U.1))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.obj (op U.1))
          (SymmetricAlgebraSheaf.sections f.relativeDifferentials (op U.1)))) ≫ U.2.isoSpec.inv = _
      simp only [Category.assoc, ← Spec.map_comp_assoc]
      rw [hscalar, Scheme.Opens.toSpecΓ_naturality_assoc]
      simp
    · have hzero : CommRingCat.ofHom
          (SymmetricAlgebraSheaf.sectionMap f.relativeDifferentials (op U.1)) ≫
          (algebraIso f).hom.right.hom.app (op U.1) ≫
          (zeroSection f).appLE ((projection f) ⁻¹ᵁ U.1) U.1
            (by rw [← Scheme.Hom.comp_preimage, zeroSection_comp_projection f]; simp) =
          CommRingCat.ofHom (SymmetricAlgebra.algebraMapInv
            (R := X.presheaf.obj (op U.1))
            (M := f.relativeDifferentials.val.obj (op U.1))).toRingHom := by
        rw [zeroSection_pullback]
        apply CommRingCat.hom_ext
        exact RingHom.ext
          ((VectorBundleZeroSection.augmentation_spec X f.relativeDifferentials).2.2 U.1)
      change (zeroSection f).resLE ((projection f) ⁻¹ᵁ U.1) U.1 _ ≫
        ((projection f) ⁻¹ᵁ U.1).toSpecΓ ≫
          Spec.map (CommRingCat.ofHom
            (SymmetricAlgebraSheaf.sectionMap f.relativeDifferentials (op U.1)) ≫
            (algebraIso f).hom.right.hom.app (op U.1)) = _
      rw [← Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc]
      simp only [← Spec.map_comp, Category.assoc] at hzero ⊢
      rw [hzero]
      rfl

attribute [local irreducible] VectorBundleZeroSection.antiEquivalence

end AlgebraicGeometry.RelativeTangentBundle
