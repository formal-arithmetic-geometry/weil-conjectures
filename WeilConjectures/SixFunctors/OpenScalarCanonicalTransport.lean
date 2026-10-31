/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenScalarCompTransport
import all WeilConjectures.SecSmoothPurity.ProEtaleDirectImageScalarCocycle

/-! Canonical pullback cocycle after presentation transport.

Source: Stacks Project, sites-cohomology.tex, Tags 07A4, 07A6 and 0D6D.
(blueprint: lem-sp-open-scalar-coefficient-canonical-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme SheafOfModules WeilConjectures
namespace AlgebraicGeometry.ProEtale.OpenScalarTensor

/-- The canonical coefficient cocycle before transport to arbitrary scalar presentations,
the inverse form of `scalarPullbackCocycle`. -/
private theorem canonical_coefficient_composition
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) {U X : Scheme.{u}} (j : U ⟶ X)
    (Q : proEtaleDerivedCategory X A) :
    (scalarExtensionFunctor ψ U).map
        ((directImageScalarPullbackIso φ j).inv.app Q) ≫
      (directImageScalarPullbackIso ψ j).inv.app ((scalarExtensionFunctor φ X).obj Q) ≫
      (proEtaleConstantRingDerivedPullback C j).map
        ((scalarExtensionFunctor_composition φ ψ X).hom.app Q) =
    (scalarExtensionFunctor_composition φ ψ U).hom.app
        ((proEtaleConstantRingDerivedPullback A j).obj Q) ≫
      (directImageScalarPullbackIso (ψ.comp φ) j).inv.app Q := by
  have h := scalarPullbackCocycle φ ψ j Q
  dsimp only [scalarExtensionFunctor] at h ⊢
  apply (cancel_mono ((directImageScalarPullbackIso (ψ.comp φ) j).hom.app Q)).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [h]
  simp only [Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

/-- The canonical inverse-lambda cocycle for a chosen scalar presentation, with the
compositor written in transported published coordinates.
Source: Stacks 07A4, 07A6 and 0D6D.
(blueprint: lem-sp-open-scalar-coefficient-canonical-transport).

Proof: expand `lambda` and `transportedScalarComp` into the presentation isomorphisms
`scalarIso`, the published comparison `tensorPullbackIso` (which is
`directImageScalarPullbackIso`) and the canonical compositor. Naturality of `scalarIso` for
`ψ` on `U` moves it to the front of both sides; the `scalarIso` inverse/hom pairs for `ψ` on
`X` and for `ψ ∘ φ` on `U` cancel, and naturality of the inverse pullback comparison for `ψ`
cancels the pair for `φ` on `X`. What remains, after the common first and last factors, is
`canonical_coefficient_composition`, the inverse form of the direct-image scalar cocycle.
-/
theorem scalar_pullback_coefficient_canonical_transport (m : Models.{u}) :
    ∀ {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
      [Finite A] [Finite B] [Finite C] (φ : A →+* B) (ψ : B →+* C)
      {U X : Scheme.{u}} (j : U ⟶ X)
      (Q : proEtaleDerivedCategory X A),
      (scalar m ψ U).map ((lambda m φ j).inv.app Q) ≫
        (lambda m ψ j).inv.app ((scalar m φ X).obj Q) ≫
        (constantPullback (A := C) j).map
          ((transportedScalarComp m φ ψ X).hom.app Q) =
      (transportedScalarComp m φ ψ U).hom.app
          ((constantPullback (A := A) j).obj Q) ≫
        (lambda m (ψ.comp φ) j).inv.app Q := by
  intro A B C _ _ _ _ _ _ φ ψ U X j Q
  have h := canonical_coefficient_composition φ ψ j Q
  have ht : ∀ {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B),
      tensorPullbackIso f j = directImageScalarPullbackIso f j := fun _ ↦ rfl
  simp only [lambda, transportedScalarComp, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv,
    Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.comp_obj, Functor.map_comp, Category.assoc, ht]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
    (scalarIso m ψ U).hom.naturality_assoc]
  slice_lhs 4 5 => rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  slice_rhs 4 5 => rw [Iso.inv_hom_id_app]
  simp only [Category.id_comp, Functor.map_comp, Category.assoc]
  congr 1
  have hn : (directImageScalarPullbackIso ψ j).inv.app ((scalar m φ X).obj Q) ≫
      (constantPullback j).map ((scalarExtensionFunctor ψ X).map ((scalarIso m φ X).hom.app Q)) =
      (scalarExtension ψ U).map ((constantPullback j).map ((scalarIso m φ X).hom.app Q)) ≫
        (directImageScalarPullbackIso ψ j).inv.app ((scalarExtension φ X).obj Q) :=
    ((directImageScalarPullbackIso ψ j).inv.naturality ((scalarIso m φ X).hom.app Q)).symm
  rw [reassoc_of% hn]
  slice_lhs 3 4 => rw [← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rw [Category.id_comp]
  dsimp only [scalarExtensionFunctor] at h ⊢
  congr 1
  rw [Category.assoc]
  exact (reassoc_of% h) _

end AlgebraicGeometry.ProEtale.OpenScalarTensor
