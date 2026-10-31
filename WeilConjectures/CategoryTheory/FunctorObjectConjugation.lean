/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.NatIso
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-! Conjugating a functor by an arbitrary family of object automorphisms.
Source: Mathlib's definition of a functor and natural isomorphism; the change of
presentation in Zheng, Construction 5.25.
(blueprint: lem-sf-functor-comparison-normalization)
-/

@[expose] public section
set_option autoImplicit false
universe v₁ v₂ v₃ u₁ u₂ u₃
namespace CategoryTheory.Functor

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  (F : A ⥤ B)

/-- The automorphisms that turn a comparison into the equality comparison.
They are explicit preimages under a fully faithful functor, so no arbitrary
existence witness is chosen.
Source: Mathlib, `Functor.FullyFaithful.preimageIso` and `NatIso.naturality_1`.
(blueprint: lem-sf-functor-comparison-normalization) -/
def comparisonNormalizer {D : Type u₃} [Category.{v₃} D]
    (J : B ⥤ D) (hJ : J.FullyFaithful) (G : A ⥤ D) (e : F ⋙ J ≅ G)
    (hobj : ∀ X : A, (F ⋙ J).obj X = G.obj X) (X : A) : F.obj X ≅ F.obj X :=
  hJ.preimageIso (e.app X ≪≫ (eqToIso (hobj X)).symm)

/-- Normalize a comparison to strict equality while preserving source objects.
Proof: map the conjugated morphism through the fully faithful functor. The
preimage equations replace the conjugating automorphisms by the comparison
components and the equality transports. Naturality cancels the comparison
components, leaving precisely the map equation of `Functor.ext`.
Source: Mathlib's fully faithful preimage and naturality formulas.
(blueprint: lem-sf-functor-comparison-normalization) -/
theorem copyObj_comparisonNormalizer_comp {D : Type u₃} [Category.{v₃} D]
    (J : B ⥤ D) (hJ : J.FullyFaithful) (G : A ⥤ D) (e : F ⋙ J ≅ G)
    (hobj : ∀ X : A, (F ⋙ J).obj X = G.obj X) :
    F.copyObj F.obj (F.comparisonNormalizer J hJ G e hobj) ⋙ J = G := by
  refine Functor.ext hobj ?_
  intro X Y f
  change J.map (_ ≫ F.map f ≫ _) = _
  simp only [Functor.map_comp, comparisonNormalizer,
    FullyFaithful.preimageIso_inv, FullyFaithful.preimageIso_hom,
    FullyFaithful.map_preimage, Iso.trans_inv, Iso.trans_hom,
    Iso.symm_inv, Iso.symm_hom, eqToIso.hom, eqToIso.inv, Iso.app_hom, Iso.app_inv]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg (fun a ↦ eqToHom (hobj X) ≫ a ≫ eqToHom (hobj Y).symm)
      (NatIso.naturality_1 e f)

end CategoryTheory.Functor
