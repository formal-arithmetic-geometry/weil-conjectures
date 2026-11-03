/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.RealSheaves.Setup.RealSheavesSetup
public import WeilConjectures.AlgebraicGeometry.RealCondensedFibre.RealCondensedFibreFunctoriality
public import WeilConjectures.SmoothPurity.CondensedWeilModules
public import WeilConjectures.AlgebraicGeometry.CondensedLisseMonodromy.CondensedLisseMonodromy
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.Compactification.GeometricallyConnectedAlgebraicClosure
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.TypeTags.Basic

/-! # The Frobenius conjugation convention on finite covers

Source: prop-wf-weil-sheaf-representation-equivalence.proof.md, Frobenius descent.
(blueprint: lem-wrp-condensed-weil-coordinates-conjugation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.CondensedWeilRepresentation

private theorem eqToIso_conjugacy {C : Type*} [Category C] {X Y Z : C}
    (p : X = Y) (q : X = Z) (r : Y = Z) (R : Aut Y) (J : Aut Z)
    (he : eqToIso p ≪≫ R ≪≫ (eqToIso p).symm =
      eqToIso q ≪≫ J ≪≫ (eqToIso q).symm) :
    (eqToIso r).symm ≪≫ R ≪≫ eqToIso r = J := by
  subst p
  subst q
  simpa using he

attribute [local irreducible] FiniteEtale.fiber

private theorem pullbackPathIso_pre_over {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : X ⟶ X) (hh : h ≫ f = f) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ X) (a : Aut (FiniteEtale.fiber s))
    (hs : (s ≫ h) ≫ f = s ≫ f) :
    (eqToIso (congrArg FiniteEtale.fiber hs)).symm ≪≫
      FiniteEtale.pullbackPathIso f (FiniteEtale.pullbackPathIso h a) ≪≫
        eqToIso (congrArg FiniteEtale.fiber hs) = FiniteEtale.pullbackPathIso f a := by
  exact eqToIso_conjugacy
    (congrArg FiniteEtale.fiber (Category.assoc s h f).symm)
    (congrArg FiniteEtale.fiber (congrArg (fun z ↦ s ≫ z) hh))
    (congrArg FiniteEtale.fiber hs) _ _
    ((FiniteEtale.pullbackPathIso_comp h f a).symm.trans
      (FiniteEtale.pullbackPathIso_congr hh a))

variable (D : WeilConjectures.FiniteFieldDatum.{u})
  (C₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom]
  (N : RealCondensedFibre.Context.{u}) (j : N.X ≅ (D.geometricFiber C₀).left)
  [ConnectedSpace C₀.left]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ N.X)
  (G : ProfiniteGrp.{u})
  [∀ Q, MulAction G ((FiniteEtale.fiber (t ≫ projection D C₀ N j)).obj Q)]
  [PreGaloisCategory.IsFundamentalGroup (FiniteEtale.fiber (t ≫ projection D C₀ N j)) G]
  (γ : Group D C₀ N j t G) (A : Coordinates D C₀ N j t G γ)

/-- The recorded arithmetic normalization forces the inverse-conjugation twist of the
geometric action. This uses the actual finite-cover paths in Coordinates.

Source: prop-wf-weil-sheaf-representation-equivalence.proof.md, Frobenius descent.
(blueprint: lem-wrp-condensed-weil-coordinates-conjugation).

Proof: Frobenius fixes the projection to the arithmetic curve. Consequently its induced
path on arithmetic covers is the original loop, conjugated by the equality of projected
basepoints. Push the displayed conjugated geometric loop through the projection, use
path composition and inverse compatibility, and insert that equality. The outer paths
are the specified arithmetic action of gamma and its inverse. The arithmetic
fundamental group acts faithfully on finite covers, so the first coordinates agree.
Both Weil elements have degree zero, giving equality of their second coordinates. -/
theorem Coordinates.conjugation (a : A.P) :
    (A.geometric
      ((PreGaloisCategory.toAutMulEquiv (FiniteEtale.fiber t) A.P).symm
        (A.path ≪≫ FiniteEtale.pullbackPathIso (frobenius D C₀ N j).hom
          (PreGaloisCategory.toAut (FiniteEtale.fiber t) A.P a) ≪≫ A.path.symm)) :
        Group D C₀ N j t G) = γ⁻¹ * (A.geometric a).val * γ := by
  let p := projection D C₀ N j
  let f := (frobenius D C₀ N j).hom
  have hp : f ≫ p = p := by
    change (j.hom ≫ (D.geometricFrobenius C₀).hom ≫ j.inv) ≫
      (j.hom ≫ pullback.fst C₀.hom _) = j.hom ≫ pullback.fst C₀.hom _
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact congrArg (fun h ↦ j.hom ≫ h) (D.galoisMap_projections C₀.hom _).1
  let δ := eqToIso (congrArg FiniteEtale.fiber A.point_eq)
  let β := FiniteEtale.pullbackPathIso p A.path
  let r := PreGaloisCategory.toAut (FiniteEtale.fiber t) A.P a
  have ht := pullbackPathIso_pre_over p f hp t r A.point_eq
  have ht' : FiniteEtale.pullbackPathIso p (FiniteEtale.pullbackPathIso f r) =
      δ ≪≫ FiniteEtale.pullbackPathIso p r ≪≫ δ.symm := by
    calc
      _ = δ ≪≫ (δ.symm ≪≫ _ ≪≫ δ) ≪≫ δ.symm := by
        simp only [Iso.trans_assoc, Iso.self_symm_id_assoc, Iso.self_symm_id, Iso.trans_refl]
      _ = _ := congrArg (fun z ↦ δ ≪≫ z ≪≫ δ.symm) ht
  apply Subtype.ext
  apply Prod.ext
  · apply (PreGaloisCategory.toAutMulEquiv
      (FiniteEtale.fiber (t ≫ projection D C₀ N j)) G).injective
    change PreGaloisCategory.toAut _ G _ =
      PreGaloisCategory.toAut _ G (γ.val.1⁻¹ * (A.geometric a).val.val.1 * γ.val.1)
    rw [map_mul, map_mul, map_inv, A.arithmetic, A.arithmetic]
    rw [← PreGaloisCategory.toAutMulEquiv_apply, MulEquiv.apply_symm_apply]
    rw [FiniteEtale.pullbackPathIso_trans, FiniteEtale.pullbackPathIso_trans,
      FiniteEtale.pullbackPathIso_symm]
    rw [ht']
    rw [← A.path_arithmetic]
    simp only [Aut.Aut_mul_def, Aut.Aut_inv_def, Iso.trans_symm, Iso.trans_assoc]
    rfl
  · change degree D C₀ N j t G (A.geometric _) =
      degree D C₀ N j t G (γ⁻¹ * (A.geometric a).val * γ)
    rw [(A.geometric _).property, map_mul, map_mul, map_inv,
      (A.geometric a).property, mul_one, inv_mul_cancel]

end AlgebraicGeometry.ProEtale.CondensedWeilRepresentation
