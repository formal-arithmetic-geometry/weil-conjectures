/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.RelativeDifferentialsAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.DifferentialsSections
import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.AlgebraicGeometry.Modules.AffineHom
import WeilConjectures.AlgebraicGeometry.Modules.FreeComplexExact
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Ordered differentials of an affine étale coordinate chart
Source: current blueprint orientation chart proof, Step 2; Stacks Tags 01V7 and 02GU.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct

namespace AlgebraicGeometry.DiagonalDifferenceReesFrame

set_option backward.isDefEq.respectTransparency false in
private theorem basis_exists {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    (d : ℕ) (h : U ⟶ V) (c : U ⟶ AffineSpace (ULift.{u} (Fin d)) V)
    [Etale c] (hc : c ≫ (AffineSpace (ULift.{u} (Fin d)) V ↘ V) = h) :
    ∃ b : Module.Basis (ULift.{u} (Fin d)) Γ(U, ⊤) Γ(h.relativeDifferentials, ⊤),
      ∀ i, b i = h.relativeDifferentialsDerivation.d (X := op ⊤)
        (c.appTop (AffineSpace.coord V i)) := by
  classical
  let A := Γ(V, ⊤)
  let B := Γ(U, ⊤)
  let P := MvPolynomial (ULift.{u} (Fin d)) A
  let ψ := h.appLE ⊤ ⊤ (by simp)
  let φ : P →+* B := MvPolynomial.eval₂Hom ψ.hom
    (fun i ↦ c.appTop (AffineSpace.coord V i))
  let cP := c ≫ (AffineSpace.isoOfIsAffine (ULift.{u} (Fin d)) V).hom
  have hcP : cP.specStructureMap ⊤ = CommRingCat.ofHom φ := by
    simp only [cP, Scheme.Hom.specStructureMap, Scheme.Hom.appLE_top_top,
      Scheme.Hom.comp_appTop, AffineSpace.isoOfIsAffine_hom_appTop,
      Category.assoc, Iso.inv_hom_id_assoc]
    apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext'
    · ext a
      simp [φ, ψ, Scheme.Hom.appLE_top_top, ← CommRingCat.comp_apply,
        ← Scheme.Hom.comp_appTop, hc]
    · intro i
      change c.appTop ((MvPolynomial.eval₂Hom
        (AffineSpace (ULift.{u} (Fin d)) V ↘ V).appTop.hom
        (AffineSpace.coord V)) (MvPolynomial.X i)) = φ (MvPolynomial.X i)
      rw [MvPolynomial.eval₂Hom_X']
      exact (MvPolynomial.eval₂Hom_X' ψ.hom
        (fun i ↦ c.appTop (AffineSpace.coord V i)) i).symm
  have he : φ.Etale := by
    have hh : Etale (Spec.map (CommRingCat.ofHom φ)) := by
      rw [← hcP, ← cP.fromSpec_comp_eq_specMap (isAffineOpen_top U)]
      infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp hh
  let : Algebra A B := ψ.hom.toAlgebra
  let : Algebra P B := φ.toAlgebra
  have : IsScalarTower A P B := .of_algebraMap_eq fun a ↦ by
    change ψ a = φ (MvPolynomial.C a)
    exact (MvPolynomial.eval₂_C _ _ _).symm
  have : Algebra.FormallyEtale P B := (RingHom.etale_algebraMap.mp he).formallyEtale
  let E := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale A P B
  obtain ⟨e, heD⟩ : ∃ e : KaehlerDifferential A B ≃ₗ[B]
      Γ(h.relativeDifferentials, ⊤), ∀ a : B,
      e (KaehlerDifferential.D A B a) = h.relativeDifferentialsDerivation.d (X := op ⊤) a := by
    exact relativeDifferentials_affine_sections h
        ⟨⊤, isAffineOpen_top U⟩ ⟨⊤, isAffineOpen_top V⟩ (by simp)
  let b := ((KaehlerDifferential.mvPolynomialBasis A (ULift.{u} (Fin d))).baseChange B).map
    (E.trans e)
  refine ⟨b, fun i ↦ ?_⟩
  dsimp only [b]
  rw [Module.Basis.map_apply, Module.Basis.baseChange_apply,
    KaehlerDifferential.mvPolynomialBasis_apply]
  change e (E (1 ⊗ₜ[P] KaehlerDifferential.D A P (MvPolynomial.X i))) = _
  have hEi : E (1 ⊗ₜ[P] KaehlerDifferential.D A P (MvPolynomial.X i)) =
      KaehlerDifferential.D A B (φ (MvPolynomial.X i)) := by
    apply E.symm.injective
    rw [E.symm_apply_apply]
    exact (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap
      A P B (MvPolynomial.X i)).symm
  rw [hEi]
  have hi : φ (MvPolynomial.X i) = c.appTop (AffineSpace.coord V i) :=
    MvPolynomial.eval₂Hom_X' ψ.hom (fun i ↦ c.appTop (AffineSpace.coord V i)) i
  rw [hi]
  exact heD _

set_option backward.isDefEq.respectTransparency false in
/-- The ordered differential basis of an affine étale chart gives a free sheaf frame.
Source: orientation chart proof, Step 2
(blueprint: lem-pur-etale-coordinate-differential-basis).

Proof: étale base change carries the polynomial Kähler basis to Ω(B/A). The affine
comparison carries it to global differential sections. Extend that basis and its
inverse to quasi-coherent sheaf maps by affine equivalence. They are mutually
inverse because their global section maps are. This includes rank zero and empty U. -/
theorem coordinate_differential_frame {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    (d : ℕ) (h : U ⟶ V) [SmoothOfRelativeDimension d h] (c : U ⟶ AffineSpace (ULift.{u} (Fin d)) V)
    [Etale c] (hc : c ≫ (AffineSpace (ULift.{u} (Fin d)) V ↘ V) = h) :
    ∃ e : SheafOfModules.free (R := U.ringCatSheaf) (ULift.{u} (Fin d)) ≅
        h.relativeDifferentials,
      ∀ i : ULift.{u} (Fin d), e.hom.val.app (op ⊤)
        ((SheafOfModules.ιFree (R := U.ringCatSheaf) i).val.app (op ⊤)
          (1 : Γ(U, ⊤))) = h.relativeDifferentialsDerivation.d (X := op ⊤)
            (c.appTop (AffineSpace.coord V i)) := by
  classical
  have : h.relativeDifferentials.IsFiniteLocallyFreeOfRank d :=
    h.isFiniteLocallyFreeOfRank_relativeDifferentials d
  have : h.relativeDifferentials.IsLocallyFree :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isLocallyFree h.relativeDifferentials d
  obtain ⟨b, hb⟩ := basis_exists d h c hc
  let E := (freeSectionsEquivOpens ⊤ (ULift.{u} (Fin d))).trans b.equivFun.symm
  obtain ⟨f, hf⟩ := exists_hom_app_top_eq_of_isAffine E.toLinearMap
  obtain ⟨g, hg⟩ := exists_hom_app_top_eq_of_isAffine E.symm.toLinearMap
  have hfg : f ≫ g = 𝟙 _ := by
    apply hom_ext_of_isAffine
    intro m
    change g.app ⊤ (f.app ⊤ m) = m
    rw [hf, hg]
    exact E.symm_apply_apply m
  have hgf : g ≫ f = 𝟙 _ := by
    apply hom_ext_of_isAffine
    intro m
    change f.app ⊤ (g.app ⊤ m) = m
    rw [hg, hf]
    exact E.apply_symm_apply m
  refine ⟨⟨f, g, hfg, hgf⟩, fun i ↦ ?_⟩
  change f.app ⊤ _ = _
  rw [hf]
  change b.equivFun.symm ((freeSectionsEquivOpens ⊤ (ULift.{u} (Fin d))) _) = _
  rw [show (freeSectionsEquivOpens ⊤ (ULift.{u} (Fin d)))
      ((SheafOfModules.ιFree (R := U.ringCatSheaf) i).val.app (op ⊤)
        (1 : Γ(U, ⊤))) = Pi.single i 1 by
    ext j
    change Hom.app (freeπ (X := U) j) ⊤
      (Hom.app (SheafOfModules.ιFree (R := U.ringCatSheaf) i) ⊤ (1 : Γ(U, ⊤))) = _
    rw [freeπ_app_ιFree_app_opens]
    simp [Pi.single_apply, eq_comm]]
  simpa using hb i

end AlgebraicGeometry.DiagonalDifferenceReesFrame
