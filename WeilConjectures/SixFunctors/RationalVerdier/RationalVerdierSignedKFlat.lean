/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralVerdier.IntegralVerdierModels
import all WeilConjectures.SixFunctors.IntegralVerdier.IntegralVerdierSignedCalculus
import all WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorSymmetryRepresentatives

/-! # Naturality of normalized signed symmetry on K-flat representatives

Source: Stacks 06YL and 08J9; blueprint thm-coef-rational-verdier, proof step 5
(blueprint: lem-coef-rational-verdier-signed-kflat). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite
open scoped TensorProduct

namespace WeilConjectures.RationalVerdier

private theorem signed_chain_unique (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (P Q : CochainComplex (IntegralHom.Modules.{u, u} X R) ℤ)
    (s t : ((IntegralHom.totalTensor.{u, u} X R).obj P).obj Q ⟶
      ((IntegralHom.totalTensor.{u, u} X R).obj Q).obj P)
    (hs : ∀ (i j : ℤ) (U : X.ProEtᵒᵖ)
      (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U),
      (s.f (i + j)).val.app U (IntegralHom.totalPair.{u, u} X R P Q i j U x y) =
        (t.f (i + j)).val.app U (IntegralHom.totalPair.{u, u} X R P Q i j U x y)) :
    s = t := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
    (K₁ := P) (K₂ := Q) (F := IntegralHom.ordinaryTensor.{u, u} X R) (c := .up ℤ)
  intro i j hij
  subst n
  apply CategoryTheory.RingedForgetTensorTransposition.pure_ext.{u + 1, u, u}
    (ProEt.topology X) R (P.X i) (Q.X j) _
  intro U x y
  exact hs i j U x y

/-- All signed symmetries on one ordinary presentation agree at literal K-flat pairs.
Source: Stacks 06YL and 08J9, the Koszul formula
(blueprint: lem-coef-rational-verdier-signed-kflat).
Proof: choose the two representative chain swaps. Their specified values on every
local homogeneous pure tensor coincide. Sheafified tensor generators and the direct-sum
totalization's inclusions detect equality, hence the chain maps are equal. Their
representative equations give the asserted derived equality. -/
private theorem signed_swap_eq (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : IntegralHom.TensorPresentation.{u, u} X R)
    (s t : IntegralVerdier.SignedSymmetry X R a)
    (P Q : CochainComplex (IntegralHom.Modules.{u, u} X R) ℤ)
    (hP : IntegralHom.flat.{u, u} X R P) (hQ : IntegralHom.flat.{u, u} X R Q) :
    (s.swap (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom =
      (t.swap (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom := by
  obtain ⟨f, hf, hsf⟩ := s.representative P Q hP hQ
  obtain ⟨g, hg, htg⟩ := t.representative P Q hP hQ
  have hfg : f = g := signed_chain_unique X R P Q f g
    (fun i j U x y ↦ (hf i j U x y).trans (hg i j U x y).symm)
  rw [← hsf, ← htg, hfg]

/-- The signed representative equation is natural for K-flat chain maps, for any
signed symmetry on the normalized tensor presentation.
Source: Stacks 06YL and 08J9; blueprint thm-coef-rational-verdier, proof step 5
(blueprint: lem-coef-rational-verdier-signed-kflat).
Proof: construct the natural signed symmetry on this presentation by transporting
the native symmetric monoidal braiding. The homogeneous Koszul formula identifies
its swaps with those of the supplied symmetry on all four K-flat pairs. Substitute
these equalities in the native naturality square. No naturality on arbitrary derived
objects is asserted or assumed. -/
theorem signed_kflat_natural (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : IntegralHom.TensorPresentation.{u, u} X R)
    (s : IntegralVerdier.SignedSymmetry X R a)
    (P P' Q Q' : CochainComplex (IntegralHom.Modules.{u, u} X R) ℤ)
    (hP : IntegralHom.flat.{u, u} X R P)
    (hP' : IntegralHom.flat.{u, u} X R P')
    (hQ : IntegralHom.flat.{u, u} X R Q)
    (hQ' : IntegralHom.flat.{u, u} X R Q') (f : P ⟶ P') (g : Q ⟶ Q') :
    a.tensor.map (Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) ≫
        (s.swap (DerivedCategory.Q.obj P') (DerivedCategory.Q.obj Q')).hom =
      (s.swap (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫
        a.tensor.map (Prod.mkHom (DerivedCategory.Q.map g) (DerivedCategory.Q.map f)) := by
  obtain ⟨t, ht⟩ := IntegralVerdier.presentation_symmetry X R a
  rw [signed_swap_eq X R a s t P Q hP hQ,
    signed_swap_eq X R a s t P' Q' hP' hQ']
  exact ht _ _ _ _ (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)

end WeilConjectures.RationalVerdier
