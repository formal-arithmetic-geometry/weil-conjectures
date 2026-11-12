/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedSwapComplex

/-! # The native chain swap obtained from the ringed signed swap

Source: Stacks 06YU and 0FPT, signed total tensor symmetry.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option Elab.async false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

set_option trace.profiler true in
private theorem ringedSwap_summand
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u})
    (P Q : CochainComplex (RingedTensorModules.{u, u, u} J R) ℤ)
    (p q n : ℤ) (hpq : p + q = n) (hqp : q + p = n) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients R
    letI := SheafOfModules.monoidalCategory R
    letI := SheafOfModules.symmetricCategory R
    RingedForgetTensorTransposition.tensorSummand J R P Q p q n hpq ≫
        (CochainComplex.Monoidal.braiding P Q).hom.f n =
      ((p * q).negOnePow : ℤ) • ((β_ (P.X p) (Q.X q)).hom ≫
        RingedForgetTensorTransposition.tensorSummand J R Q P q p n hqp) := by
  letI := SheafOfModules.isMonoidal_W_independentCoefficients R
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.symmetricCategory R
  simpa only [RingedForgetTensorTransposition.tensorSummand, Preadditive.zsmul_comp] using
    (CochainComplex.Monoidal.ι_braiding_hom (K := P) (L := Q) p q n hpq)

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  (b : NativeWeilTensorRingedBridge k₀ l X)
  (T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
    ProEtaleWeilSheaf k₀ l X)
  [T.Additive] [∀ P, (T.obj P).Additive]
  [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
  (adj : T ⊣₂ ihomBifunctor k₀ l X)
  (A : NativeWeilRingedTensorComplexes b T adj)

/-- The underived native swap induced by the ringed braiding.
Source: Stacks 03EK, 06YU.
(blueprint: new-sf-native-weil-ringed-swap-summand).

This is the fully faithful preimage of an explicit composite of isomorphisms. -/
def nativeRingedSwapUnderived (P Q : ProEtaleWeilSheaf k₀ l X) :
    (T.obj Q).obj P ≅ (T.obj P).obj Q := by
  letI := SheafOfModules.isMonoidal_W_independentCoefficients b.R
  letI := SheafOfModules.monoidalCategory b.R
  letI := SheafOfModules.symmetricCategory b.R
  exact b.native.functor.preimageIso (A.underived Q P ≪≫
    β_ (b.native.functor.obj P) (b.native.functor.obj Q) ≪≫ (A.underived P Q).symm)

set_option trace.profiler true in
/-- The native signed chain swap on one homogeneous tensor summand.
Source: Stacks 06YU, 0FPT.
(blueprint: new-sf-native-weil-ringed-swap-summand).

Proof: apply the fully faithful ringed equivalence and postcompose by the target
chain comparison. Its defining square moves the swap to the ringed total. Apply
the two summand normalizations and the signed braiding formula. The two signs
on each side agree since p*q=q*p. Cancel the underived comparison and reflect
the equality through the equivalence. -/
theorem nativeRingedSwapComplex_summand
    (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (p q n : ℤ) (hpq : p + q = n) (hqp : q + p = n) :
    HomologicalComplex.ιMapBifunctor Q P T (.up ℤ) q p n hqp ≫
        (nativeRingedSwapComplex b T adj A P Q).hom.f n =
      ((p * q).negOnePow : ℤ) •
        ((nativeRingedSwapUnderived b T adj A (P.X p) (Q.X q)).hom ≫
          HomologicalComplex.ιMapBifunctor P Q T (.up ℤ) p q n hpq) := by
  letI := SheafOfModules.isMonoidal_W_independentCoefficients b.R
  letI := SheafOfModules.monoidalCategory b.R
  letI := SheafOfModules.symmetricCategory b.R
  let E := b.native.functor
  let Ec := E.mapHomologicalComplex (.up ℤ)
  let s := nativeRingedSwapUnderived b T adj A (P.X p) (Q.X q)
  have hs : E.map s.hom ≫ (A.underived (P.X p) (Q.X q)).hom =
      (A.underived (Q.X q) (P.X p)).hom ≫
        (β_ (E.obj (P.X p)) (E.obj (Q.X q))).hom := by
    simp only [E, s, nativeRingedSwapUnderived, Functor.preimageIso_hom,
      Functor.map_preimage, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  have h := congrArg (fun f ↦ f.f n) (nativeRingedSwapComplex_square b T adj A P Q)
  change E.map ((nativeRingedSwapComplex b T adj A P Q).hom.f n) ≫
    (A.chain P Q).hom.f n =
      (A.chain Q P).hom.f n ≫
        (CochainComplex.Monoidal.braiding (Ec.obj P) (Ec.obj Q)).hom.f n at h
  apply E.map_injective
  apply (cancel_mono ((A.chain P Q).hom.f n)).1
  simp only [Functor.map_comp, Functor.map_zsmul, Preadditive.zsmul_comp,
    Category.assoc]
  rw [h, ← Category.assoc, A.summand Q P q p n hqp hpq]
  rw [A.summand P Q p q n hpq hqp]
  simp only [nativeRingedTensorSign, zsmul_eq_smul, Preadditive.comp_zsmul,
    Preadditive.zsmul_comp, Category.assoc]
  have hb := ringedSwap_summand b.J b.R (Ec.obj P) (Ec.obj Q) p q n hpq hqp
  rw [hb, reassoc_of% hs]
  simp only [Preadditive.comp_zsmul, mul_comm q p]
  rfl

end AlgebraicGeometry.ProEtaleWeilSheaf
