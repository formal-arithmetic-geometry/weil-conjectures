/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q76
-/
module

public import Sheaf.Algebra.Homology.StrictScalarHomChain
import Sheaf.Algebra.Homology.SliceScalarHomChainAdjunction

/-! # Scalar evaluation on actual product Hom complexes

Source: Stacks Project, sites-modules.tex, Tags 03CY and 03CZ;
sites-cohomology.tex, Section 0A8X (section-hom-complexes).
(blueprint: lem-sfb-scalar-hom-chain-evaluation).

We reuse the existing normalized tensor.{c, v, u}, extension, and local evaluation definitions.
The assertion here concerns alpha and sigma and their input naturality only.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v u
open CategoryTheory Opposite

namespace SheafOfModules.StrictScalarHom

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  [HasWeakSheafify J AddCommGrpCat.{max c v u}]

private theorem adjunction_exists
    {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S) :
    ∃ D : NormalizedOrdinaryAdjunction.{c, v, u} φ,
      Nonempty (ScalarHomAdjunctionChains.{c, v, u} D.extension) := by
  let _ : ∀ W : C, (J.over W).HasSheafCompose
      (forget₂ CommRingCat.{max c v u} RingCat.{max c v u}) := fun W ↦ inferInstance
  let _ : ∀ W : C, (J.over W).WEqualsLocallyBijective AddCommGrpCat.{max c v u} :=
    fun W ↦ wEqualsLocallyBijective_coefficientUniverse.{max c v, v, max c v u}
      (J := J.over W)
  let _ : ∀ W : C, HasWeakSheafify (J.over W) AddCommGrpCat.{max c v u} :=
    fun W ↦ (hasSheafify_coefficientUniverse.{max c v, v, max c v u} (J := J.over W)).isRightAdjoint
  obtain ⟨D⟩ := exists_sliceScalarHomChainAdjunction.{c, v, u} φ
  exact ⟨D.ordinary, ⟨D.chains⟩⟩

private noncomputable def chainForward
    {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (D : NormalizedOrdinaryAdjunction.{c, v, u} φ)
    {A : Complex.{c, v, u} R} {N : Complex.{c, v, u} S}
    (f : D.extension.complex.obj A ⟶ N) : A ⟶ (restriction.{c, v, u} φ).obj N where
  f n := D.adjunction.homEquiv (A.X n) (N.X n) (f.f n)
  comm' i j _ := by
    exact (D.adjunction.homEquiv_naturality_left_square
      (A.d i j) (f.f j) (f.f i) (N.d i j) (f.comm i j).symm).symm

private noncomputable def chainInverse
    {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (D : NormalizedOrdinaryAdjunction.{c, v, u} φ)
    {A : Complex.{c, v, u} R} {N : Complex.{c, v, u} S}
    (f : A ⟶ (restriction.{c, v, u} φ).obj N) : D.extension.complex.obj A ⟶ N where
  f n := (D.adjunction.homEquiv (A.X n) (N.X n)).symm (f.f n)
  comm' i j _ := by
    exact (D.adjunction.homEquiv_naturality_right_square
      (A.d i j) (f.f j) (f.f i) (N.d i j) (f.comm i j).symm).symm

private noncomputable def chainEquiv
    {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (D : NormalizedOrdinaryAdjunction.{c, v, u} φ)
    (A : Complex.{c, v, u} R) (N : Complex.{c, v, u} S) :
    (D.extension.complex.obj A ⟶ N) ≃ (A ⟶ (restriction.{c, v, u} φ).obj N) where
  toFun := chainForward.{c, v, u} D
  invFun := chainInverse.{c, v, u} D
  left_inv f := by
    ext n : 1
    exact (D.adjunction.homEquiv (A.X n) (N.X n)).symm_apply_apply _
  right_inv f := by
    ext n : 1
    exact (D.adjunction.homEquiv (A.X n) (N.X n)).apply_symm_apply _

private theorem inverse_pure
    {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (D : NormalizedOrdinaryAdjunction.{c, v, u} φ)
    {A : Complex.{c, v, u} R} {N : Complex.{c, v, u} S}
    (f : A ⟶ (restriction.{c, v, u} φ).obj N)
    (n : ℤ) (V : Cᵒᵖ) (s : S.obj.obj V) (x : (A.X n).val.obj V) :
    (((chainEquiv.{c, v, u} D A N).symm f).f n).val.app V (D.extension.section A n V s x) =
      s • (@id ((N.X n).val.obj V) ((f.f n).val.app V x)) := by
  exact D.inverse (A.X n) (N.X n) (f.f n) V s x

private theorem forward_pure
    {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (D : NormalizedOrdinaryAdjunction.{c, v, u} φ)
    {A : Complex.{c, v, u} R} {N : Complex.{c, v, u} S}
    (f : D.extension.complex.obj A ⟶ N)
    (n : ℤ) (V : Cᵒᵖ) (x : (A.X n).val.obj V) :
    (((chainEquiv.{c, v, u} D A N) f).f n).val.app V x =
      (f.f n).val.app V (D.extension.section A n V 1 x) := by
  exact D.forward (A.X n) (N.X n) (f.f n) V x

private theorem chainEquiv_natural
    {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (D : NormalizedOrdinaryAdjunction.{c, v, u} φ)
    {A B : Complex.{c, v, u} R} {N N' : Complex.{c, v, u} S}
    (a : A ⟶ B) (f : D.extension.complex.obj B ⟶ N) (b : N ⟶ N') :
    chainEquiv.{c, v, u} D A N' (D.extension.complex.map a ≫ f ≫ b) =
      a ≫ chainEquiv.{c, v, u} D B N f ≫ (restriction.{c, v, u} φ).map b := by
  ext n : 1
  exact (D.adjunction.homEquiv_naturality_left (a.f n) (f.f n ≫ b.f n)).trans
    (congrArg (a.f n ≫ ·) (D.adjunction.homEquiv_naturality_right (f.f n) (b.f n)))

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  [HasWeakSheafify J AddCommGrpCat.{max c v u}] in
private theorem homMap_comp
    {R : Sheaf J CommRingCat.{max c v u}}
    {P P' P'' A A' A'' : Complex.{c, v, u} R}
    (a : P' ⟶ P) (a' : P'' ⟶ P') (b : A ⟶ A') (b' : A' ⟶ A'') :
    homMap.{c, v, u} a b ≫ homMap.{c, v, u} a' b' = homMap.{c, v, u} (a' ≫ a) (b ≫ b') := by
  simp only [homMap, Category.assoc]
  rw [← Category.assoc ((homComplexFunctor.obj (op P')).map b),
    (homComplexFunctor.map a'.op).naturality, Category.assoc,
    ← CategoryTheory.Functor.map_comp, ← Category.assoc, ← NatTrans.comp_app,
    ← CategoryTheory.Functor.map_comp, ← op_comp]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  [HasWeakSheafify J AddCommGrpCat.{max c v u}] in
private theorem evaluate_map
    {R : Sheaf J CommRingCat.{max c v u}}
    {P P' A A' : Complex.{c, v, u} R} (a : P' ⟶ P) (b : A ⟶ A')
    (n i k : ℤ) (h : i + n = k) (V : Cᵒᵖ)
    (f : ((homComplex (R := R) P A).X n).val.obj V) (x : (P'.X i).val.obj V) :
    evaluate.{c, v, u} P' A' n i k h V (((homMap.{c, v, u} a b).f n).val.app V f) x =
      (b.f k).val.app V (evaluate.{c, v, u} P A n i k h V f ((a.f i).val.app V x)) := by
  have e := congrArg (fun z ↦ (z.val.app V) f)
    (homComplexFunctor_map_f_π a b n i k h)
  exact congrArg (fun z ↦ (z.app (op (Over.mk (𝟙 V.unop)))).hom x) e

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  [HasWeakSheafify J AddCommGrpCat.{max c v u}] in
private theorem evaluate_ext
    {R : Sheaf J CommRingCat.{max c v u}} (P A : Complex.{c, v, u} R)
    {B : Complex.{c, v, u} R} (f g : B ⟶ homComplex (R := R) P A)
    (h : ∀ (n i k : ℤ) (hik : i + n = k) (V : Cᵒᵖ)
      (x : (B.X n).val.obj V) (p : (P.X i).val.obj V),
      evaluate.{c, v, u} P A n i k hik V ((f.f n).val.app V x) p =
        evaluate.{c, v, u} P A n i k hik V ((g.f n).val.app V x) p) : f = g := by
  ext n : 1
  apply homComplex_hom_ext
  intro i k hik
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro p
  have hf := PresheafOfModules.naturality_apply (f.f n ≫ homComplexπ P A n i k hik).val
    W.unop.hom.op x
  have hg := PresheafOfModules.naturality_apply (g.f n ≫ homComplexπ P A n i k hik).val
    W.unop.hom.op x
  change _ = PresheafOfModules.restrictOverMap W.unop.hom
    ((homComplexπ P A n i k hik).val.app V ((f.f n).val.app V x)) at hf
  change _ = PresheafOfModules.restrictOverMap W.unop.hom
    ((homComplexπ P A n i k hik).val.app V ((g.f n).val.app V x)) at hg
  have e := h n i k hik (op W.unop.left) ((B.X n).val.map W.unop.hom.op x) p
  unfold evaluate at e
  change ((f.f n ≫ homComplexπ P A n i k hik).val.app (op W.unop.left)
    ((B.X n).val.map W.unop.hom.op x)).app (op (Over.mk (𝟙 W.unop.left))) p =
    ((g.f n ≫ homComplexπ P A n i k hik).val.app (op W.unop.left)
      ((B.X n).val.map W.unop.hom.op x)).app (op (Over.mk (𝟙 W.unop.left))) p at e
  rw [hf, hg] at e
  exact (PresheafOfModules.restrictOver_hom_app_congr
    ((homComplexπ P A n i k hik).val.app V ((f.f n).val.app V x))
    (Category.id_comp W.unop.hom) p).symm.trans
    (e.trans (PresheafOfModules.restrictOver_hom_app_congr
      ((homComplexπ P A n i k hik).val.app V ((g.f n).val.app V x))
      (Category.id_comp W.unop.hom) p))

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  [HasWeakSheafify J AddCommGrpCat.{max c v u}] in
private theorem evaluate_smul
    {R : Sheaf J CommRingCat.{max c v u}} (P A : Complex.{c, v, u} R)
    (n i k : ℤ) (h : i + n = k) (V : Cᵒᵖ) (s : R.obj.obj V)
    (f : ((homComplex (R := R) P A).X n).val.obj V) (x : (P.X i).val.obj V) :
    evaluate.{c, v, u} P A n i k h V (s • f) x =
      s • evaluate.{c, v, u} P A n i k h V f x := by
  unfold evaluate
  rw [map_smul, PresheafOfModules.smul_app]
  change R.obj.map (𝟙 V.unop).op s •
    evaluate.{c, v, u} P A n i k h V f x = s • evaluate.{c, v, u} P A n i k h V f x
  simp

private noncomputable def sigmaMap
    {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (D : NormalizedOrdinaryAdjunction.{c, v, u} φ)
    (T : ScalarHomAdjunctionChains.{c, v, u} D.extension)
    (P A : Complex.{c, v, u} R) (N : Complex.{c, v, u} S)
    (q : D.extension.complex.obj A ⟶ N) :
    D.extension.complex.obj (homComplex (R := R) P A) ⟶
      homComplex (R := S) (D.extension.complex.obj P) N :=
  (chainEquiv.{c, v, u} D _ _).symm
    (homMap.{c, v, u} (𝟙 P) (chainEquiv.{c, v, u} D A N q) ≫ (T.theta P N).inv)

private theorem sigmaMap_formula
    {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (D : NormalizedOrdinaryAdjunction.{c, v, u} φ)
    (T : ScalarHomAdjunctionChains.{c, v, u} D.extension)
    (P A : Complex.{c, v, u} R) (N : Complex.{c, v, u} S)
    (q : D.extension.complex.obj A ⟶ N) :
    SigmaFormula.{c, v, u} D.extension P A N q (sigmaMap.{c, v, u} D T P A N q) := by
  intro n i k h V s t f x
  unfold sigmaMap
  rw [inverse_pure.{c, v, u}, evaluate_smul.{c, v, u}]
  change s • evaluate.{c, v, u} (D.extension.complex.obj P) N n i k h V
    (((T.theta P N).inv.f n).val.app V
      (((homMap.{c, v, u} (𝟙 P) (chainEquiv.{c, v, u} D A N q)).f n).val.app V f))
    (D.extension.section P i V t x) = _
  rw [T.theta_inverse, evaluate_map.{c, v, u}]
  simp only [HomologicalComplex.id_f, SheafOfModules.id_val,
    PresheafOfModules.id_app, ModuleCat.id_apply, id_eq]
  rw [forward_pure.{c, v, u}]
  change s • t • (q.f k).val.app V
    (D.extension.section A k V 1 (evaluate.{c, v, u} P A n i k h V f x)) = _
  exact (mul_smul s t _).symm

private theorem sigmaMap_unique
    {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (D : NormalizedOrdinaryAdjunction.{c, v, u} φ)
    (T : ScalarHomAdjunctionChains.{c, v, u} D.extension)
    (P A : Complex.{c, v, u} R) (N : Complex.{c, v, u} S)
    (q : D.extension.complex.obj A ⟶ N)
    (τ : D.extension.complex.obj (homComplex (R := R) P A) ⟶
      homComplex (R := S) (D.extension.complex.obj P) N)
    (hτ : SigmaFormula.{c, v, u} D.extension P A N q τ) :
    τ = sigmaMap.{c, v, u} D T P A N q := by
  apply (chainEquiv.{c, v, u} D _ _).injective
  apply (cancel_mono (T.theta P N).hom).mp
  apply evaluate_ext.{c, v, u} P ((restriction.{c, v, u} φ).obj N)
  intro n i k h V f x
  change evaluate.{c, v, u} P ((restriction.{c, v, u} φ).obj N) n i k h V
    (((T.theta P N).hom.f n).val.app V
      (((chainEquiv.{c, v, u} D _ _) τ).f n |>.val.app V f)) x = _
  rw [T.theta_forward, forward_pure.{c, v, u}]
  change _ = evaluate.{c, v, u} P ((restriction.{c, v, u} φ).obj N) n i k h V
    (((T.theta P N).hom.f n).val.app V
      ((((chainEquiv.{c, v, u} D _ _) (sigmaMap.{c, v, u} D T P A N q)).f n).val.app V f)) x
  rw [T.theta_forward, forward_pure.{c, v, u}]
  have hs := sigmaMap_formula.{c, v, u} D T P A N q n i k h V 1 1 f x
  have ht := hτ n i k h V 1 1 f x
  change _ = evaluate.{c, v, u} (D.extension.complex.obj P) N n i k h V
    (((sigmaMap.{c, v, u} D T P A N q).f n).val.app V
      (D.extension.section (homComplex P A) n V 1 f)) (D.extension.section P i V 1 x)
  exact ht.trans hs.symm

private theorem sigmaMap_natural
    {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (D : NormalizedOrdinaryAdjunction.{c, v, u} φ)
    (T : ScalarHomAdjunctionChains.{c, v, u} D.extension)
    (P P' A A' : Complex.{c, v, u} R) (N N' : Complex.{c, v, u} S)
    (q : D.extension.complex.obj A ⟶ N) (q' : D.extension.complex.obj A' ⟶ N')
    (a : P' ⟶ P) (b : A ⟶ A') (w : N ⟶ N')
    (h : D.extension.complex.map b ≫ q' = q ≫ w) :
    sigmaMap.{c, v, u} D T P A N q ≫ homMap.{c, v, u} (D.extension.complex.map a) w =
      D.extension.complex.map (homMap.{c, v, u} a b) ≫ sigmaMap.{c, v, u} D T P' A' N' q' := by
  apply (chainEquiv.{c, v, u} D _ _).injective
  have hn := chainEquiv_natural.{c, v, u} D (𝟙 (homComplex P A)) (sigmaMap.{c, v, u} D T P A N q)
    (homMap.{c, v, u} (D.extension.complex.map a) w)
  have hn' := chainEquiv_natural.{c, v, u} D (homMap.{c, v, u} a b)
    (sigmaMap.{c, v, u} D T P' A' N' q') (𝟙 _)
  erw [CategoryTheory.Functor.map_id] at hn
  erw [CategoryTheory.Functor.map_id] at hn'
  simp only [Category.id_comp, Category.comp_id] at hn hn'
  rw [hn, hn']
  apply (cancel_mono (T.theta P' N').hom).mp
  simp only [sigmaMap, Equiv.apply_symm_apply, Category.assoc]
  rw [T.theta_natural P P' N N' a w]
  simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [homMap_comp.{c, v, u}, homMap_comp.{c, v, u}]
  simp only [Category.comp_id, Category.id_comp]
  congr 1
  have he := congrArg (chainEquiv.{c, v, u} D A N') h
  have he' := chainEquiv_natural.{c, v, u} D b q' (𝟙 N')
  have he'' := chainEquiv_natural.{c, v, u} D (𝟙 A) q w
  erw [CategoryTheory.Functor.map_id] at he'
  erw [CategoryTheory.Functor.map_id] at he''
  simp only [Category.id_comp, Category.comp_id] at he' he''
  exact ((he'.symm.trans he).trans he'').symm

private theorem section_smul
    {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (D : NormalizedOrdinaryAdjunction.{c, v, u} φ)
    (A : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ) (s : S.obj.obj V)
    (x : (A.X n).val.obj V) :
    D.extension.section A n V s x = s • D.extension.section A n V 1 x := by
  have h := inverse_pure.{c, v, u} D
    (chainEquiv.{c, v, u} D A (D.extension.complex.obj A) (𝟙 _)) n V s x
  rw [Equiv.symm_apply_apply, forward_pure.{c, v, u}] at h
  exact h

private noncomputable def alphaMap
    {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (D : NormalizedOrdinaryAdjunction.{c, v, u} φ)
    (T : ScalarHomAdjunctionChains.{c, v, u} D.extension)
    (P A : Complex.{c, v, u} R) :
    (tensor.{c, v, u} φ).obj (homComplex (R := R) P A) ⟶
      homComplex (R := R) P ((tensor.{c, v, u} φ).obj A) :=
  (T.nu.app (homComplex P A)).hom ≫
    (restriction.{c, v, u} φ).map (sigmaMap.{c, v, u} D T P A (D.extension.complex.obj A) (𝟙 _)) ≫
    (T.theta P (D.extension.complex.obj A)).hom ≫ homMap.{c, v, u} (𝟙 P) (T.nu.app A).inv

private theorem alphaMap_formula
    {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (D : NormalizedOrdinaryAdjunction.{c, v, u} φ)
    (T : ScalarHomAdjunctionChains.{c, v, u} D.extension)
    (P A : Complex.{c, v, u} R) (n i k : ℤ) (h : i + n = k)
    (V : Cᵒᵖ) (s : S.obj.obj V)
    (f : ((homComplex (R := R) P A).X n).val.obj V) (x : (P.X i).val.obj V) :
    evaluate.{c, v, u} P ((tensor.{c, v, u} φ).obj A) n i k h V
      (((alphaMap.{c, v, u} D T P A).f n).val.app V
        (tensorSection.{c, v, u} φ (homComplex P A) n V s f)) x =
        tensorSection.{c, v, u} φ A k V s (evaluate.{c, v, u} P A n i k h V f x) := by
  change evaluate.{c, v, u} P ((tensor.{c, v, u} φ).obj A) n i k h V
    (((homMap.{c, v, u} (𝟙 P) (T.nu.app A).inv).f n).val.app V
      (((T.theta P (D.extension.complex.obj A)).hom.f n).val.app V
        (((sigmaMap.{c, v, u} D T P A (D.extension.complex.obj A) (𝟙 _)).f n).val.app V
          (((T.nu.app (homComplex P A)).hom.f n).val.app V
            (tensorSection.{c, v, u} φ (homComplex P A) n V s f))))) x = _
  rw [T.nu_pure, evaluate_map.{c, v, u}]
  change (((T.nu.app A).inv.f k).val.app V)
    (evaluate.{c, v, u} P ((restriction.{c, v, u} φ).obj (D.extension.complex.obj A))
      n i k h V
      (((T.theta P (D.extension.complex.obj A)).hom.f n).val.app V
        (((sigmaMap.{c, v, u} D T P A (D.extension.complex.obj A) (𝟙 _)).f n).val.app V
          (D.extension.section (homComplex P A) n V s f))) x) = _
  rw [T.theta_forward, sigmaMap_formula.{c, v, u}]
  simp only [mul_one, HomologicalComplex.id_f, SheafOfModules.id_val,
    PresheafOfModules.id_app, ModuleCat.id_apply]
  rw [← section_smul.{c, v, u}]
  rw [← T.nu_pure A k V s]
  have he := congrArg (fun z ↦ (z.val.app V) (tensorSection.{c, v, u} φ A k V s
    (evaluate.{c, v, u} P A n i k h V f x)))
    (HomologicalComplex.congr_hom (T.nu.app A).hom_inv_id k)
  exact he

private theorem alphaMap_natural
    {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (D : NormalizedOrdinaryAdjunction.{c, v, u} φ)
    (T : ScalarHomAdjunctionChains.{c, v, u} D.extension)
    (P P' A A' : Complex.{c, v, u} R) (a : P' ⟶ P) (b : A ⟶ A') :
    alphaMap.{c, v, u} D T P A ≫ homMap.{c, v, u} a ((tensor.{c, v, u} φ).map b) =
      (tensor.{c, v, u} φ).map (homMap.{c, v, u} a b) ≫ alphaMap.{c, v, u} D T P' A' := by
  have hs := sigmaMap_natural.{c, v, u} D T P P' A A'
    (D.extension.complex.obj A) (D.extension.complex.obj A')
    (𝟙 _) (𝟙 _) a b (D.extension.complex.map b) (by simp)
  have ht := T.theta_natural P P' (D.extension.complex.obj A)
    (D.extension.complex.obj A') a (D.extension.complex.map b)
  have hn := T.nu.hom.naturality (homMap.{c, v, u} a b)
  have hb := T.nu.inv.naturality b
  dsimp only [Functor.comp_map] at hn hb
  have hc : homMap.{c, v, u} (𝟙 P) (T.nu.app A).inv ≫
      homMap.{c, v, u} a ((tensor.{c, v, u} φ).map b) =
      homMap.{c, v, u} a ((restriction.{c, v, u} φ).map (D.extension.complex.map b)) ≫
        homMap.{c, v, u} (𝟙 P') (T.nu.app A').inv := by
    rw [homMap_comp.{c, v, u}, homMap_comp.{c, v, u}]
    simp only [Category.comp_id, Category.id_comp]
    exact congrArg (homMap.{c, v, u} a) hb.symm
  unfold alphaMap
  simp only [Category.assoc]
  rw [hc]
  rw [← Category.assoc (T.theta P (D.extension.complex.obj A)).hom, ← ht]
  simp only [Category.assoc]
  rw [← Category.assoc ((restriction.{c, v, u} φ).map
    (sigmaMap.{c, v, u} D T P A (D.extension.complex.obj A) (𝟙 _))),
    ← CategoryTheory.Functor.map_comp, hs, CategoryTheory.Functor.map_comp]
  simp only [← Category.assoc]
  exact congrArg (fun z ↦ ((z ≫ (restriction.{c, v, u} φ).map
    (sigmaMap.{c, v, u} D T P' A' (D.extension.complex.obj A') (𝟙 _))) ≫
      (T.theta P' (D.extension.complex.obj A')).hom) ≫
        homMap.{c, v, u} (𝟙 P') (T.nu.app A').inv) hn.symm

/-- Scalar evaluation and input naturality for the unbounded product Hom complex.
Source: Stacks 03CY (lemma-sheafification-presheaf-modules), 03CZ
(lemma-adjointness-tensor-restrict), and 0A8X (section-hom-complexes).
(blueprint: lem-sfb-scalar-hom-chain-evaluation).

Proof plan, following the ten steps of the node:
1. On each slice define alpha's coordinate by `p ↦ s ⊗ f(p)`. This is linear
in p and balanced bilinear in s and f; restrictions commute with this rule.
2. Extend by the module tensor universal property and then by module sheafification
(def-weil-pbc-module-tensor-product, def-weil-presheaf-modules-sheafification).
3. On each coordinate the signed differential gives
`s ⊗ d_J f(p) - (-1)^n s ⊗ f(d_P p) = s ⊗ (d_H f)(p)`, proving the chain equation
(def-pur-hom-complex, def-pur-sheaf-tensor-product).
4. The unit x ↦ 1 ⊗ x defines a chain map eta. Postcompose the Hom complex
with Uq eta to obtain the R-linear family f ↦ (p ↦ q(1 ⊗ f(p))).
5. Apply the inverse normalized slice scalar-Hom chain adjunction
(lem-sfb-slice-scalar-hom-chain-adjunction) to get beta, whose coordinates send
`t ⊗ p` to `t q(1 ⊗ f(p))`.
6. Extend `(s,f) ↦ s beta(f)` through the tensor and S-module sheafification.
This gives sigma and its displayed formula, on every slice.
7. Since beta is a chain map and the Hom differential is S-linear,
`d sigma(s ⊗ f) = s beta(d f) = sigma(s ⊗ d f)`.
8. For uniqueness, the slice adjunction detects each inner map on `1 ⊗ p`;
product projections detect Hom sections, and tensor generation followed by the
sheafification adjunction detects the outer map. Pure tensors need not exhaust
sections of the sheafified tensor.
9. Alpha's naturality follows because both sides evaluate to
`s ⊗ v(f(u(p)))` on every coordinate over every further slice object.
10. Sigma's two naturality composites evaluate to `st w q(1 ⊗ f(u(p)))`
and `st q'(1 ⊗ v(f(u(p))))`; these agree by `Ev ≫ q' = q ≫ w`.
Use the same three equality tests as in step 8. No boundedness, flatness,
projectivity, K-injectivity, or preservation of infinite products enters. -/
theorem exists_scalarHomChainEvaluation
    {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S) :
    ∃ E : Extension.{c, v, u} φ,
    ∃ α : ∀ (P A : Complex.{c, v, u} R),
      (tensor.{c, v, u} φ).obj (homComplex (R := R) P A) ⟶
        homComplex (R := R) P ((tensor.{c, v, u} φ).obj A),
    ∃ σ : ∀ (P A : Complex.{c, v, u} R) (N : Complex.{c, v, u} S)
      (_q : E.complex.obj A ⟶ N),
      E.complex.obj (homComplex (R := R) P A) ⟶
        homComplex (R := S) (E.complex.obj P) N,
    (∀ (P A : Complex.{c, v, u} R) (n i k : ℤ) (h : i + n = k)
      (V : Cᵒᵖ) (s : S.obj.obj V)
      (f : ((homComplex (R := R) P A).X n).val.obj V) (x : (P.X i).val.obj V),
      evaluate.{c, v, u} P ((tensor.{c, v, u} φ).obj A) n i k h V
          (((α P A).f n).val.app V
            (tensorSection.{c, v, u} φ (homComplex (R := R) P A) n V s f)) x =
        tensorSection.{c, v, u} φ A k V s (evaluate.{c, v, u} P A n i k h V f x)) ∧
    (∀ (P A : Complex.{c, v, u} R) (N : Complex.{c, v, u} S)
      (q : E.complex.obj A ⟶ N),
      SigmaFormula.{c, v, u} E P A N q (σ P A N q)) ∧
    (∀ (P A : Complex.{c, v, u} R) (N : Complex.{c, v, u} S)
      (q : E.complex.obj A ⟶ N)
      (τ : E.complex.obj (homComplex (R := R) P A) ⟶
        homComplex (R := S) (E.complex.obj P) N),
      SigmaFormula.{c, v, u} E P A N q τ → τ = σ P A N q) ∧
    (∀ (P P' A A' : Complex.{c, v, u} R) (a : P' ⟶ P) (b : A ⟶ A'),
      α P A ≫ homMap.{c, v, u} a ((tensor.{c, v, u} φ).map b) =
        (tensor.{c, v, u} φ).map (homMap.{c, v, u} a b) ≫ α P' A') ∧
    (∀ (P P' A A' : Complex.{c, v, u} R) (N N' : Complex.{c, v, u} S)
      (q : E.complex.obj A ⟶ N) (q' : E.complex.obj A' ⟶ N')
      (a : P' ⟶ P) (b : A ⟶ A') (w : N ⟶ N'),
      E.complex.map b ≫ q' = q ≫ w →
        σ P A N q ≫ homMap.{c, v, u} (E.complex.map a) w =
          E.complex.map (homMap.{c, v, u} a b) ≫ σ P' A' N' q') := by
  obtain ⟨D, ⟨T⟩⟩ := adjunction_exists.{c, v, u} φ
  refine ⟨D.extension, alphaMap.{c, v, u} D T, sigmaMap.{c, v, u} D T, ?_, ?_, ?_, ?_, ?_⟩
  · exact alphaMap_formula.{c, v, u} D T
  · exact sigmaMap_formula.{c, v, u} D T
  · exact sigmaMap_unique.{c, v, u} D T
  · exact alphaMap_natural.{c, v, u} D T
  · exact sigmaMap_natural.{c, v, u} D T

end SheafOfModules.StrictScalarHom
