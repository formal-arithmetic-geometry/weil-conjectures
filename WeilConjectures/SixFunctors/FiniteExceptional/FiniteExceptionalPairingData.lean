/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteExceptional.FiniteExceptionalData
import WeilConjectures.SixFunctors.IntegralVerdier.FiniteIntrinsicVerdierBiduality
import WeilConjectures.SixFunctors.IntegralHom.Evaluation.IntegralHomEvaluationNaturality

/-! # Evaluation and trace pairings for the finite exceptional formula

Source: current blueprint lem-coef-finite-exceptional.proof.md, paragraph 2,
transposition under the finite duality bijections.
(blueprint: lem-sf-finite-exceptional-pairing-data).

Record the two uncurried words in the normalization of the fixed dual formula. If two
arrows have the same evaluation pairing, swap their tensor factors and transpose once
more. Naturality identifies the transposes with those arrows followed by the canonical
biduality morphism. Finite Verdier biduality makes that morphism invertible, so the
arrows agree. Tensor functoriality gives evaluation precomposition. Naturality of the
projection map and of the signed symmetry gives trace precomposition. The uniquely
normalized formula isomorphism supplies equality of the two words.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FiniteExceptional

private theorem evaluation_injective_of_delta
    {C : Type*} [Category C] (T : C × C ⥤ C) (H : Cᵒᵖ × C ⥤ C)
    (adj : ∀ K : C, (Functor.curry.obj T).obj K ⊣ (Functor.curry.obj H).obj (op K))
    (s : ∀ K L : C, T.obj (K, L) ≅ T.obj (L, K))
    (hs : ∀ (K L K' L' : C) (f : K ⟶ K') (g : L ⟶ L'),
      T.map (Prod.mkHom f g) ≫ (s K' L').hom =
        (s K L).hom ≫ T.map (Prod.mkHom g f))
    (ω L P : C)
    (hδ : IsIso (restrictionDualDelta (Functor.curry.obj T)
      (Functor.curry.obj H) adj s ω L)) :
    Function.Injective (fun g : P ⟶ L ↦
      T.map (Prod.mkHom g (𝟙 (H.obj (op L, ω)))) ≫ (adj L).counit.app ω) := by
  intro f g hfg
  let V := H.obj (op L, ω)
  have hf (v : P ⟶ L) :
      (adj V).homEquiv P ω ((s V P).hom ≫
        T.map (Prod.mkHom v (𝟙 V)) ≫ (adj L).counit.app ω) =
      v ≫ restrictionDualDelta (Functor.curry.obj T) (Functor.curry.obj H) adj s ω L := by
    change (adj V).homEquiv P ω ((s V P).hom ≫
      T.map (Prod.mkHom v (𝟙 V)) ≫ (adj L).counit.app ω) =
      v ≫ (adj V).homEquiv L ω ((s V L).hom ≫ (adj L).counit.app ω)
    rw [← reassoc_of% (hs V P V L (𝟙 V) v)]
    exact (adj V).homEquiv_naturality_left v
      ((s V L).hom ≫ (adj L).counit.app ω)
  have h := congrArg (fun z ↦ (adj V).homEquiv P ω ((s V P).hom ≫ z)) hfg
  rw [hf, hf] at h
  exact (cancel_mono (restrictionDualDelta (Functor.curry.obj T)
    (Functor.curry.obj H) adj s ω L)).1 h

private theorem tensor_precomp {C : Type*} [Category C] (T : C × C ⥤ C)
    {P P' L M W : C} (v : P ⟶ P') (g : P' ⟶ L) (e : T.obj (L, M) ⟶ W) :
    T.map (Prod.mkHom (v ≫ g) (𝟙 M)) ≫ e =
      T.map (Prod.mkHom v (𝟙 M)) ≫ T.map (Prod.mkHom g (𝟙 M)) ≫ e := by
  rw [← Category.assoc, ← T.map_comp]
  congr 2
  ext <;> simp

private theorem tensor_identity {C : Type*} [Category C] (T : C × C ⥤ C)
    {P L M W : C} (g : P ⟶ L) (e : T.obj (L, M) ⟶ W) :
    T.map (Prod.mkHom g (𝟙 M)) ≫ T.map (Prod.mkHom (𝟙 L) (𝟙 M)) ≫ e =
      T.map (Prod.mkHom g (𝟙 M)) ≫ e := by
  rw [← prod_id, T.map_id, Category.id_comp]

private theorem tensor_trace_naturality
    {C D : Type*} [Category C] [Category D]
    (T : C × C ⥤ C) (S : D × D ⥤ D) (F : C ⥤ D)
    {K K' U V W ω : C} {M ω' : D}
    (v : K ⟶ K') (ψ : U ⟶ V)
    (s : T.obj (K, V) ⟶ T.obj (V, K))
    (s' : T.obj (K', V) ⟶ T.obj (V, K'))
    (g : K' ⟶ W) (ev : T.obj (V, W) ⟶ ω) (r : F.obj ω ⟶ ω')
    (p : S.obj (F.obj K, M) ⟶ F.obj (T.obj (K, U)))
    (p' : S.obj (F.obj K', M) ⟶ F.obj (T.obj (K', U)))
    (hp : S.map (Prod.mkHom (F.map v) (𝟙 M)) ≫ p' =
      p ≫ F.map (T.map (Prod.mkHom v (𝟙 U))))
    (hs : T.map (Prod.mkHom v (𝟙 V)) ≫ s' =
      s ≫ T.map (Prod.mkHom (𝟙 V) v)) :
    p ≫ F.map (T.map (Prod.mkHom (𝟙 K) ψ) ≫ s ≫
      T.map (Prod.mkHom (𝟙 V) (v ≫ g)) ≫ ev) ≫ r =
    S.map (Prod.mkHom (F.map v) (𝟙 M)) ≫ p' ≫
      F.map (T.map (Prod.mkHom (𝟙 K') ψ) ≫ s' ≫
        T.map (Prod.mkHom (𝟙 V) g) ≫ ev) ≫ r := by
  have ht : T.map (Prod.mkHom v (𝟙 U)) ≫ T.map (Prod.mkHom (𝟙 K') ψ) =
      T.map (Prod.mkHom (𝟙 K) ψ) ≫ T.map (Prod.mkHom v (𝟙 V)) := by
    rw [← T.map_comp, ← T.map_comp]
    congr 1
    ext <;> simp
  have hw : T.map (Prod.mkHom v (𝟙 U)) ≫
      (T.map (Prod.mkHom (𝟙 K') ψ) ≫ s' ≫ T.map (Prod.mkHom (𝟙 V) g) ≫ ev) =
      T.map (Prod.mkHom (𝟙 K) ψ) ≫ s ≫
        T.map (Prod.mkHom (𝟙 V) (v ≫ g)) ≫ ev := by
    rw [← Category.assoc _ (T.map _) _, ht]
    simp only [Category.assoc]
    rw [reassoc_of% hs, ← T.map_comp_assoc]
    simp
  symm
  calc
    _ = (S.map (Prod.mkHom (F.map v) (𝟙 M)) ≫ p') ≫
        F.map (T.map (Prod.mkHom (𝟙 K') ψ) ≫ s' ≫
          T.map (Prod.mkHom (𝟙 V) g) ≫ ev) ≫ r := by simp only [Category.assoc]
    _ = (p ≫ F.map (T.map (Prod.mkHom v (𝟙 U)))) ≫
        F.map (T.map (Prod.mkHom (𝟙 K') ψ) ≫ s' ≫
          T.map (Prod.mkHom (𝟙 V) g) ≫ ev) ≫ r := by rw [hp]
    _ = _ := by rw [Category.assoc, ← F.map_comp_assoc, hw]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [Xbase : X.Over (Spec (.of D.k))] [Ybase : Y.Over (Spec (.of D.k))]
  [Xft : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [Xqc : QuasiCompact (X ↘ Spec (.of D.k))]
  [Yft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [Yqc : QuasiCompact (Y ↘ Spec (.of D.k))]
  [Xsep : IsSeparated (X ↘ Spec (.of D.k))]
  [Ysep : IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [fbase : f.IsOver (Spec (.of D.k))]
  [fsep : IsSeparated f] [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]
  (c : Compactification f)

/-- The uncurried ordinary evaluation pairing at one finite coefficient level. -/
def evaluationPairing (n : ℕ)
    (aY : IntegralHom.TensorPresentation.{u, u} Y
      (integralCoefficientCommRingSheaf l E Y n))
    (P : proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E (n + 1)))
    (L : (domain l E Y n).FullSubcategory) (g : P ⟶ L.obj) :
    aY.tensor.obj (P, (dual l E D Y n).obj (op L.obj)) ⟶
      integralDualizingFiniteTerm l E D Y n :=
  aY.tensor.map (Prod.mkHom g (𝟙 _)) ≫
    (aY.adjunction L.obj).counit.app (integralDualizingFiniteTerm l E D Y n)

include hl in
/-- Finite Verdier biduality makes evaluation detect arrows into a constructible object. -/
theorem evaluationPairing_injective (n : ℕ)
    (aY : IntegralHom.TensorPresentation.{u, u} Y
      (integralCoefficientCommRingSheaf l E Y n))
    (sY : IntegralVerdier.SignedSymmetry Y _ aY)
    (P : proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E (n + 1)))
    (L : (domain l E Y n).FullSubcategory) :
    Function.Injective (evaluationPairing l E D n aY P L) := by
  obtain ⟨hc, p, q, ht⟩ := L.property
  have hd := IntegralVerdier.finiteIntrinsicVerdier_biduality D l hl E Y n aY sY
    sY.naturality (IntegralHom.evaluation_naturality Y _ aY) L.obj hc p q ht
  exact evaluation_injective_of_delta aY.tensor
    (finiteIntrinsicDerivedInternalHom l E Y n) aY.adjunction sY.swap sY.naturality
    (integralDualizingFiniteTerm l E D Y n) L.obj P hd

/-- Evaluation is contravariantly natural in its free source. -/
theorem evaluationPairing_precomp (n : ℕ)
    (aY : IntegralHom.TensorPresentation.{u, u} Y
      (integralCoefficientCommRingSheaf l E Y n))
    (P P' : proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E (n + 1)))
    (L : (domain l E Y n).FullSubcategory) (v : P ⟶ P') (g : P' ⟶ L.obj) :
    evaluationPairing l E D n aY P L (v ≫ g) =
      aY.tensor.map (Prod.mkHom v (𝟙 _)) ≫ evaluationPairing l E D n aY P' L g := by
  exact tensor_precomp aY.tensor v g _

/-- The projection--evaluation--trace word defining the finite exceptional formula. -/
def tracePairing (n : ℕ)
    (aX : IntegralHom.TensorPresentation.{u, u} X
      (integralCoefficientCommRingSheaf l E X n))
    (aZ : IntegralHom.TensorPresentation.{u, u} c.Z
      (integralCoefficientCommRingSheaf l E c.Z n))
    (aY : IntegralHom.TensorPresentation.{u, u} Y
      (integralCoefficientCommRingSheaf l E Y n))
    (sX : IntegralVerdier.SignedSymmetry X _ aX)
    (K : (domain l E X n).FullSubcategory)
    (L : (domain l E Y n).FullSubcategory)
    (v : K.obj ⟶ (H l E D f n).obj L.obj) :
    aY.tensor.obj (((PurCompactSupport.image
      (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) c).obj K.obj),
      (dual l E D Y n).obj (op L.obj)) ⟶ integralDualizingFiniteTerm l E D Y n :=
  ((PurCompactSupport.projectionMap
    (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) c
    (IntegralFiniteExtension.tensorModel X aX)
    (IntegralFiniteExtension.tensorModel c.Z aZ)
    (IntegralFiniteExtension.tensorModel Y aY)
    (finitePull_comp l E f c n)).app K.obj).app ((dual l E D Y n).obj (op L.obj)) ≫
    (PurCompactSupport.image
      (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) c).map
      (aX.tensor.map (Prod.mkHom (𝟙 _)
        ((formulaPullIso l E f n).hom.app ((dual l E D Y n).obj (op L.obj)))) ≫
        (sX.swap K.obj ((finiteDerivedPullback l E n f).obj
          ((dual l E D Y n).obj (op L.obj)))).hom ≫
        aX.tensor.map (Prod.mkHom (𝟙 _) v) ≫
        (aX.adjunction ((finiteDerivedPullback l E n f).obj
          ((dual l E D Y n).obj (op L.obj)))).counit.app
            (integralDualizingFiniteTerm l E D X n)) ≫
    (PurCompactSupport.finiteImageIso l E n c).hom.app
      (integralDualizingFiniteTerm l E D X n) ≫
    CoefDualFormulaScalarTranspose.finiteTrace D l E f c n

/-- Normalization of the prescribed formula is precisely equality of these two pairings. -/
theorem dualFormula_pairing (n : ℕ)
    (aX : IntegralHom.TensorPresentation.{u, u} X
      (integralCoefficientCommRingSheaf l E X n))
    (aZ : IntegralHom.TensorPresentation.{u, u} c.Z
      (integralCoefficientCommRingSheaf l E c.Z n))
    (aY : IntegralHom.TensorPresentation.{u, u} Y
      (integralCoefficientCommRingSheaf l E Y n))
    (sX : IntegralVerdier.SignedSymmetry X _ aX)
    (L : (domain l E Y n).FullSubcategory) :
    tracePairing l E D f c n aX aZ aY sX ((G l E D hl f c n).obj L) L
        ((dualFormulaIso l E D hl f c n).hom.app L) =
      evaluationPairing l E D n aY _ L
        ((PurCompactSupport.finiteImageIso l E n c).hom.app
          ((G l E D hl f c n).obj L).obj ≫
          ((adjunction l E D hl f c n).counit.app L).hom) := by
  have hn := (dualFormula_existsUnique l E D hl f c n).exists.choose_spec aX aZ aY sX L
  exact hn.trans (tensor_identity aY.tensor _ _)

/-- The trace word is natural in its first constructible argument. -/
theorem tracePairing_precomp (n : ℕ)
    (aX : IntegralHom.TensorPresentation.{u, u} X
      (integralCoefficientCommRingSheaf l E X n))
    (aZ : IntegralHom.TensorPresentation.{u, u} c.Z
      (integralCoefficientCommRingSheaf l E c.Z n))
    (aY : IntegralHom.TensorPresentation.{u, u} Y
      (integralCoefficientCommRingSheaf l E Y n))
    (sX : IntegralVerdier.SignedSymmetry X _ aX)
    (K K' : (domain l E X n).FullSubcategory)
    (L : (domain l E Y n).FullSubcategory) (v : K ⟶ K')
    (g : K'.obj ⟶ (H l E D f n).obj L.obj) :
    tracePairing l E D f c n aX aZ aY sX K L (v.hom ≫ g) =
      aY.tensor.map (Prod.mkHom
        ((PurCompactSupport.image
          (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) c).map v.hom) (𝟙 _)) ≫
        tracePairing l E D f c n aX aZ aY sX K' L g := by
  let F := PurCompactSupport.image
    (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) c
  let M := (dual l E D Y n).obj (op L.obj)
  let U := (PurCompactSupport.pull
    (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) f).obj M
  let V := (finiteDerivedPullback l E n f).obj M
  let ψ : U ⟶ V := (formulaPullIso l E f n).hom.app M
  have hp := congrArg (fun t ↦ t.app M)
    ((PurCompactSupport.projectionMap
      (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) c
      (IntegralFiniteExtension.tensorModel X aX)
      (IntegralFiniteExtension.tensorModel c.Z aZ)
      (IntegralFiniteExtension.tensorModel Y aY) (finitePull_comp l E f c n)).naturality v.hom)
  change aY.tensor.map (Prod.mkHom (F.map v.hom) (𝟙 M)) ≫ _ =
    _ ≫ F.map (aX.tensor.map (Prod.mkHom v.hom (𝟙 U))) at hp
  exact tensor_trace_naturality aX.tensor aY.tensor F v.hom ψ
    (sX.swap K.obj V).hom (sX.swap K'.obj V).hom g
    ((aX.adjunction V).counit.app (integralDualizingFiniteTerm l E D X n))
    ((PurCompactSupport.finiteImageIso l E n c).hom.app
      (integralDualizingFiniteTerm l E D X n) ≫
      CoefDualFormulaScalarTranspose.finiteTrace D l E f c n)
    _ _ hp (sX.naturality K.obj V K'.obj V v.hom (𝟙 V))

end WeilConjectures.FiniteExceptional
