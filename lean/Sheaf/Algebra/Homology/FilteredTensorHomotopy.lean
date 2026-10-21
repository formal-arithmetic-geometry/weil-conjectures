/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import Sheaf.Algebra.Homology.FilteredTensorLocalizationSetup
import Mathlib.Algebra.Homology.BifunctorHomotopy
import all Sheaf.Algebra.Homology.FilteredQuasiIsoTwoOutOfThree

/-! # Filtered homotopies and convolution tensor

Source: Stacks Project, Homology, Tag 012Z, and Derived Categories, Tag 05S2.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CochainComplex

variable {R : Type u} [CommRing R]

private theorem tensor_homotopy₁_naturality
    {K L U V K₀ L₀ U₀ V₀ : CochainComplex (ModuleCat.{u} R) ℤ}
    {f f' : K ⟶ L} {f₀ f₀' : K₀ ⟶ L₀}
    (h : Homotopy f f') (h₀ : Homotopy f₀ f₀') (g : U ⟶ V) (g₀ : U₀ ⟶ V₀)
    (a : K₀ ⟶ K) (b : L₀ ⟶ L) (c : U₀ ⟶ U) (d : V₀ ⟶ V)
    (hh : ∀ p q : ℤ, a.f p ≫ h.hom p q = h₀.hom p q ≫ b.f q)
    (hg : c ≫ g = g₀ ≫ d) (n k : ℤ) :
    (a ⊗ₘ c).f n ≫
      (HomologicalComplex.mapBifunctorMapHomotopy₁ h g
        (curriedTensor (ModuleCat.{u} R)) (.up ℤ)).hom n k =
      (HomologicalComplex.mapBifunctorMapHomotopy₁ h₀ g₀
        (curriedTensor (ModuleCat.{u} R)) (.up ℤ)).hom n k ≫ (b ⊗ₘ d).f k := by
  change (HomologicalComplex.mapBifunctorMap a c
    (curriedTensor (ModuleCat.{u} R)) (.up ℤ)).f n ≫ _ =
    _ ≫ (HomologicalComplex.mapBifunctorMap b d
      (curriedTensor (ModuleCat.{u} R)) (.up ℤ)).f k
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  dsimp only [HomologicalComplex.mapBifunctorMapHomotopy₁]
  simp only [← Category.assoc, HomologicalComplex.ι_mapBifunctorMap]
  simp only [Category.assoc, HomologicalComplex.mapBifunctorMapHomotopy.ιMapBifunctor_hom₁
    h g (curriedTensor (ModuleCat.{u} R)) (.up ℤ) _ _ _ _ _ hpq rfl,
    HomologicalComplex.mapBifunctorMapHomotopy.ιMapBifunctor_hom₁
      h₀ g₀ (curriedTensor (ModuleCat.{u} R)) (.up ℤ) _ _ _ _ _ hpq rfl]
  by_cases hk : ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ)
      ((ComplexShape.up ℤ).prev p, q) = k
  · rw [HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ hk,
      HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ hk]
    simp only [Linear.comp_units_smul, Linear.units_smul_comp, Category.assoc,
      HomologicalComplex.ι_mapBifunctorMap]
    congr 1
    rw [← NatTrans.naturality_assoc, ← NatTrans.comp_app_assoc, ← Functor.map_comp]
    rw [hh]
    simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc,
      NatTrans.naturality_assoc]
    simp only [← Functor.map_comp_assoc]
    rw [← HomologicalComplex.comp_f, hg, HomologicalComplex.comp_f]
  · simp only [HomologicalComplex.ιMapBifunctorOrZero_eq_zero _ _ _ _ _ _ _ hk,
      comp_zero, smul_zero, zero_comp]

private theorem tensor_homotopy₂_naturality
    {K L U V K₀ L₀ U₀ V₀ : CochainComplex (ModuleCat.{u} R) ℤ}
    {g g' : U ⟶ V} {g₀ g₀' : U₀ ⟶ V₀}
    (f : K ⟶ L) (f₀ : K₀ ⟶ L₀) (h : Homotopy g g') (h₀ : Homotopy g₀ g₀')
    (a : K₀ ⟶ K) (b : L₀ ⟶ L) (c : U₀ ⟶ U) (d : V₀ ⟶ V)
    (hf : a ≫ f = f₀ ≫ b)
    (hh : ∀ p q : ℤ, c.f p ≫ h.hom p q = h₀.hom p q ≫ d.f q) (n k : ℤ) :
    (a ⊗ₘ c).f n ≫
      (HomologicalComplex.mapBifunctorMapHomotopy₂ f h
        (curriedTensor (ModuleCat.{u} R)) (.up ℤ)).hom n k =
      (HomologicalComplex.mapBifunctorMapHomotopy₂ f₀ h₀
        (curriedTensor (ModuleCat.{u} R)) (.up ℤ)).hom n k ≫ (b ⊗ₘ d).f k := by
  change (HomologicalComplex.mapBifunctorMap a c
    (curriedTensor (ModuleCat.{u} R)) (.up ℤ)).f n ≫ _ =
    _ ≫ (HomologicalComplex.mapBifunctorMap b d
      (curriedTensor (ModuleCat.{u} R)) (.up ℤ)).f k
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  dsimp only [HomologicalComplex.mapBifunctorMapHomotopy₂]
  simp only [← Category.assoc, HomologicalComplex.ι_mapBifunctorMap]
  simp only [Category.assoc, HomologicalComplex.mapBifunctorMapHomotopy.ιMapBifunctor_hom₂
    f h (curriedTensor (ModuleCat.{u} R)) (.up ℤ) _ _ _ _ _ hpq rfl,
    HomologicalComplex.mapBifunctorMapHomotopy.ιMapBifunctor_hom₂
      f₀ h₀ (curriedTensor (ModuleCat.{u} R)) (.up ℤ) _ _ _ _ _ hpq rfl]
  by_cases hk : ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ)
      (p, (ComplexShape.up ℤ).prev q) = k
  · rw [HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ hk,
      HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ hk]
    simp only [Linear.comp_units_smul, Linear.units_smul_comp, Category.assoc,
      HomologicalComplex.ι_mapBifunctorMap]
    congr 1
    rw [← NatTrans.naturality_assoc, ← NatTrans.comp_app_assoc, ← Functor.map_comp]
    rw [← HomologicalComplex.comp_f, hf, HomologicalComplex.comp_f]
    simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc,
      NatTrans.naturality_assoc]
    simp only [← Functor.map_comp_assoc]
    rw [hh]
  · simp only [HomologicalComplex.ιMapBifunctorOrZero_eq_zero _ _ _ _ _ _ _ hk,
      comp_zero, smul_zero, zero_comp]

private theorem convolution_image_lift
    (P P' Q Q' : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ))
    (a n k : ℤ) (H : (P.obj ⊗ Q.obj).X n ⟶ (P'.obj ⊗ Q'.obj).X k)
    (hH : ∀ i : ℤ, ∃ H₀ : (kunnethTensorSteps P Q a i).X n ⟶
        (kunnethTensorSteps P' Q' a i).X k,
      ((P.filtration.step i).arrow ⊗ₘ (Q.filtration.step (a - i)).arrow).f n ≫ H =
        H₀ ≫ ((P'.filtration.step i).arrow ⊗ₘ
          (Q'.filtration.step (a - i)).arrow).f k) :
    ∃ lift : ((kunnethConvolution P Q).step a :
        CochainComplex (ModuleCat.{u} R) ℤ).X n ⟶
      ((kunnethConvolution P' Q').step a :
        CochainComplex (ModuleCat.{u} R) ℤ).X k,
      lift ≫ ((kunnethConvolution P' Q').step a).arrow.f k =
        ((kunnethConvolution P Q).step a).arrow.f n ≫ H := by
  let j := ((kunnethConvolution P' Q').step a).arrow.f k
  have hz : ((kunnethConvolution P Q).step a).arrow.f n ≫ H ≫ cokernel.π j = 0 := by
    apply zero_of_epi_comp
      ((factorThruImageSubobject (kunnethConvolutionArrow P Q a)).f n)
    rw [← Category.assoc, ← Category.assoc, ← HomologicalComplex.comp_f]
    change ((factorThruImageSubobject (kunnethConvolutionArrow P Q a) ≫
      (imageSubobject (kunnethConvolutionArrow P Q a)).arrow).f n ≫ H) ≫
        cokernel.π j = 0
    rw [imageSubobject_arrow_comp]
    apply (isColimitOfPreserves (HomologicalComplex.eval (ModuleCat.{u} R) (.up ℤ) n)
      (coproductIsCoproduct (kunnethTensorSteps P Q a))).hom_ext
    intro i
    change (Sigma.ι (kunnethTensorSteps P Q a) i.as).f n ≫
      ((kunnethConvolutionArrow P Q a).f n ≫ H) ≫ cokernel.π j = _ ≫ 0
    have hι : (Sigma.ι (kunnethTensorSteps P Q a) i.as).f n ≫
        (kunnethConvolutionArrow P Q a).f n =
        ((P.filtration.step i.as).arrow ⊗ₘ
          (Q.filtration.step (a - i.as)).arrow).f n := by
      rw [← HomologicalComplex.comp_f]
      simp [kunnethConvolutionArrow]
    simp only [← Category.assoc, hι, comp_zero]
    obtain ⟨H₀, hH₀⟩ := hH i.as
    rw [hH₀, Category.assoc]
    have ht : (Sigma.ι (kunnethTensorSteps P' Q' a) i.as ≫
        factorThruImageSubobject (kunnethConvolutionArrow P' Q' a)) ≫
          (imageSubobject (kunnethConvolutionArrow P' Q' a)).arrow =
        (P'.filtration.step i.as).arrow ⊗ₘ
          (Q'.filtration.step (a - i.as)).arrow := by
      simp [kunnethConvolutionArrow]
    have htk := HomologicalComplex.congr_hom ht k
    simp only [HomologicalComplex.comp_f] at htk
    rw [← htk]
    change H₀ ≫ (_ ≫ j) ≫ cokernel.π j = 0
    simp only [Category.assoc, cokernel.condition, comp_zero]
  exact ⟨Abelian.monoLift j (((kunnethConvolution P Q).step a).arrow.f n ≫ H) hz,
    Abelian.monoLift_comp _ _ _⟩

/-- Convolution of good complexes respects filtration-preserving homotopies.
Source: Stacks Project, Homology, Tag 012Z (signed total differential), and
Derived Categories, before Tag 05S2 (filtered homotopies).
(blueprint: lem-kun-convolution-filtered-homotopy).

Proof. If h is a filtered homotopy from f to f', totalize h tensor g.
On a homogeneous element x tensor y this is h(x) tensor g(y). The two mixed
terms in dH+Hd have coefficients (-1)^(deg(x)-1) and (-1)^deg(x), so cancel.
For a homotopy k from g to g', use (-1)^deg(x) f'(x) tensor k(y); its mixed
terms cancel too. Each component preserves every diagonal sum of tensors of
filtration steps, because h and k preserve each step. It therefore preserves
the image defining each convolution step. Add the two homotopies. The underlying
maps of m are the tensor maps by hm, so this gives the asserted filtered homotopy.
This also applies to zero complexes and unbounded cochain complexes: the total
complex uses direct sums, so all representatives have finite support. -/
theorem kunnethConvolution_filtered_homotopy
    (hconv : ∀ P Q : KunnethFilteredComplex R,
      HasKunnethFiltration (kunnethConvolutionObject P.obj Q.obj))
    (m : ∀ (P P' Q Q' : KunnethFilteredComplex R) (_f : P ⟶ P') (_g : Q ⟶ Q'),
      kunnethConvolutionObject P.obj Q.obj ⟶ kunnethConvolutionObject P'.obj Q'.obj)
    (hm : ∀ (P P' Q Q' : KunnethFilteredComplex R) (f : P ⟶ P') (g : Q ⟶ Q'),
      (m P P' Q Q' f g).hom = f.hom.hom ⊗ₘ g.hom.hom)
    (P P' Q Q' : KunnethFilteredComplex R) (f f' : P ⟶ P') (g g' : Q ⟶ Q')
    (hf : finiteFilteredModuleHomotopyRel R
      (kunnethRepresentativeMap f) (kunnethRepresentativeMap f'))
    (hg : finiteFilteredModuleHomotopyRel R
      (kunnethRepresentativeMap g) (kunnethRepresentativeMap g')) :
    finiteFilteredModuleHomotopyRel R
      (kunnethRepresentativeMap
        (kunnethConvolutionRepresentativeMap hconv (m P P' Q Q' f g)))
      (kunnethRepresentativeMap
        (kunnethConvolutionRepresentativeMap hconv (m P P' Q Q' f' g'))) := by
  obtain ⟨hf, hff⟩ := hf
  obtain ⟨hg, hgg⟩ := hg
  change ∃ h : Homotopy (m P P' Q Q' f g).hom (m P P' Q Q' f' g').hom, _
  let H₀ := (HomologicalComplex.mapBifunctorMapHomotopy₁ hf g.hom.hom
    (curriedTensor (ModuleCat.{u} R)) (.up ℤ)).trans
      (HomologicalComplex.mapBifunctorMapHomotopy₂ f'.hom.hom hg
        (curriedTensor (ModuleCat.{u} R)) (.up ℤ))
  let H := (Homotopy.ofEq (hm P P' Q Q' f g)).trans
    (H₀.trans (Homotopy.ofEq (hm P P' Q Q' f' g').symm))
  refine ⟨H, ?_⟩
  intro a n k
  let hf₀ (i : ℤ) := restrictedHomotopy hf hff i
  let hg₀ (i : ℤ) := restrictedHomotopy hg hgg i
  have hhf (i p q : ℤ) : (P.obj.filtration.step i).arrow.f p ≫ hf.hom p q =
      (hf₀ i).hom p q ≫ (P'.obj.filtration.step i).arrow.f q := by
    exact (hff i p q).choose_spec.symm
  have hhg (i p q : ℤ) : (Q.obj.filtration.step i).arrow.f p ≫ hg.hom p q =
      (hg₀ i).hom p q ≫ (Q'.obj.filtration.step i).arrow.f q := by
    exact (hgg i p q).choose_spec.symm
  obtain ⟨l₁, hl₁⟩ := convolution_image_lift P.obj P'.obj Q.obj Q'.obj a n k
    ((HomologicalComplex.mapBifunctorMapHomotopy₁ hf g.hom.hom
      (curriedTensor (ModuleCat.{u} R)) (.up ℤ)).hom n k) (fun i ↦
        ⟨(HomologicalComplex.mapBifunctorMapHomotopy₁ (hf₀ i)
          (FilteredObject.restrictionSteps g.hom (a - i))
          (curriedTensor (ModuleCat.{u} R)) (.up ℤ)).hom n k,
          tensor_homotopy₁_naturality hf (hf₀ i) g.hom.hom
            (FilteredObject.restrictionSteps g.hom (a - i))
            (P.obj.filtration.step i).arrow (P'.obj.filtration.step i).arrow
            (Q.obj.filtration.step (a - i)).arrow (Q'.obj.filtration.step (a - i)).arrow
            (hhf i) (restriction_arrow g.hom (a - i)).symm n k⟩)
  obtain ⟨l₂, hl₂⟩ := convolution_image_lift P.obj P'.obj Q.obj Q'.obj a n k
    ((HomologicalComplex.mapBifunctorMapHomotopy₂ f'.hom.hom hg
      (curriedTensor (ModuleCat.{u} R)) (.up ℤ)).hom n k) (fun i ↦
        ⟨(HomologicalComplex.mapBifunctorMapHomotopy₂
          (FilteredObject.restrictionSteps f'.hom i) (hg₀ (a - i))
          (curriedTensor (ModuleCat.{u} R)) (.up ℤ)).hom n k,
          tensor_homotopy₂_naturality f'.hom.hom
            (FilteredObject.restrictionSteps f'.hom i) hg (hg₀ (a - i))
            (P.obj.filtration.step i).arrow (P'.obj.filtration.step i).arrow
            (Q.obj.filtration.step (a - i)).arrow (Q'.obj.filtration.step (a - i)).arrow
            (restriction_arrow f'.hom i).symm (hhg (a - i)) n k⟩)
  refine ⟨l₁ + l₂, ?_⟩
  simpa [H, H₀, kunnethConvolutionObject, Homotopy.trans, Homotopy.ofEq, Preadditive.add_comp,
    Preadditive.comp_add] using congrArg₂ (· + ·) hl₁ hl₂

end CochainComplex
