/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.HyperplaneClass

/-!
# The top component of the projective bundle map

Tools for the localization step of the projective space formula:

* `AlgebraicGeometry.Etale.isIso_biprod_desc_of_distTriang`: a morphism from a split triangle;
* `AlgebraicGeometry.Etale.isIso_homEquiv_of_isIso_leftDerivedUpperStar_map`: direct images of
  objects supported on a section;
* `AlgebraicGeometry.Etale.exists_isIso_comp_map_counit_eq_chernPowMap`: if `hᵃ` is the class of
  a Thom class supported on a section, the component `chernPowMap q h a` is an isomorphism onto
  the direct image of the cohomology with supports.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Triangle

open Pretriangulated

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [HasBinaryBiproducts C]

/-- In a distinguished triangle `X ⟶ Y ⟶ Z ⟶ X[1]`, morphisms `ψ : A ⟶ X` and `φ : B ⟶ Y` with
`ψ` and `φ ≫ g` invertible give an isomorphism `(ψ ≫ f, φ) : A ⊞ B ≅ Y`: they form a morphism
from the split triangle `A ⟶ A ⊞ B ⟶ B ⟶ A[1]`. -/
lemma isIso_biprod_desc_of_distTriang {X Y Z A B : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (w : Z ⟶ X⟦(1 : ℤ)⟧) (hT : Triangle.mk f g w ∈ distTriang C) (ψ : A ⟶ X) [IsIso ψ]
    (φ : B ⟶ Y) [IsIso (φ ≫ g)] : IsIso (biprod.desc (ψ ≫ f) φ) := by
  have hfg : f ≫ g = 0 := comp_distTriang_mor_zero₁₂ _ hT
  have hgw : g ≫ w = 0 := comp_distTriang_mor_zero₂₃ _ hT
  let τ : binaryBiproductTriangle A B ⟶ Triangle.mk f g w :=
    { hom₁ := ψ
      hom₂ := biprod.desc (ψ ≫ f) φ
      hom₃ := φ ≫ g
      comm₁ := by simp [binaryBiproductTriangle]
      comm₂ := by
        dsimp [binaryBiproductTriangle]
        ext
        · simp [reassoc_of% hfg]
        · simp
      comm₃ := by
        dsimp [binaryBiproductTriangle]
        rw [zero_comp, Category.assoc, hgw, comp_zero] }
  exact isIso₂_of_isIso₁₃ τ (binaryBiproductTriangle_distinguished A B) hT
    (inferInstanceAs (IsIso ψ)) (inferInstanceAs (IsIso (φ ≫ g)))

end Triangle

section Section

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The derived pullback along an isomorphism of schemes is an equivalence. -/
lemma isEquivalence_leftDerivedUpperStar_of_isIso' {X Y : Scheme.{u}} (φ : X ⟶ Y) [IsIso φ] :
    (L((φ)^*[ModuleCat.{u + 1} Λ])).IsEquivalence := by
  obtain ⟨e₁⟩ := nonempty_leftDerivedUpperStar_id_iso Λ Y (inv φ ≫ φ) (by simp)
  obtain ⟨e₂⟩ := nonempty_leftDerivedUpperStar_id_iso Λ X (φ ≫ inv φ) (by simp)
  exact (CategoryTheory.Equivalence.mk (L((φ)^*[ModuleCat.{u + 1} Λ]))
    (L((inv φ)^*[ModuleCat.{u + 1} Λ]))
    (e₁.symm ≪≫ leftDerivedUpperStarComp _ (inv φ) φ _ rfl)
    ((leftDerivedUpperStarComp _ φ (inv φ) _ rfl).symm ≪≫ e₂)).isEquivalence_functor

/-- **Direct images of objects supported on a section.** Let `i : Z ⟶ X` be a closed immersion
and `q : X ⟶ S` with `i ≫ q` an isomorphism. A morphism `y : Lq^* K ⟶ Ri_! B` whose pullback
`Li^* y` is invertible has an invertible adjoint `K ⟶ Rq_* Ri_! B`: through `Ri_! ≅ Ri_*`, the
adjoint is that of `Li^* y` for the adjunction `L(i ≫ q)^* ⊣ R(i ≫ q)_*`, whose unit is
invertible. -/
lemma isIso_homEquiv_of_isIso_leftDerivedUpperStar_map {X S Z : Scheme.{u}} (q : X ⟶ S)
    (i : Z ⟶ X) [IsClosedImmersion i] [IsIso (i ≫ q)]
    {K : _root_.DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {B : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (y : (L((q)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj B)
    (hy : IsIso ((L((i)^*[ModuleCat.{u + 1} Λ])).map y)) :
    IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).homEquiv _ _ y) := by
  set A := ModuleCat.{u + 1} Λ
  let adjq := derivedUpperStarLowerStarAdjunction A q
  let adji := derivedUpperStarLowerStarAdjunction A i
  let θ := rightDerivedLowerShriekIsoRightDerivedLowerStar A i
  have := isIso_derivedUpperStarLowerStarAdjunction_counit_of_isClosedImmersion Λ i
  let z := (adji.homEquiv _ _).symm (y ≫ θ.hom.app B)
  have hz : IsIso z := by
    simp only [z, Adjunction.homEquiv_counit, Functor.map_comp]
    infer_instance
  have := isEquivalence_leftDerivedUpperStar_of_isIso' Λ (i ≫ q)
  have e : L((q)^*[A]) ⋙ L((i)^*[A]) ≅ L((i ≫ q)^*[A]) :=
    (leftDerivedUpperStarComp A i q (i ≫ q) rfl).symm
  have : (L((q)^*[A]) ⋙ L((i)^*[A])).Full := Functor.Full.of_iso e.symm
  have : (L((q)^*[A]) ⋙ L((i)^*[A])).Faithful := Functor.Faithful.of_iso e.symm
  let adj := adjq.comp adji
  have key : adj.homEquiv _ _ z = adjq.homEquiv _ _ y ≫ (R((q)_*[A])).map (θ.hom.app B) := by
    rw [Adjunction.comp_homEquiv]
    simp only [Equiv.trans_apply, z, Equiv.apply_symm_apply]
    exact adjq.homEquiv_naturality_right y _
  have : IsIso (adj.homEquiv _ _ z) := by
    rw [Adjunction.homEquiv_unit]
    infer_instance
  rw [key] at this
  exact IsIso.of_isIso_comp_right _ ((R((q)_*[A])).map (θ.hom.app B))

end Section

section TopClass

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] [HasKummerClass Λ]

/-- **The top class of the projective bundle map.** Let `q : X ⟶ S`, `i : Z ⟶ X` a closed
immersion with `i ≫ q` an isomorphism, and `γ ∈ H^{2a}_Z(X, Λ(a))` a Thom class (its adjoint
`Λ_Z ⟶ Ri^! Λ(a)[2a]` is invertible) with `hᵃ` as underlying class. Then the component
`chernPowMap q h a : Λ_S(-a)[-2a] ⟶ Rq_* Λ_X` factors through an isomorphism
`Λ_S(-a)[-2a] ≅ Rq_* Ri_! Ri^! Λ_X` followed by the counit.

Proof: the forget-supports morphism `χ : Ri_! Λ_Z ⟶ Λ(a)[2a]` of `γ` is universal for objects
supported on `Z` (`AlgebraicGeometry.Etale.isIso_iff_isSupportedUniversal`), hence so is
`χ ⊗ Λ(-a)[-2a]`, which therefore factors through the counit `Ri_! Ri^! Λ_X ⟶ Λ_X` by an
isomorphism. As `γ = u ≫ Ri_! (φ_γ)` for the restriction map `u : Λ_X ⟶ Ri_! Λ_Z`, whose
pullback to `Z` is invertible, `isIso_homEquiv_of_isIso_leftDerivedUpperStar_map` applies. -/
theorem exists_isIso_comp_map_counit_eq_chernPowMap {X S Z : Scheme.{u}}
    [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ S] (q : X ⟶ S) (i : Z ⟶ X)
    [IsClosedImmersion i] [IsIso (i ≫ q)]
    (h : constantComplex Λ X ⟶ (tateObject Λ X 1)⟦2 * (1 : ℤ)⟧) (a : ℕ)
    (γ : constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i)^![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ X a)⟦2 * (a : ℤ)⟧)))
    (hγ : IsIso (supportedClassMap Λ i γ))
    (hforget : γ ≫ (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i).counit.app _ =
      chernPow h a) :
    ∃ ψ : (tateObject Λ S (-(a : ℤ)))⟦2 * (-(a : ℤ))⟧ ⟶ (R((q)_*[ModuleCat.{u + 1} Λ])).obj
        ((R(i)_![ModuleCat.{u + 1} Λ]).obj
          ((R(i)^![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ X))),
      IsIso ψ ∧ ψ ≫ (R((q)_*[ModuleCat.{u + 1} Λ])).map
        ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i).counit.app _) =
        chernPowMap q h a := by
  set A := ModuleCat.{u + 1} Λ
  set M := (tateObject Λ X a)⟦2 * (a : ℤ)⟧
  set T := (tateObject Λ X (-(a : ℤ)))⟦2 * (-(a : ℤ))⟧
  set K := constantComplex Λ X
  set ε := (rightDerivedUpperShriekAdjunction A i).counit
  set u := supportedRestrictionMap Λ i
  set φ := supportedTranspose Λ i γ
  set χ := (R(i)_![A]).map φ ≫ ε.app M
  set e₂ : ((derivedTensor A X).obj M).obj T ⟶ K :=
    (shiftTateObjectAddIso Λ X a (-(a : ℤ))).hom ≫ (tateObjectShiftAddNegIso (a : ℤ)).hom
  set χ' := ((derivedTensor A X).map χ).app T ≫ e₂
  set N := ((derivedTensor A X).obj ((R(i)_![A]).obj (constantComplex Λ Z))).obj T
  have hφ : IsIso φ := hγ
  have hγ' : u ≫ (R(i)_![A]).map φ = γ := supportedRestrictionMap_comp_map_supportedTranspose Λ i γ
  -- `χ'` is universal for objects supported on `Z`
  have huniv : IsSupportedUniversal Λ i χ' := by
    intro S' hS'
    obtain ⟨M', ⟨eM⟩, ⟨eM'⟩⟩ :=
      DerivedCategory.isInvertible.shift (isInvertible_tateObject Λ X (-(a : ℤ))) (2 * (-(a : ℤ)))
    have h₁ := bijective_comp_derivedTensor_map_app _ eM eM' χ
      ((isIso_iff_isSupportedUniversal Λ i φ).1 hφ _ (hS'.derivedTensor M'))
    exact bijective_comp_comp h₁ (bijective_comp_right_of_isIso _)
  have hN : IsSupported Λ i N := (isSupported_rightDerivedLowerShriek Λ i _).derivedTensor T
  -- `χ'` factors through the counit by an isomorphism `θ`
  obtain ⟨θ, hθ⟩ := (bijective_comp_counit Λ i hN K).2 χ'
  dsimp only at hθ
  have hθiso : IsIso θ := by
    have hb : ∀ S', IsSupported Λ i S' → Function.Bijective (fun f : S' ⟶ N ↦ f ≫ θ) :=
      fun S' hS' ↦ bijective_comp_of_bijective_comp_comp (by
        have : (fun f : S' ⟶ N ↦ f ≫ θ ≫ ε.app K) = fun f ↦ f ≫ χ' := by rw [hθ]
        rw [this]
        exact huniv S' hS') (bijective_comp_counit Λ i hS' K)
    exact isIso_of_bijective_comp_right _
      (hb _ (isSupported_rightDerivedLowerShriek Λ i _)).2 (hb _ hN).1
  -- the morphism `Lq^* Λ_S(-a)[-2a] ⟶ Ri_! Ri^! Λ_X`
  set y := (leftDerivedUpperStarTateShiftIso Λ q (-(a : ℤ))).hom ≫
    (derivedTensorLeftUnitor A X T).inv ≫ ((derivedTensor A X).map u).app T ≫ θ
  have hy : y ≫ ε.app K = (leftDerivedUpperStarTateShiftIso Λ q (-(a : ℤ))).hom ≫
      (derivedTensorLeftUnitor A X T).inv ≫ ((derivedTensor A X).map (chernPow h a)).app T ≫
      e₂ := by
    simp only [y, Category.assoc, hθ, χ', ← hforget, ← hγ', χ, Functor.map_comp,
      NatTrans.comp_app]
  have hLy : IsIso ((L((i)^*[A])).map y) := by
    have := isIso_leftDerivedUpperStar_map_supportedRestrictionMap Λ i
    have hn := leftDerivedUpperStarTensorIso_hom_naturality_left A i u T
    have : IsIso ((L((i)^*[A])).map (((derivedTensor A X).map u).app T) ≫
        (leftDerivedUpperStarTensorIso A i _ T).hom) := by
      rw [hn]
      infer_instance
    have : IsIso ((L((i)^*[A])).map (((derivedTensor A X).map u).app T)) :=
      IsIso.of_isIso_comp_right _ (leftDerivedUpperStarTensorIso A i _ T).hom
    simp only [y, Functor.map_comp]
    infer_instance
  refine ⟨_, isIso_homEquiv_of_isIso_leftDerivedUpperStar_map Λ q i y hLy, ?_⟩
  rw [← Adjunction.homEquiv_naturality_right, hy]
  rfl

end TopClass

section Biproduct

variable {C : Type*} [Category C] [Preadditive C] [HasFiniteBiproducts C]

/-- A morphism out of a biproduct indexed by `Fin (N + 1)` is an isomorphism if its last component
together with the morphism out of the first `N` summands is one. -/
lemma isIso_biproduct_desc_of_isIso_biprod_desc {N : ℕ} {F : Fin (N + 1) → C} {Y : C}
    (g : ∀ a, F a ⟶ Y)
    (h : IsIso (biprod.desc (g (Fin.last N)) (biproduct.desc fun a : Fin N ↦ g a.castSucc))) :
    IsIso (biproduct.desc g) := by
  let e : (⨁ F) ≅ F (Fin.last N) ⊞ ⨁ (fun a : Fin N ↦ F a.castSucc) :=
    { hom := biprod.lift (biproduct.π F _) (biproduct.lift fun a ↦ biproduct.π F a.castSucc)
      inv := biprod.desc (biproduct.ι F _) (biproduct.desc fun a ↦ biproduct.ι F a.castSucc)
      hom_inv_id := by
        rw [biprod.lift_desc, biproduct.lift_desc, ← biproduct.total (f := F),
          Fin.sum_univ_castSucc, add_comm]
      inv_hom_id := by
        ext
        · simp
        · simp [biproduct.ι_π, Fin.castSucc_ne_last]
        · refine biproduct.hom_ext' _ _ fun a ↦ ?_
          simp [biproduct.ι_π, (Fin.castSucc_ne_last a).symm]
        · refine biproduct.hom_ext' _ _ fun a ↦ biproduct.hom_ext _ _ fun b ↦ ?_
          simp [biproduct.ι_π, Fin.castSucc_inj] }
  have : biproduct.desc g = e.hom ≫
      biprod.desc (g (Fin.last N)) (biproduct.desc fun a : Fin N ↦ g a.castSucc) := by
    refine biproduct.hom_ext' _ _ fun b ↦ ?_
    induction b using Fin.lastCases with
    | last => simp [e, biproduct.ι_π, Fin.castSucc_ne_last]
    | cast a => simp [e, biproduct.ι_π, (Fin.castSucc_ne_last a).symm, Fin.castSucc_inj]
  rw [this]
  infer_instance

end Biproduct

end Etale

end AlgebraicGeometry
