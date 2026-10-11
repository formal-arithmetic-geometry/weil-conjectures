/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.SupportsBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso

/-!
# Base change of products of Kummer boundaries

The iterated cup product with supports `∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_n)` of the Kummer boundaries of global
functions (`AlgebraicGeometry.Etale.kummerBoundaryProduct`) is compatible with base change along
every morphism `e : U' ⟶ U`: its restriction of supports is the product of the Kummer boundaries
of the pulled back functions `e^* f_a`.

This combines the base change of a single Kummer boundary
(`AlgebraicGeometry.Etale.kummerBoundary_baseChange`) with the base change of cup products with
supports (`AlgebraicGeometry.Etale.restrictSupportedClass_cupWithSupports`), and the
compatibility of the Tate twist datum with pullback.

## Main statements

- `AlgebraicGeometry.Etale.leftDerivedUpperStar_map_shiftTateObjectAddIso`
- `AlgebraicGeometry.Etale.restrictSupportedClass_kummerBoundaryProduct`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {U U' : Scheme.{u}}

/-- Pullback along a shift of an equation of shift amounts. -/
@[reassoc]
lemma leftDerivedUpperStar_map_eqToHom_shift_comp_commShiftIso_hom (e : U' ⟶ U)
    {K K' : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hK : K = K')
    {n n' : ℤ} (h : n = n') :
    (L((e)^*[ModuleCat.{u + 1} Λ])).map (eqToHom (by rw [hK, h]) : K⟦n⟧ ⟶ K'⟦n'⟧) ≫
        ((L((e)^*[ModuleCat.{u + 1} Λ])).commShiftIso n').hom.app K' =
      ((L((e)^*[ModuleCat.{u + 1} Λ])).commShiftIso n).hom.app K ≫
        eqToHom (by rw [hK, h]) := by
  subst hK h
  simp

/-- Shifting a morphism across an equation of shift amounts. -/
@[reassoc]
lemma eqToHom_comp_shift_map {X X' Y : DerivedCategory (Sheaf U'.smallEtaleTopology
      (ModuleCat.{u + 1} Λ))} (hX : X = X') {n n' : ℤ} (h : n = n') (f : X' ⟶ Y) :
    (eqToHom (by rw [hX, h]) : X⟦n⟧ ⟶ X'⟦n'⟧) ≫ f⟦n'⟧' =
      (eqToHom hX ≫ f)⟦n⟧' ≫ eqToHom (by rw [h]) := by
  subst hX h
  simp

/-- `K⟦a⟧ ⊗ M⟦b⟧ ≅ (K ⊗ M)⟦a + b⟧` is natural in both factors. -/
@[reassoc]
lemma derivedTensorHom_shift_comp_derivedTensorShiftIso_hom {X : Scheme.{u}}
    {K K' M M' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (f : K ⟶ K') (g : M ⟶ M') (a b : ℤ) :
    derivedTensorHom _ (f⟦a⟧') (g⟦b⟧') ≫ (derivedTensorShiftIso _ K' M' a b).hom =
      (derivedTensorShiftIso _ K M a b).hom ≫ (derivedTensorHom _ f g)⟦a + b⟧' := by
  simp only [derivedTensorHom, Category.assoc, Functor.map_comp]
  rw [derivedTensorShiftIso_hom_naturality_right, derivedTensorShiftIso_hom_naturality_left_assoc]

section Twist

variable [HasTateTwist Λ]

/-- **The Tate twist identifications are compatible with pullback**:
`Le^* (Λ(m)[2m] ⊗ Λ(m')[2m'] ≅ Λ(m + m')[2(m + m')])` is the corresponding identification
on `U'`, through `Le^* (K ⊗ M) ≅ Le^* K ⊗ Le^* M` and `Le^* Λ_U(m)[2m] ≅ Λ_{U'}(m)[2m]`. -/
lemma leftDerivedUpperStar_map_shiftTateObjectAddIso (e : U' ⟶ U) (m m' : ℤ) :
    (L((e)^*[ModuleCat.{u + 1} Λ])).map (shiftTateObjectAddIso Λ U m m').hom ≫
        (leftDerivedUpperStarTateShiftIso Λ e (m + m')).hom =
      (leftDerivedUpperStarTensorIso _ e _ _).hom ≫
        derivedTensorHom _ (leftDerivedUpperStarTateShiftIso Λ e m).hom
          (leftDerivedUpperStarTateShiftIso Λ e m').hom ≫
        (shiftTateObjectAddIso Λ U' m m').hom := by
  have hc : (L((e)^*[ModuleCat.{u + 1} Λ])).map (HasTateTwist.twistObjectAddIso U m m').hom ≫
      (HasTateTwist.leftDerivedUpperStarTwistObjectIso e (m + m')).hom =
        (leftDerivedUpperStarTensorIso _ e _ _).hom ≫
          derivedTensorHom _ (HasTateTwist.leftDerivedUpperStarTwistObjectIso e m).hom
            (HasTateTwist.leftDerivedUpperStarTwistObjectIso e m').hom ≫
          (HasTateTwist.twistObjectAddIso U' m m').hom := by
    rw [HasTateTwist.leftDerivedUpperStar_map_twistObjectAddIso]
    simp only [derivedTensorHom, Category.assoc]
  have hd : (L((e)^*[ModuleCat.{u + 1} Λ])).map (derivedTensorShiftIso _
      (HasTateTwist.twistObject (Λ := Λ) U m) (HasTateTwist.twistObject U m') (2 * m)
        (2 * m')).hom ≫
      ((L((e)^*[ModuleCat.{u + 1} Λ])).commShiftIso (2 * m + 2 * m')).hom.app _ ≫
        (leftDerivedUpperStarTensorIso _ e _ _).hom⟦2 * m + 2 * m'⟧' =
      (leftDerivedUpperStarTensorIso _ e _ _).hom ≫
        derivedTensorHom _ (((L((e)^*[ModuleCat.{u + 1} Λ])).commShiftIso (2 * m)).hom.app _)
          (((L((e)^*[ModuleCat.{u + 1} Λ])).commShiftIso (2 * m')).hom.app _) ≫
        (derivedTensorShiftIso _ _ _ _ _).hom := by
    simp only [leftDerivedUpperStarTensorIso_hom, derivedTensorHom, Category.assoc]
    exact leftDerivedUpperStarTensorComparison_derivedTensorShiftIso _ e _ _ _ _
  simp only [shiftTateObjectAddIso, leftDerivedUpperStarTateShiftIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, eqToIso.hom, Functor.map_comp, Category.assoc, tateObject,
    leftDerivedUpperStarTateObjectIso]
  rw [leftDerivedUpperStar_map_eqToHom_shift_comp_commShiftIso_hom_assoc Λ e rfl (by ring),
    eqToHom_comp_shift_map Λ rfl (by ring)]
  simp only [eqToHom_refl, Category.id_comp]
  simp only [← Category.assoc]
  congr 1
  simp only [Category.assoc]
  rw [Functor.commShiftIso_hom_naturality_assoc, ← Functor.map_comp, hc, Functor.map_comp,
    Functor.map_comp, reassoc_of% hd, ← derivedTensorHom_comp_assoc,
    derivedTensorHom_shift_comp_derivedTensorShiftIso_hom_assoc]

/-- The Tate twist datum on pulled back twisting objects, `Le^* Λ_U(m) ≅ Λ_{U'}(m)`, across an
equation of twists. -/
@[reassoc]
lemma leftDerivedUpperStar_map_eqToHom_twistObject (e : U' ⟶ U) {m m' : ℤ} (h : m = m') :
    (L((e)^*[ModuleCat.{u + 1} Λ])).map (eqToHom (by rw [h]) :
        HasTateTwist.twistObject (Λ := Λ) U m ⟶ HasTateTwist.twistObject U m') ≫
      (HasTateTwist.leftDerivedUpperStarTwistObjectIso e m').hom =
        (HasTateTwist.leftDerivedUpperStarTwistObjectIso e m).hom ≫ eqToHom (by rw [h]) := by
  subst h
  simp

/-- The identifications `Le^* (Λ(m)[2m]) ≅ Λ(m)[2m]` are compatible with composition. -/
lemma leftDerivedUpperStarTateShiftIso_comp {U₂ : Scheme.{u}} (e₁ : U₂ ⟶ U') (e : U' ⟶ U)
    (e' : U₂ ⟶ U) (he : e' = e₁ ≫ e) (m : ℤ) :
    leftDerivedUpperStarTateShiftIso Λ e' m =
      (leftDerivedUpperStarComp _ e₁ e e' he).app _ ≪≫
        (L((e₁)^*[ModuleCat.{u + 1} Λ])).mapIso (leftDerivedUpperStarTateShiftIso Λ e m) ≪≫
          leftDerivedUpperStarTateShiftIso Λ e₁ m := by
  have h₁ := NatTrans.shift_app_comm (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) e₁ e e' he).hom
    (2 * m) (tateObject Λ U m)
  rw [Functor.commShiftIso_comp_hom_app] at h₁
  ext
  simp only [leftDerivedUpperStarTateShiftIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc, leftDerivedUpperStarTateObjectIso_comp e₁ e e' he m]
  rw [reassoc_of% h₁]
  simp only [← Functor.map_comp]
  erw [Functor.commShiftIso_hom_naturality_assoc]
  rw [Functor.map_comp]

end Twist

/-- Tensor product of identities. -/
@[simp]
lemma derivedTensorHom_id {X : Scheme.{u}}
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    derivedTensorHom _ (𝟙 K) (𝟙 M) = 𝟙 _ := by
  simp [derivedTensorHom]

section Kummer

variable [Finite Λ] [HasKummerClass Λ]

omit [Finite Λ] in
/-- The diagonal `Λ_U ⟶ Λ_U ⊗ Λ_U` along which classes are multiplied
(`AlgebraicGeometry.Etale.constantComplexDiagonal`) is compatible with pullback. -/
lemma constantComplexDiagonal_comp_derivedTensorHom (e : U' ⟶ U) :
    constantComplexDiagonal Λ U' ≫
        derivedTensorHom _ (leftDerivedUpperStarConstantComplexIso Λ e).inv
          (leftDerivedUpperStarConstantComplexIso Λ e).inv =
      (leftDerivedUpperStarConstantComplexIso Λ e).inv ≫
        (L((e)^*[ModuleCat.{u + 1} Λ])).map (constantComplexDiagonal Λ U) ≫
          (leftDerivedUpperStarTensorIso _ e _ _).hom := by
  have hdiag : ∀ X : Scheme.{u}, constantComplexDiagonal Λ X =
      (HasTateTwist.twistObjectZeroIso (Λ := Λ) X).inv ≫ eqToHom (by rw [add_zero]) ≫
        (HasTateTwist.twistObjectAddIso X 0 0).inv ≫
          derivedTensorHom _ (HasTateTwist.twistObjectZeroIso X).hom
            (HasTateTwist.twistObjectZeroIso X).hom := fun X ↦ by
    simp [constantComplexDiagonal, derivedTensorHom]
  set p := HasTateTwist.leftDerivedUpperStarTwistObjectIso (Λ := Λ) e 0
  have hc : (L((e)^*[ModuleCat.{u + 1} Λ])).map (HasTateTwist.twistObjectAddIso U 0 0).hom ≫
      (HasTateTwist.leftDerivedUpperStarTwistObjectIso e (0 + 0)).hom =
        (leftDerivedUpperStarTensorIso _ e _ _).hom ≫ derivedTensorHom _ p.hom p.hom ≫
          (HasTateTwist.twistObjectAddIso U' 0 0).hom := by
    rw [HasTateTwist.leftDerivedUpperStar_map_twistObjectAddIso]
    simp only [derivedTensorHom, Category.assoc, p]
  have h₁ : (leftDerivedUpperStarTensorIso _ e _ _).hom ≫ derivedTensorHom _ p.hom p.hom =
      (L((e)^*[ModuleCat.{u + 1} Λ])).map (HasTateTwist.twistObjectAddIso U 0 0).hom ≫
        (HasTateTwist.leftDerivedUpperStarTwistObjectIso e (0 + 0)).hom ≫
          (HasTateTwist.twistObjectAddIso U' 0 0).inv := by
    rw [reassoc_of% hc, Iso.hom_inv_id, Category.comp_id]
  have hc' : (L((e)^*[ModuleCat.{u + 1} Λ])).map (HasTateTwist.twistObjectAddIso U 0 0).inv ≫
      (leftDerivedUpperStarTensorIso _ e _ _).hom =
        (HasTateTwist.leftDerivedUpperStarTwistObjectIso e (0 + 0)).hom ≫
          (HasTateTwist.twistObjectAddIso U' 0 0).inv ≫ derivedTensorHom _ p.inv p.inv := by
    have : (leftDerivedUpperStarTensorIso _ e _ _).hom =
        (leftDerivedUpperStarTensorIso _ e _ _).hom ≫ derivedTensorHom _ p.hom p.hom ≫
          derivedTensorHom _ p.inv p.inv := by
      rw [derivedTensorHom_comp, Iso.hom_inv_id, derivedTensorHom_id, Category.comp_id]
    rw [this, reassoc_of% h₁, ← Functor.map_comp_assoc, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  rw [hdiag, hdiag]
  simp only [leftDerivedUpperStarConstantComplexIso, Iso.trans_inv, Functor.mapIso_inv,
    Iso.symm_inv, Category.assoc, Functor.map_comp]
  rw [derivedTensorHom_comp, Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp, leftDerivedUpperStarTensorIso_hom_naturality,
    reassoc_of% hc', leftDerivedUpperStar_map_eqToHom_twistObject_assoc Λ e (add_zero 0).symm]
  simp only [Iso.inv_hom_id_assoc, derivedTensorHom_comp]
  rfl

/-- Closed subschemes cut out by global sections pull back to the closed subschemes cut out by the
pulled back sections. -/
lemma exists_isPullback_zeroLocusSubschemeι (e : U' ⟶ U) (s : Set Γ(U, ⊤))
    (s' : Set Γ(U', ⊤)) (hs : e.appTop '' s = s') :
    ∃ g, IsPullback g (U'.zeroLocusSubschemeι s') (U.zeroLocusSubschemeι s) e := by
  subst hs
  exact ⟨_, isPullback_zeroLocusSubschemeι e s⟩

/-- Restriction of supports across an equation of twists. -/
lemma restrictSupportedClass_comp_eqToHom (e : U' ⟶ U) {Z Z' : Scheme.{u}} (i : Z ⟶ U)
    (i' : Z' ⟶ U') [IsClosedImmersion i] [IsClosedImmersion i'] (g : Z' ⟶ Z)
    (hg : IsPullback g i' i e) {k k' : ℤ} (h : k = k')
    (γ : constantComplex Λ U ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i)^![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ U k)⟦2 * k⟧))) :
    restrictSupportedClass (ModuleCat.{u + 1} Λ) e i i' g hg
        (leftDerivedUpperStarConstantComplexIso Λ e).inv (leftDerivedUpperStarTateShiftIso Λ e k')
        (γ ≫ eqToHom (by rw [h])) =
      restrictSupportedClass (ModuleCat.{u + 1} Λ) e i i' g hg
          (leftDerivedUpperStarConstantComplexIso Λ e).inv (leftDerivedUpperStarTateShiftIso Λ e k)
          γ ≫ eqToHom (by rw [h]) := by
  subst h
  simp

omit [Finite Λ] in
/-- The unit class `Λ_U ≅ Λ_U(0)[0]` is compatible with pullback. -/
lemma leftDerivedUpperStarConstantComplexIso_inv_comp_map_twistObjectZeroIso_inv (e : U' ⟶ U)
    {a : ℤ} (ha : a = 0) :
    (leftDerivedUpperStarConstantComplexIso Λ e).inv ≫
        (L((e)^*[ModuleCat.{u + 1} Λ])).map ((HasTateTwist.twistObjectZeroIso (Λ := Λ) U).inv ≫
          (shiftFunctorZero' _ a ha).inv.app _) ≫
        ((L((e)^*[ModuleCat.{u + 1} Λ])).commShiftIso a).hom.app _ ≫
          ((HasTateTwist.leftDerivedUpperStarTwistObjectIso (Λ := Λ) e 0).hom)⟦a⟧' =
      (HasTateTwist.twistObjectZeroIso U').inv ≫ (shiftFunctorZero' _ a ha).inv.app _ := by
  subst ha
  simp only [shiftFunctorZero', eqToIso_refl, Iso.refl_trans]
  simp only [leftDerivedUpperStarConstantComplexIso, Functor.commShiftIso_zero, Iso.trans_inv,
    Functor.mapIso_inv, Iso.symm_inv, Category.assoc, Functor.CommShift.isoZero_hom_app,
    Functor.map_comp, Functor.comp_obj]
  rw [← Functor.map_comp_assoc _ (HasTateTwist.twistObjectZeroIso U).hom, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id]
  rw [Category.id_comp, ← (shiftFunctorZero _ ℤ).inv.naturality, Functor.id_map,
    Iso.inv_hom_id_assoc]

/-- **Base change of products of Kummer boundaries.** For `e : U' ⟶ U` and global functions
`f₁, …, f_n` on `U` with pullbacks `f'_a = e^* f_a`, restricting
`∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_n) ∈ H^{2n}_{V(f)}(U, Λ(n))` along `e` gives
`∂κ(f'₁) ∪ ⋯ ∪ ∂κ(f'_n) ∈ H^{2n}_{V(f')}(U', Λ(n))`. -/
theorem restrictSupportedClass_kummerBoundaryProduct (e : U' ⟶ U) :
    ∀ {n : ℕ} (f : Fin n → Γ(U, ⊤)) (f' : Fin n → Γ(U', ⊤)) (_ : ∀ a, e.appTop (f a) = f' a)
      (g : U'.zeroLocusSubscheme (Set.range f') ⟶ U.zeroLocusSubscheme (Set.range f))
      (hg : IsPullback g (U'.zeroLocusSubschemeι (Set.range f'))
        (U.zeroLocusSubschemeι (Set.range f)) e),
      restrictSupportedClass (ModuleCat.{u + 1} Λ) e _ _ g hg
          (leftDerivedUpperStarConstantComplexIso Λ e).inv
          (leftDerivedUpperStarTateShiftIso Λ e n) (kummerBoundaryProduct Λ f) =
        kummerBoundaryProduct Λ f'
  | 0, f, f', hf, g, hg => by
    rw [kummerBoundaryProduct, kummerBoundaryProduct]
    refine restrictSupportedClass_liftCounitOfRangeEqUniv _ e _ _ _ _ g hg _ _ _ _ ?_
    exact leftDerivedUpperStarConstantComplexIso_inv_comp_map_twistObjectZeroIso_inv Λ e _
  | n + 1, f, f', hf, g, hg => by
    obtain ⟨g₁, hg₁⟩ := exists_isPullback_zeroLocusSubschemeι e {f 0} {f' 0} (by simp [hf])
    obtain ⟨g₂, hg₂⟩ := exists_isPullback_zeroLocusSubschemeι e (Set.range (Fin.tail f))
      (Set.range (Fin.tail f')) (by
        ext x
        simp only [Set.mem_image, Set.mem_range, Fin.tail]
        constructor
        · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
          exact ⟨a, (hf _).symm⟩
        · rintro ⟨a, rfl⟩
          exact ⟨_, ⟨a, rfl⟩, hf _⟩)
    have ih := restrictSupportedClass_kummerBoundaryProduct e (Fin.tail f) (Fin.tail f')
      (fun a ↦ hf _) g₂ hg₂
    rw [kummerBoundaryProduct, kummerBoundaryProduct,
      restrictSupportedClass_comp_eqToHom Λ e _ _ g hg (by push_cast; ring)]
    congr 1
    simp only [cupWithSupportsTateObject]
    rw [restrictSupportedClass_map _ e _ _ g hg _
      (leftDerivedUpperStarTensorIso _ e _ _ ≪≫
        ((derivedTensor _ U').mapIso (leftDerivedUpperStarTateShiftIso Λ e 1)).app _ ≪≫
          ((derivedTensor _ U').obj _).mapIso (leftDerivedUpperStarTateShiftIso Λ e n))
      _ _ _ (by
        rw [leftDerivedUpperStar_map_shiftTateObjectAddIso]
        simp only [derivedTensorHom, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
          Category.assoc]; rfl),
      restrictSupportedClass_cupWithSupports _ e _ _ _ _ _ _ _ _ g₁ g₂ g hg₁ hg₂ hg _ _ _ _ _
        (constantComplexDiagonal_comp_derivedTensorHom Λ e), ih]
    · congr 3
      erw [restrictSupportedClass_shiftSupportedClass]
      congr 1
      exact kummerBoundary_baseChange_of_eq Λ e (f 0) (f' 0) (hf 0) g₁ hg₁
    · rw [Fin.range_fin_succ, range_zeroLocusSubschemeι_insert]

end Kummer

end Etale

end AlgebraicGeometry
