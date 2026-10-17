/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSection
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerProductAppend
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerProductBaseChange
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ThomClassProduct
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.SixFunctors.Etale.Derived.SupportsEtale

/-!
# The Thom class of the zero section of affine space

For the zero section `z : B ↪ 𝔸^c_B`, realised as the closed subscheme cut out by the
coordinates `t₁, …, t_c`, the cup product with supports `∂κ(t₁) ∪ ⋯ ∪ ∂κ(t_c)` of the Kummer
boundaries of the coordinates (`AlgebraicGeometry.Etale.kummerBoundaryProduct`) is the Thom
class: its adjoint `Λ_B ⟶ Rz^! (Λ(c)[2c])` is an isomorphism. This is the generator clause of
clause (i) of `sk-prop-an`; the bare isomorphism `Rz^! Λ(c)[2c] ≅ Λ_B` is
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_affineSpaceZero`.

The proof is an induction on `c`. Write `𝔸^{c+1}_B = 𝔸¹_{B'}` with `B' = 𝔸^c_B`, the first
coordinate becoming the coordinate `t` of the affine line. The product of Kummer boundaries is
`∂κ(t) ∪ (∂κ(t₂) ∪ ⋯)`, and the cup product of Thom classes is a Thom class
(`AlgebraicGeometry.Etale.isIso_supportedTranspose_cupWithSupports`): `∂κ(t)` is the Thom class
of the zero section of `𝔸¹_{B'}` by the rank-one normalisation
(`AlgebraicGeometry.Etale.HasKummerClass.IsNormalized`), and the restriction of `∂κ(t₂) ∪ ⋯` to
`V(t) ≅ B'` is the class of the zero section of `B' = 𝔸^c_B`, a Thom class by induction.
Thom classes are transported along étale maps
(`AlgebraicGeometry.Etale.isIso_supportedClassMap_kummerBoundaryProduct_of_etale`).

## Main statements

- `AlgebraicGeometry.Etale.isIso_supportedClassMap_kummerBoundaryProduct_of_etale`
- `AlgebraicGeometry.Etale.isIso_supportedClassMap_kummerBoundaryProduct_cons_coord`
- `AlgebraicGeometry.Etale.isIso_supportedClassMap_kummerBoundaryProduct_coord`
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Scheme

namespace AffineSpace

/-- `ULift (Fin c) ⊕ ULift (Fin 1) ≃ ULift (Fin (c + 1))`: the summand `Fin 1` becomes the first
coordinate and `Fin c` the remaining ones. -/
def sumConsEquiv (c : ℕ) : ULift.{u} (Fin c) ⊕ ULift.{u} (Fin 1) ≃ ULift.{u} (Fin (c + 1)) where
  toFun := Sum.elim (fun a ↦ ULift.up a.down.succ) fun _ ↦ ULift.up 0
  invFun x := Fin.cases (Sum.inr (ULift.up 0)) (fun a ↦ Sum.inl (ULift.up a)) x.down
  left_inv := by
    rintro (⟨a⟩ | ⟨a⟩)
    · simp
    · simp [Fin.fin_one_eq_zero a]
  right_inv := by
    rintro ⟨x⟩
    induction x using Fin.cases <;> simp

/-- `𝔸^{c+1}_B ≅ 𝔸¹_{𝔸^c_B}`, the first coordinate becoming the coordinate of the affine line. -/
noncomputable def consIso (c : ℕ) (B : Scheme.{u}) :
    𝔸(ULift.{u} (Fin (c + 1)); B) ≅ 𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin c); B)) :=
  reindexIso B (sumConsEquiv c) ≪≫ sumIso B

lemma consIso_hom_appTop_coord_zero (c : ℕ) (B : Scheme.{u}) :
    (consIso c B).hom.appTop (coord 𝔸(ULift.{u} (Fin c); B) (ULift.up 0)) =
      coord B (ULift.up 0) := by
  simp [consIso, sumIso_hom, sumHom, sumConsEquiv]

lemma consIso_hom_appTop_coord_succ (c : ℕ) (B : Scheme.{u}) (a : Fin c) :
    (consIso c B).hom.appTop ((𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin c); B)) ↘
        𝔸(ULift.{u} (Fin c); B)).appTop (coord B (ULift.up a))) =
      coord B (ULift.up a.succ) := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, consIso, Iso.trans_hom,
    Category.assoc, sumIso_hom, sumHom_over, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    homOfVector_appTop_coord]
  simp [sumConsEquiv]

end AffineSpace

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]

section Transport

variable {X U Z Z' : Scheme.{u}}

/-- Restriction of supports along an étale map preserves Thom classes: if the adjoint
`Λ_Z ⟶ Ri^! L` of a class `γ` supported on `Z` is an isomorphism, so is the adjoint of its
restriction along an étale `e : U ⟶ X`. -/
theorem isIso_supportedClassMap_restrictSupportedClass_of_etale (e : U ⟶ X)
    [AlgebraicGeometry.Etale e] (i : Z ⟶ X) (i' : Z' ⟶ U) [IsClosedImmersion i]
    [IsClosedImmersion i'] (g : Z' ⟶ Z) (hg : IsPullback g i' i e)
    {L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {L' : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (τ : (L((e)^*[ModuleCat.{u + 1} Λ])).obj L ≅ L')
    (γ : constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i)^![ModuleCat.{u + 1} Λ]).obj L))
    (hγ : IsIso (supportedClassMap Λ i γ)) :
    IsIso (supportedClassMap Λ i' (restrictSupportedClass (ModuleCat.{u + 1} Λ) e i i' g hg
      (leftDerivedUpperStarConstantComplexIso Λ e).inv τ γ)) :=
  (isIso_supportedClassMap_restrictSupportedClass_iff Λ e i i' g hg L L' τ γ
    (isIso_supportedRestriction_of_etale Λ e i i' g hg L L' τ)).2 inferInstance

/-- Products of Kummer boundaries which are Thom classes pull back to Thom classes along étale
maps: if `∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_n)` is a Thom class of `V(f) ⊂ U`, then for an étale `e : U' ⟶ U`,
`∂κ(e^* f₁) ∪ ⋯ ∪ ∂κ(e^* f_n)` is a Thom class of `V(e^* f) ⊂ U'`. -/
theorem isIso_supportedClassMap_kummerBoundaryProduct_of_etale {U U' : Scheme.{u}}
    [HasInvertibleExponent Λ U] [HasInvertibleExponent Λ U'] (e : U' ⟶ U)
    [AlgebraicGeometry.Etale e] {n : ℕ} (f : Fin n → Γ(U, ⊤)) (f' : Fin n → Γ(U', ⊤))
    (hf : ∀ a, e.appTop (f a) = f' a)
    (hγ : IsIso (supportedClassMap Λ (U.zeroLocusSubschemeι (Set.range f))
      (kummerBoundaryProduct Λ f))) :
    IsIso (supportedClassMap Λ (U'.zeroLocusSubschemeι (Set.range f'))
      (kummerBoundaryProduct Λ f')) := by
  have hs : e.appTop '' Set.range f = Set.range f' := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext hf)
  have hg := isPullback_zeroLocusSubschemeι e (Set.range f) (Set.range f') hs
  rw [← restrictSupportedClass_kummerBoundaryProduct Λ e f f' hf _ hg]
  exact isIso_supportedClassMap_restrictSupportedClass_of_etale Λ e _ _ _ hg _ _ hγ

/-- Transporting a class along an equality of twists does not affect whether it is a Thom
class. -/
lemma isIso_supportedClassMap_comp_eqToHom {U Z : Scheme.{u}} [HasInvertibleExponent Λ U]
    (i : Z ⟶ U) [IsClosedImmersion i] {m m' : ℤ} (hm : m = m')
    (γ : constantComplex Λ U ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i)^![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ U m)⟦2 * m⟧)))
    (h : (R(i)_![ModuleCat.{u + 1} Λ]).obj
        ((R(i)^![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ U m)⟦2 * m⟧)) =
      (R(i)_![ModuleCat.{u + 1} Λ]).obj
        ((R(i)^![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ U m')⟦2 * m'⟧))) :
    IsIso (supportedClassMap Λ i (γ ≫ eqToHom h)) ↔ IsIso (supportedClassMap Λ i γ) := by
  subst hm
  simp

/-- A class supported everywhere which lifts an isomorphism `Λ_U ≅ L` through the counit is a
Thom class. -/
lemma isIso_supportedClassMap_liftCounitOfRangeEqUniv {U Z : Scheme.{u}} (i : Z ⟶ U)
    [IsClosedImmersion i] (hi : Set.range i.base = Set.univ)
    {L : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : constantComplex Λ U ⟶ L) [IsIso φ] :
    IsIso (supportedClassMap Λ i
      (liftCounitOfRangeEqUniv (ModuleCat.{u + 1} Λ) i hi φ)) := by
  have : IsEmpty i.openComplement.toScheme := ⟨fun x ↦ x.2 (hi ▸ Set.mem_univ _)⟩
  have hsupp : ∀ S, IsSupported Λ i S := fun S ↦
    isZero_derivedCategory_of_isEmpty (ModuleCat.{u + 1} Λ) _ _
  set u' := supportedRestrictionMap Λ i
  have hu : IsIso u' := by
    refine isIso_of_bijective_comp_left u' fun T ↦ ?_
    have := isIso_counit_app_of_isZero Λ i T (hsupp T)
    exact bijective_comp_of_iso u'
      (asIso ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i).counit.app T)).symm
      (bijective_supportedRestrictionMap_comp Λ i _)
  set γ := liftCounitOfRangeEqUniv (ModuleCat.{u + 1} Λ) i hi φ
  have hγ : γ ≫ (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i).counit.app L = φ :=
    (existsUnique_comp_counit_of_range_eq_univ (ModuleCat.{u + 1} Λ) i hi φ).exists.choose_spec
  have hχ : IsIso ((R(i)_![ModuleCat.{u + 1} Λ]).map (supportedClassMap Λ i γ) ≫
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i).counit.app L) := by
    have e : u' ≫ (R(i)_![ModuleCat.{u + 1} Λ]).map (supportedClassMap Λ i γ) ≫
        (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i).counit.app L = φ := by
      rw [← Category.assoc, supportedClassMap_eq_supportedTranspose,
        supportedRestrictionMap_comp_map_supportedTranspose, hγ]
    have : IsIso (u' ≫ (R(i)_![ModuleCat.{u + 1} Λ]).map (supportedClassMap Λ i γ) ≫
        (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i).counit.app L) := by
      rw [e]; infer_instance
    exact IsIso.of_isIso_comp_left u' _
  exact (isIso_iff_isSupportedUniversal Λ i _).2 fun S _ ↦ bijective_comp_right_of_isIso _

end Transport

section Model

variable [HasKummerClass.IsNormalized Λ]

/-- **The inductive step.** Let `B` be separated and locally of finite type over a field, and let
`s₁, …, s_c` be functions on `B` whose product of Kummer boundaries `∂κ(s₁) ∪ ⋯ ∪ ∂κ(s_c)` is a
Thom class of `V(s) ⊂ B`. On the affine line `p : 𝔸¹_B ⟶ B` with coordinate `t`, the product
`∂κ(t) ∪ ∂κ(p^* s₁) ∪ ⋯ ∪ ∂κ(p^* s_c)` is a Thom class of `V(t, p^* s) ⊂ 𝔸¹_B`.

Indeed `∂κ(t)` is the Thom class of the zero section `V(t)` (the rank-one normalisation), and
the restriction of `∂κ(p^* s₁) ∪ ⋯` to `V(t)`, which `p` identifies with `B`, is
`∂κ(s₁) ∪ ⋯`; the cup product of such classes is a Thom class
(`AlgebraicGeometry.Etale.isIso_supportedTranspose_cupWithSupports`). -/
theorem isIso_supportedClassMap_kummerBoundaryProduct_cons_coord {k : Type u} [Field k]
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of k)) [IsSeparated aB] [LocallyOfFiniteType aB]
    [HasInvertibleExponent Λ B] {c : ℕ} (s : Fin c → Γ(B, ⊤))
    (hs : IsIso (supportedClassMap Λ (B.zeroLocusSubschemeι (Set.range s))
      (kummerBoundaryProduct Λ s))) :
    IsIso (supportedClassMap Λ (𝔸(ULift.{u} (Fin 1); B).zeroLocusSubschemeι
        (Set.range (Fin.cons (AffineSpace.coord B (ULift.up 0))
          (fun a ↦ (𝔸(ULift.{u} (Fin 1); B) ↘ B).appTop (s a)) : Fin (c + 1) → _)))
      (kummerBoundaryProduct Λ (Fin.cons (AffineSpace.coord B (ULift.up 0))
          (fun a ↦ (𝔸(ULift.{u} (Fin 1); B) ↘ B).appTop (s a)) : Fin (c + 1) → _))) := by
  set A := 𝔸(ULift.{u} (Fin 1); B)
  set p := A ↘ B
  set t : Γ(A, ⊤) := AffineSpace.coord B (ULift.up 0)
  set s' : Fin c → Γ(A, ⊤) := fun a ↦ p.appTop (s a)
  set i₁ := A.zeroLocusSubschemeι {t}
  set i₂ := A.zeroLocusSubschemeι (Set.range s')
  set i := A.zeroLocusSubschemeι (Set.range (Fin.cons t s' : Fin (c + 1) → Γ(A, ⊤)))
  have : HasInvertibleExponent Λ (A.zeroLocusSubscheme {t}) := .of_hom i₁
  have hrange : Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base := by
    rw [Fin.range_cons, range_zeroLocusSubschemeι_insert]
  rw [kummerBoundaryProduct_cons Λ t s']
  refine (isIso_supportedClassMap_comp_eqToHom Λ i (by push_cast; ring) _ _).2 ?_
  rw [cupWithSupportsTateObject, supportedClassMap_eq_supportedTranspose, supportedTranspose_comp]
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ ?_ inferInstance
  -- the inclusions `V(t, p^* s) ⊆ V(t)` and `V(t, p^* s) ⊆ V(p^* s)`
  let b₁ := i.liftZeroLocusSubscheme (s := {t}) fun x hx ↦ by
    rw [Set.mem_singleton_iff.1 hx]
    exact Scheme.zeroLocusSubschemeι_appTop ⟨0, Fin.cons_zero _ _⟩
  let b₂ := i.liftZeroLocusSubscheme (s := Set.range s') fun x hx ↦ by
    obtain ⟨a, rfl⟩ := hx
    exact Scheme.zeroLocusSubschemeι_appTop ⟨a.succ, Fin.cons_succ _ _ _⟩
  -- the restriction of `p^* s` to `V(t)`
  let s'' : Fin c → Γ(A.zeroLocusSubscheme {t}, ⊤) := fun a ↦ i₁.appTop (s' a)
  have hs'' : i₁.appTop '' Set.range s' = Set.range s'' := by
    rw [← Set.range_comp]; rfl
  have hg := isPullback_zeroLocusSubschemeι i₁ (Set.range s') (Set.range s'') hs''
  have : IsIso (constantComplexDiagonal Λ A) := by
    unfold constantComplexDiagonal; infer_instance
  refine isIso_supportedTranspose_cupWithSupports Λ i₁ i₂ i hrange b₁
    (Scheme.Hom.liftZeroLocusSubscheme_zeroLocusSubschemeι _ _) b₂
    (Scheme.Hom.liftZeroLocusSubscheme_zeroLocusSubschemeι _ _) _ _ hg
    ((isInvertible_tateObject Λ A c).shift _) (leftDerivedUpperStarTateShiftIso Λ i₁ c)
    (constantComplexDiagonal Λ A) _ _ ?_ ?_
  · exact HasKummerClass.IsNormalized.isIso_supportedClassMap_kummerBoundary_coord B aB
  · rw [restrictSupportedClass_kummerBoundaryProduct Λ i₁ s' s'' (fun _ ↦ rfl) _ hg]
    -- `V(t) ⟶ 𝔸¹_B ⟶ B` is an isomorphism, the inverse of the zero section
    let e₀ := AffineSpace.zeroSectionIsoZeroLocusSubscheme (ULift.{u} (Fin 1)) B
      (s := {t}) Set.range_unique
    have : IsIso (i₁ ≫ p) := inferInstanceAs (IsIso e₀.inv)
    exact isIso_supportedClassMap_kummerBoundaryProduct_of_etale Λ (i₁ ≫ p) s s''
      (fun _ ↦ rfl) hs

/-- Blueprint `sk-prop-an`: `𝔸¹ ⇒ 𝔸ⁿ`: the model purity

**(i) The Thom class.** For the zero section `z : B ↪ 𝔸^c_B`, cut out by the coordinates
`t₁, …, t_c`, over a scheme `B` separated and locally of finite type over a field, the
isomorphism `Rz^! Λ(c)[2c] ≅ Λ_B` is generated by the fundamental class of the zero section, the
cup product with supports `∂κ(t₁) ∪ ⋯ ∪ ∂κ(t_c)` of the Kummer boundaries of the coordinates:
the adjoint `Λ_B ⟶ Rz^! (Λ(c)[2c])` of this class (`AlgebraicGeometry.Etale.supportedClassMap`)
is an isomorphism.

By induction on `c`, writing `𝔸^{c+1}_B ≅ 𝔸¹_{𝔸^c_B}` with the first coordinate as the
coordinate of the affine line
(`AlgebraicGeometry.Etale.isIso_supportedClassMap_kummerBoundaryProduct_cons_coord`). -/
theorem isIso_supportedClassMap_kummerBoundaryProduct_coord {k : Type u} [Field k] (c : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of k)) [IsSeparated aB] [LocallyOfFiniteType aB]
    [HasInvertibleExponent Λ B] :
    IsIso (supportedClassMap Λ (𝔸(ULift.{u} (Fin c); B).zeroLocusSubschemeι
        (Set.range fun a : Fin c ↦ AffineSpace.coord B (ULift.up a)))
      (kummerBoundaryProduct Λ fun a : Fin c ↦ AffineSpace.coord B (ULift.up a))) := by
  induction c with
  | zero =>
    rw [kummerBoundaryProduct]
    exact isIso_supportedClassMap_liftCounitOfRangeEqUniv Λ _ _ _
  | succ c ih =>
    have core := isIso_supportedClassMap_kummerBoundaryProduct_cons_coord Λ
      𝔸(ULift.{u} (Fin c); B) (𝔸(ULift.{u} (Fin c); B) ↘ B ≫ aB)
      (fun a : Fin c ↦ AffineSpace.coord B (ULift.up a)) ih
    refine isIso_supportedClassMap_kummerBoundaryProduct_of_etale Λ
      (AffineSpace.consIso c B).hom _ _ (fun a ↦ ?_) core
    induction a using Fin.cases with
    | zero => rw [Fin.cons_zero]; exact AffineSpace.consIso_hom_appTop_coord_zero c B
    | succ a => rw [Fin.cons_succ]; exact AffineSpace.consIso_hom_appTop_coord_succ c B a

end Model

end Etale

end AlgebraicGeometry
