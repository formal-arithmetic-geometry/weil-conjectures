/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalCoefficient
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationMap
public import WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients

/-!
# Scalar extension between the rational stages

Let `E ⊆ L` be finite extensions of `ℚ_ℓ` inside `ℚ̄_ℓ`, with rings of integers `𝒪_E ⊆ 𝒪_L`.
The scalar extension `- ⊗_E L : D_comp(Y, E) ⥤ D_comp(Y, L)` of blueprint
`def-weil-rationalization-karoubi` is computed on an integral representative `K` by the derived
base change `K ⊗ᴸ_{𝒪_E} 𝒪_L`, followed by rationalization. Here the derived base change is
characterized by its universal property (`AlgebraicGeometry.Etale.IsDerivedBaseChange`): a
morphism `η : K ⟶ Res K'` to the restriction of scalars of `K' ∈ D(Y_ét, 𝒪_L)` through which
every morphism from `K` to a restriction of scalars factors uniquely.

## Main statements

- `AlgebraicGeometry.Etale.IsDerivedBaseChange.map`: the morphism `K₁' ⟶ K₂'` induced by a
  morphism `K₁ ⟶ K₂` between objects with derived base changes; it is functorial and linear
  along `𝒪_E ⟶ 𝒪_L`.
- `AlgebraicGeometry.Etale.nonempty_iso_fromIntegral_of_isDerivedBaseChange`
  (`lem-weil-scalar-extension-well-defined`): the rationalization of the derived base change
  only depends on the rationalization of the integral representative.
-/

@[expose] public section

universe w u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime] (E L : Type w) [Field E] [Field L]
  [Algebra E (PadicAlgCl l)] [Algebra L (PadicAlgCl l)] [Algebra E L]
  [IsScalarTower E L (PadicAlgCl l)]

/-- The inclusion `𝒪_E ⟶ 𝒪_L` of rings of integers induced by an embedding `E ⟶ L` over
`ℚ̄_ℓ`. -/
noncomputable def integersMap : integers l E →+* integers l L :=
  (algebraMap E L).restrict (integers l E) (integers l L) fun x hx ↦ by
    rw [mem_integers_iff, ← IsScalarTower.algebraMap_apply]
    exact hx

lemma integersMap_injective : Function.Injective (integersMap l E L) := fun _ _ h ↦
  Subtype.ext ((algebraMap E L).injective (congrArg Subtype.val h))

variable [Small.{u + 1} E] [Small.{u + 1} L]

/-- The inclusion `𝒪_E ⟶ 𝒪_L`, between the universe `u + 1` copies of the rings of integers. -/
noncomputable def integersShrinkMap :
    Shrink.{u + 1} (integers l E) →+* Shrink.{u + 1} (integers l L) :=
  (shrinkRingEquiv l L).toRingHom.comp
    ((integersMap l E L).comp (shrinkRingEquiv l E).symm.toRingHom)

lemma integersShrinkMap_injective : Function.Injective (integersShrinkMap.{w, u} l E L) :=
  (shrinkRingEquiv l L).injective.comp
    ((integersMap_injective l E L).comp (shrinkRingEquiv l E).symm.injective)

/-- The inclusion `𝒪_E ⟶ 𝒪_L` carries nonzerodivisors to nonzerodivisors. -/
lemma integersShrinkMap_mem_nonZeroDivisors {x : Shrink.{u + 1} (integers l E)}
    (hx : x ∈ nonZeroDivisors _) : integersShrinkMap l E L x ∈ nonZeroDivisors _ := by
  have hx0 : x ≠ 0 := nonZeroDivisors.ne_zero hx
  have h0 : integersShrinkMap l E L x ≠ 0 := fun h ↦
    hx0 (integersShrinkMap_injective l E L (h.trans (map_zero _).symm))
  refine mem_nonZeroDivisors_of_ne_zero ?_
  exact h0

end PadicAlgCl

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

section RestrictScalars

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ') {X : Scheme.{u}}

/-- Restriction of scalars along `φ : Λ ⟶ Λ'` is linear along `φ`: it carries the
multiplication by `φ r` to the multiplication by `r`. -/
lemma derivedRestrictScalars_map_smul_id (r : Λ) (N : 𝐃(X, Λ')) :
    (derivedRestrictScalars φ X).map (φ r • 𝟙 N) = r • 𝟙 _ := by
  let F := Sheaf.restrictScalars X.smallEtaleTopology φ
  let P := (_root_.DerivedCategory.Q).objPreimage N
  let eN : (_root_.DerivedCategory.Q).obj P ≅ N := (_root_.DerivedCategory.Q).objObjPreimageIso N
  have h₀ : (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (φ r • 𝟙 P) = r • 𝟙 _ := by
    refine HomologicalComplex.hom_ext _ _ fun i ↦ ?_
    simp only [Functor.mapHomologicalComplex_map_f, HomologicalComplex.smul_f_apply,
      HomologicalComplex.id_f]
    ext U x
    exact (ModuleCat.restrictScalars.smul_def φ r x).symm
  have h₁ : (derivedRestrictScalars φ X).map ((_root_.DerivedCategory.Q).map (φ r • 𝟙 P)) =
      r • 𝟙 _ := by
    have h : (derivedRestrictScalars φ X).map ((_root_.DerivedCategory.Q).map (φ r • 𝟙 P)) ≫
        F.mapDerivedCategoryFactors.hom.app P = F.mapDerivedCategoryFactors.hom.app P ≫
          (_root_.DerivedCategory.Q).map ((F.mapHomologicalComplex _).map (φ r • 𝟙 P)) :=
      F.mapDerivedCategoryFactors.hom.naturality (φ r • 𝟙 P)
    rw [← cancel_mono (F.mapDerivedCategoryFactors.hom.app P), h, h₀, Functor.map_smul,
      CategoryTheory.Functor.map_id, Linear.comp_smul]
    simp only [Linear.smul_comp, Category.id_comp]
    erw [Category.comp_id]
  have h₂ : φ r • 𝟙 N = eN.inv ≫ (_root_.DerivedCategory.Q).map (φ r • 𝟙 P) ≫ eN.hom := by
    rw [Functor.map_smul, CategoryTheory.Functor.map_id, Linear.smul_comp, Linear.comp_smul,
      Category.id_comp, Iso.inv_hom_id]
  rw [h₂, Functor.map_comp, Functor.map_comp, h₁, Linear.smul_comp, Linear.comp_smul,
    Category.id_comp, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]

/-- Restriction of scalars along `φ : Λ ⟶ Λ'` is linear along `φ`. -/
lemma derivedRestrictScalars_map_smul (r : Λ) {N N' : 𝐃(X, Λ')} (g : N ⟶ N') :
    (derivedRestrictScalars φ X).map (φ r • g) = r • (derivedRestrictScalars φ X).map g := by
  have : φ r • g = g ≫ (φ r • 𝟙 N') := by rw [Linear.comp_smul, Category.comp_id]
  rw [this, Functor.map_comp, derivedRestrictScalars_map_smul_id, Linear.comp_smul,
    Category.comp_id]

end RestrictScalars

namespace IsDerivedBaseChange

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {φ : Λ →+* Λ'} {X : Scheme.{u}}
  {K₁ K₂ K₃ : 𝐃(X, Λ)} {K₁' K₂' K₃' : 𝐃(X, Λ')}
  {η₁ : K₁ ⟶ (derivedRestrictScalars φ X).obj K₁'}
  {η₂ : K₂ ⟶ (derivedRestrictScalars φ X).obj K₂'}
  {η₃ : K₃ ⟶ (derivedRestrictScalars φ X).obj K₃'}

/-- The morphism out of a derived base change corresponding to a morphism into a restriction of
scalars. -/
noncomputable def lift (h₁ : IsDerivedBaseChange η₁) {N : 𝐃(X, Λ')}
    (f : K₁ ⟶ (derivedRestrictScalars φ X).obj N) : K₁' ⟶ N :=
  ((h₁ N).2 f).choose

@[reassoc (attr := simp)]
lemma fac (h₁ : IsDerivedBaseChange η₁) {N : 𝐃(X, Λ')}
    (f : K₁ ⟶ (derivedRestrictScalars φ X).obj N) :
    η₁ ≫ (derivedRestrictScalars φ X).map (h₁.lift f) = f :=
  ((h₁ N).2 f).choose_spec

lemma hom_ext (h₁ : IsDerivedBaseChange η₁) {N : 𝐃(X, Λ')} {g g' : K₁' ⟶ N}
    (h : η₁ ≫ (derivedRestrictScalars φ X).map g = η₁ ≫ (derivedRestrictScalars φ X).map g') :
    g = g' :=
  (h₁ N).1 h

/-- The morphism `K₁' ⟶ K₂'` between derived base changes induced by a morphism `K₁ ⟶ K₂`: the
unique morphism compatible with `η₁` and `η₂`. -/
noncomputable def map (h₁ : IsDerivedBaseChange η₁) (η₂ : K₂ ⟶ (derivedRestrictScalars φ X).obj K₂')
    (f : K₁ ⟶ K₂) : K₁' ⟶ K₂' :=
  h₁.lift (f ≫ η₂)

@[reassoc (attr := simp)]
lemma map_fac (h₁ : IsDerivedBaseChange η₁) (f : K₁ ⟶ K₂) :
    η₁ ≫ (derivedRestrictScalars φ X).map (h₁.map η₂ f) = f ≫ η₂ :=
  h₁.fac _

lemma map_id (h₁ : IsDerivedBaseChange η₁) : h₁.map η₁ (𝟙 K₁) = 𝟙 K₁' :=
  h₁.hom_ext (by rw [map_fac, Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id])

lemma map_comp (h₁ : IsDerivedBaseChange η₁) (h₂ : IsDerivedBaseChange η₂) (f : K₁ ⟶ K₂)
    (g : K₂ ⟶ K₃) : h₁.map η₃ (f ≫ g) = h₁.map η₂ f ≫ h₂.map η₃ g :=
  h₁.hom_ext (by rw [map_fac, Functor.map_comp, map_fac_assoc, map_fac, Category.assoc])

lemma map_smul (h₁ : IsDerivedBaseChange η₁) (r : Λ) (f : K₁ ⟶ K₂) :
    h₁.map η₂ (r • f) = φ r • h₁.map η₂ f :=
  h₁.hom_ext (by
    rw [map_fac, derivedRestrictScalars_map_smul, Linear.comp_smul, map_fac, Linear.smul_comp])

end IsDerivedBaseChange

section Rational

variable (l : ℕ) [Fact l.Prime] (E L : Type w) [Field E] [Field L]
  [Algebra E (PadicAlgCl l)] [Algebra L (PadicAlgCl l)] [Algebra E L]
  [IsScalarTower E L (PadicAlgCl l)] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E] [Algebra ℚ_[l] L] [IsScalarTower ℚ_[l] L (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] L] [Small.{u + 1} E] [Small.{u + 1} L]

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

/-- In a category, a morphism `a` with `a ≫ b` and `b ≫ a` isomorphisms is an isomorphism. -/
lemma _root_.CategoryTheory.isIso_of_isIso_comp_of_isIso_comp {C : Type*} [Category C]
    {P Q : C} (a : P ⟶ Q) (b : Q ⟶ P) (h₁ : IsIso (a ≫ b)) (h₂ : IsIso (b ≫ a)) : IsIso a := by
  have : IsSplitMono a := IsSplitMono.mk'
    ⟨b ≫ inv (a ≫ b), by rw [← Category.assoc, IsIso.hom_inv_id]⟩
  have : IsSplitEpi a := IsSplitEpi.mk'
    ⟨inv (b ≫ a) ≫ b, by rw [Category.assoc, IsIso.inv_hom_id]⟩
  exact isIso_of_epi_of_isSplitMono a

variable {Y : Scheme.{u}}

/-- Blueprint `lem-weil-scalar-extension-well-defined`: Well-definedness of scalar extension.

Let `E ⊆ L` be finite extensions of `ℚ_ℓ` inside `ℚ̄_ℓ`. If two integral objects
`K₁, K₂ ∈ D_comp(Y_ét, 𝒪_E)` become isomorphic in the rationalization `D_comp(Y_ét, E)`, then
their derived base changes `K₁ ⊗ᴸ_{𝒪_E} 𝒪_L` and `K₂ ⊗ᴸ_{𝒪_E} 𝒪_L` (objects of
`D_comp(Y_ét, 𝒪_L)` given with the universal property `IsDerivedBaseChange`) become isomorphic in
`D_comp(Y_ét, L)`. So the scalar extension `(K ⊗ᴸ_{𝒪_E} 𝒪_L) ⊗_{𝒪_L} L` of an object of
`D_comp(Y_ét, E)` does not depend on the chosen integral representative `K`.

As in the blueprint, this is the uniqueness of the extension of the `𝒪_E`-linear derived base
change to the rationalizations: an isomorphism of rationalizations is a morphism `f : K₁ ⟶ K₂`
with a morphism `g : K₂ ⟶ K₁` such that `g ∘ f` and `f ∘ g` are nonzero scalars up to torsion
(`CategoryTheory.Rationalization.exists_smul_eq_map`,
`CategoryTheory.Rationalization.map_eq_map_iff`), and the base change of morphisms is
functorial and linear along `𝒪_E ⟶ 𝒪_L` (`AlgebraicGeometry.Etale.IsDerivedBaseChange.map`). -/
theorem nonempty_iso_fromIntegral_of_isDerivedBaseChange
    {K₁ K₂ : DerivedCategoryDerivedCompleteIntegral Y.smallEtaleTopology l E}
    {K₁' K₂' : DerivedCategoryDerivedCompleteIntegral Y.smallEtaleTopology l L}
    {η₁ : K₁.obj ⟶ (derivedRestrictScalars (PadicAlgCl.integersShrinkMap l E L) Y).obj K₁'.obj}
    {η₂ : K₂.obj ⟶ (derivedRestrictScalars (PadicAlgCl.integersShrinkMap l E L) Y).obj K₂'.obj}
    (h₁ : IsDerivedBaseChange η₁) (h₂ : IsDerivedBaseChange η₂)
    (e : (DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj K₁ ≅
      (DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj K₂) :
    Nonempty ((DerivedCategoryDerivedCompleteRational.fromIntegral _ l L).obj K₁' ≅
      (DerivedCategoryDerivedCompleteRational.fromIntegral _ l L).obj K₂') := by
  let φ := PadicAlgCl.integersShrinkMap.{w, u} l E L
  let QE := DerivedCategoryDerivedCompleteRational.fromIntegral Y.smallEtaleTopology l E
  let QL := DerivedCategoryDerivedCompleteRational.fromIntegral Y.smallEtaleTopology l L
  obtain ⟨m₁, hm₁, f, hf⟩ := Rationalization.exists_smul_eq_map e.hom
  obtain ⟨m₂, hm₂, g, hg⟩ := Rationalization.exists_smul_eq_map e.inv
  -- the base changes of `f` and `g`
  let f' : K₁' ⟶ K₂' := ObjectProperty.homMk (h₁.map η₂ f.hom)
  let g' : K₂' ⟶ K₁' := ObjectProperty.homMk (h₂.map η₁ g.hom)
  -- `g ∘ f` and `f ∘ g` are scalars up to torsion
  have key : ∀ {P₁ P₂ : DerivedCategoryDerivedCompleteIntegral Y.smallEtaleTopology l E}
      {P₁' P₂' : DerivedCategoryDerivedCompleteIntegral Y.smallEtaleTopology l L}
      {θ₁ : P₁.obj ⟶ (derivedRestrictScalars φ Y).obj P₁'.obj}
      {θ₂ : P₂.obj ⟶ (derivedRestrictScalars φ Y).obj P₂'.obj}
      (k₁ : IsDerivedBaseChange θ₁) (k₂ : IsDerivedBaseChange θ₂) (a : P₁ ⟶ P₂) (b : P₂ ⟶ P₁)
      (c : Shrink.{u + 1} (PadicAlgCl.integers l E)) (hc : c ∈ nonZeroDivisors _)
      (hab : QE.map (a ≫ b) = c • 𝟙 _),
      QL.map (ObjectProperty.homMk (k₁.map θ₂ a.hom) ≫ ObjectProperty.homMk (k₂.map θ₁ b.hom)) =
        φ c • 𝟙 _ := by
    intro P₁ P₂ P₁' P₂' θ₁ θ₂ k₁ k₂ a b c hc hab
    have hab' : QE.map (a ≫ b) = QE.map (c • 𝟙 _) := by
      rw [hab, Functor.map_smul, CategoryTheory.Functor.map_id]
    obtain ⟨m, hm, hm'⟩ := (Rationalization.map_eq_map_iff _ _).1 hab'
    have hm'' : m • (a.hom ≫ b.hom) = (m * c) • 𝟙 P₁.obj := by
      have := congrArg (fun t ↦ t.hom) hm'
      change m • (a.hom ≫ b.hom) = m • c • 𝟙 P₁.obj at this
      rw [this, smul_smul]
    have hbc : φ m • (k₁.map θ₂ a.hom ≫ k₂.map θ₁ b.hom) = φ (m * c) • 𝟙 P₁'.obj := by
      rw [← IsDerivedBaseChange.map_comp, ← IsDerivedBaseChange.map_smul, hm'',
        IsDerivedBaseChange.map_smul, IsDerivedBaseChange.map_id]
    have hφm : φ m ∈ nonZeroDivisors _ :=
      PadicAlgCl.integersShrinkMap_mem_nonZeroDivisors l E L hm
    refine Rationalization.smul_left_injective hφm ?_
    dsimp only
    have : φ m • (ObjectProperty.homMk (k₁.map θ₂ a.hom) ≫
        ObjectProperty.homMk (k₂.map θ₁ b.hom) : P₁' ⟶ P₁') = φ (m * c) • 𝟙 P₁' :=
      ObjectProperty.hom_ext _ (by
        change φ m • (k₁.map θ₂ a.hom ≫ k₂.map θ₁ b.hom) = φ (m * c) • 𝟙 P₁'.obj
        exact hbc)
    rw [← Functor.map_smul, this, Functor.map_smul, CategoryTheory.Functor.map_id, map_mul,
      mul_smul]
  have hfg : QE.map (f ≫ g) = (m₁ * m₂) • 𝟙 _ := by
    rw [Functor.map_comp, ← hf, ← hg, Linear.smul_comp, Linear.comp_smul, Iso.hom_inv_id,
      mul_smul]
  have hgf : QE.map (g ≫ f) = (m₂ * m₁) • 𝟙 _ := by
    rw [Functor.map_comp, ← hf, ← hg, Linear.smul_comp, Linear.comp_smul, Iso.inv_hom_id,
      mul_smul]
  have h₁₂ := key h₁ h₂ f g _ (Submonoid.mul_mem _ hm₁ hm₂) hfg
  have h₂₁ := key h₂ h₁ g f _ (Submonoid.mul_mem _ hm₂ hm₁) hgf
  have hφ₁ := Rationalization.isIso_smul_id
    (PadicAlgCl.integersShrinkMap_mem_nonZeroDivisors l E L (Submonoid.mul_mem _ hm₁ hm₂))
    (QL.obj K₁')
  have hφ₂ := Rationalization.isIso_smul_id
    (PadicAlgCl.integersShrinkMap_mem_nonZeroDivisors l E L (Submonoid.mul_mem _ hm₂ hm₁))
    (QL.obj K₂')
  have : IsIso (QL.map f') := by
    refine isIso_of_isIso_comp_of_isIso_comp _ (QL.map g') ?_ ?_
    · rw [← Functor.map_comp, h₁₂]
      exact hφ₁
    · rw [← Functor.map_comp, h₂₁]
      exact hφ₂
  exact ⟨asIso (QL.map f')⟩

end Rational

end Etale

end AlgebraicGeometry
