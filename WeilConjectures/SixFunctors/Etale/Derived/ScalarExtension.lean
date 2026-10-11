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
- `AlgebraicGeometry.Etale.isTriangulated_derivedCompleteRationalScalarExtension`
  (`lem-weil-scalar-extension-exact-triangulated`): the scalar extension
  `D_comp(Y, E) ⥤ D_comp(Y, L)` is triangulated.

## Implementation notes

The derived extension of scalars of étale sheaves is not constructed in this repository. The
scalar extension functor is therefore built from the hypotheses that every object of
`D(Y_ét, 𝒪_E)` has a derived base change and that derived base change preserves derived
completeness; these are the existence statements contained in the definition of the scalar
extension in `def-weil-rationalization-karoubi`. The derived base change functor is then the
left adjoint of restriction of scalars (`AlgebraicGeometry.Etale.derivedBaseChange`), and the
functor between rationalizations is induced along `𝒪_E ⟶ 𝒪_L`
(`CategoryTheory.Rationalization.mapOfRingHom`).
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

/-- `𝒪_L` is flat over `𝒪_E`: it is torsion-free over the principal ideal domain `𝒪_E`. -/
lemma integersShrinkMap_flat [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
    [FiniteDimensional ℚ_[l] E] : (integersShrinkMap.{w, u} l E L).Flat := by
  let := (integersShrinkMap.{w, u} l E L).toAlgebra
  change Module.Flat _ _
  have : IsPrincipalIdealRing (Shrink.{u + 1} (integers l E)) :=
    IsPrincipalIdealRing.of_surjective (shrinkRingEquiv l E).toRingHom
      (shrinkRingEquiv l E).surjective
  have : Module.IsTorsionFree (Shrink.{u + 1} (integers l E))
      (Shrink.{u + 1} (integers l L)) := ⟨fun r hr x y hxy ↦ by
    have hr0 : integersShrinkMap l E L r ≠ 0 := fun h ↦
      hr.ne_zero (integersShrinkMap_injective l E L (h.trans (map_zero _).symm))
    simp only [Algebra.smul_def] at hxy
    exact mul_left_cancel₀ hr0 hxy⟩
  infer_instance

end PadicAlgCl

namespace CategoryTheory.Rationalization

variable {R R' : Type*} [CommRing R] [CommRing R'] (ψ : R →+* R') {M : Submonoid R}
  {M' : Submonoid R'} (hM : M ≤ M'.comap ψ)
  {C : Type*} [Category C] [Preadditive C] [Linear R C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor C n).Linear R]
  [Pretriangulated C] [IsTriangulated C]
  {D : Type*} [Category D] [Preadditive D] [Linear R' D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [∀ n : ℤ, (shiftFunctor D n).Linear R']
  [Pretriangulated D] [IsTriangulated D]
  (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
  (hF : ∀ (r : R) {X Y : C} (f : X ⟶ Y), F.map (r • f) = ψ r • F.map f)

omit [∀ n : ℤ, (shiftFunctor C n).Linear R] [IsTriangulated C]
  [∀ n : ℤ, (shiftFunctor D n).Linear R'] [IsTriangulated D] in
include hM hF in
/-- A triangulated functor which is linear along a ring morphism `ψ : R ⟶ R'` carrying `M` into
`M'` preserves the morphisms with torsion mapping cone. -/
lemma W_map_of_ringHom {X Y : C} {s : X ⟶ Y} (hs : W M C s) : W M' D (F.map s) := by
  obtain ⟨Z, g, h, hT, m, hm, hZ⟩ := hs
  exact ObjectProperty.trW.mk _ (F.map_distinguished _ hT)
    ⟨ψ m, hM hm, by
      change ψ m • 𝟙 (F.obj Z) = 0
      rw [← F.map_id, ← hF, hZ, F.map_zero]⟩

/-- The functor `Rationalization M C ⥤ Rationalization M' D` induced by a triangulated functor
which is linear along a ring morphism `ψ : R ⟶ R'` carrying `M` into `M'`. -/
noncomputable def mapOfRingHom : Rationalization M C ⥤ Rationalization M' D :=
  Localization.lift (F ⋙ Q M' D)
    (fun _ _ _ hs ↦ Localization.inverts (Q M' D) (W M' D) _ (W_map_of_ringHom ψ hM F hF hs))
    (Q M C)

noncomputable instance : Localization.Lifting (Q M C) (W M C) (F ⋙ Q M' D)
    (mapOfRingHom ψ hM F hF) :=
  ⟨Localization.fac _ _ _⟩

noncomputable instance : (mapOfRingHom ψ hM F hF).CommShift ℤ :=
  Functor.commShiftOfLocalization (Q M C) (W M C) ℤ (F ⋙ Q M' D) (mapOfRingHom ψ hM F hF)

/-- The functor induced on rationalizations by a triangulated functor linear along a ring
morphism is triangulated: a distinguished triangle of the rationalization is isomorphic to the
image of a distinguished triangle of `C`. -/
instance isTriangulated_mapOfRingHom : (mapOfRingHom ψ hM F hF).IsTriangulated := by
  have := Localization.essSurj_mapArrow (Q M C) (W M C)
  refine ⟨fun T hT ↦ ?_⟩
  obtain ⟨T₀, e, hT₀⟩ := (Functor.distTriang_iff (Q M C) T).1 hT
  let G := mapOfRingHom ψ hM F hF
  exact Pretriangulated.isomorphic_distinguished _ ((F ⋙ Q M' D).map_distinguished _ hT₀) _
    (G.mapTriangle.mapIso e ≪≫ (Functor.mapTriangleCompIso (Q M C) G).symm.app T₀ ≪≫
      (Functor.mapTriangleIso (Localization.Lifting.iso (Q M C) (W M C) (F ⋙ Q M' D) G)).app T₀)

end CategoryTheory.Rationalization

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

section ExtendScalars

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ') (X : Scheme.{u})

/- Mathlib's instance is stated for `extendScalars.{u₁, u₂, max u₂ w}`, and unifying
`u + 1 =?= max (u + 1) ?w` gets stuck, so instance search does not find it here. -/
instance : (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ).IsLeftAdjoint :=
  (ModuleCat.extendRestrictScalarsAdj.{u + 1} φ).isLeftAdjoint

instance : (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ).IsRightAdjoint :=
  (ModuleCat.extendRestrictScalarsAdj.{u + 1} φ).isRightAdjoint

/-- Extension of scalars along `φ : Λ ⟶ Λ'`, from étale sheaves of `Λ`-modules to étale sheaves
of `Λ'`-modules: objectwise extension of scalars followed by sheafification. -/
noncomputable abbrev sheafExtendScalars :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ') :=
  Sheaf.composeAndSheafify X.smallEtaleTopology (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)

/-- Extension of scalars of étale sheaves is left adjoint to restriction of scalars. -/
noncomputable def sheafExtendRestrictScalarsAdj :
    sheafExtendScalars φ X ⊣ Sheaf.restrictScalars X.smallEtaleTopology φ :=
  Sheaf.adjunction _ (ModuleCat.extendRestrictScalarsAdj.{u + 1} φ)

instance : (sheafExtendScalars φ X).Additive :=
  (sheafExtendRestrictScalarsAdj φ X).left_adjoint_additive

instance : PreservesFiniteColimits (sheafExtendScalars φ X) :=
  have := (sheafExtendRestrictScalarsAdj φ X).leftAdjoint_preservesColimits
  inferInstance

/-- Extension of scalars of étale sheaves along a flat ring morphism is left exact. -/
lemma preservesFiniteLimits_sheafExtendScalars (hφ : φ.Flat) :
    PreservesFiniteLimits (sheafExtendScalars φ X) := by
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hφ
  have : PreservesFiniteLimits ((Functor.whiskeringRight X.Etaleᵒᵖ (ModuleCat.{u + 1} Λ)
      (ModuleCat.{u + 1} Λ')).obj (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  unfold sheafExtendScalars Sheaf.composeAndSheafify
  infer_instance

/-- Along a flat ring morphism, every object of `D(X_ét, Λ)` has a derived base change: the unit
of the adjunction between the levelwise extension and restriction of scalars, which are exact. -/
theorem exists_isDerivedBaseChange (hφ : φ.Flat) (K : 𝐃(X, Λ)) :
    ∃ (K' : 𝐃(X, Λ')) (η : K ⟶ (derivedRestrictScalars φ X).obj K'), IsDerivedBaseChange η := by
  have := preservesFiniteLimits_sheafExtendScalars φ X hφ
  have : PreservesFiniteLimits (Sheaf.restrictScalars X.smallEtaleTopology φ) :=
    have := (sheafExtendRestrictScalarsAdj φ X).rightAdjoint_preservesLimits
    inferInstance
  have : PreservesFiniteColimits (Sheaf.restrictScalars X.smallEtaleTopology φ) :=
    have := (Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).leftAdjoint_preservesColimits
    inferInstance
  let : CatCommSq ((sheafExtendScalars φ X).mapHomologicalComplex (ComplexShape.up ℤ))
      _root_.DerivedCategory.Q _root_.DerivedCategory.Q
      (sheafExtendScalars φ X).mapDerivedCategory :=
    ⟨(sheafExtendScalars φ X).mapDerivedCategoryFactors.symm⟩
  let : CatCommSq ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapHomologicalComplex
      (ComplexShape.up ℤ)) _root_.DerivedCategory.Q _root_.DerivedCategory.Q
      (derivedRestrictScalars φ X) :=
    ⟨(Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryFactors.symm⟩
  let adj : (sheafExtendScalars φ X).mapDerivedCategory ⊣ derivedRestrictScalars φ X :=
    ((sheafExtendRestrictScalarsAdj φ X).mapHomologicalComplex (ComplexShape.up ℤ)).localization
      _root_.DerivedCategory.Q (HomologicalComplex.quasiIso _ _) _root_.DerivedCategory.Q
      (HomologicalComplex.quasiIso _ _) _ _
  refine ⟨_, adj.unit.app K, fun N ↦ ?_⟩
  have e : (fun g ↦ adj.unit.app K ≫ (derivedRestrictScalars φ X).map g) = adj.homEquiv K N :=
    funext fun g ↦ (adj.homEquiv_unit K N g).symm
  rw [e]
  exact (adj.homEquiv K N).bijective

end ExtendScalars

section BaseChangeFunctor

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ') (X : Scheme.{u})
  (h : ∀ K : 𝐃(X, Λ), ∃ (K' : 𝐃(X, Λ')) (η : K ⟶ (derivedRestrictScalars φ X).obj K'),
    IsDerivedBaseChange η)

/-- The universal property of the derived base changes, as a family of bijections. -/
noncomputable def derivedBaseChangeHomEquiv (K : 𝐃(X, Λ)) (N : 𝐃(X, Λ')) :
    ((h K).choose ⟶ N) ≃ (K ⟶ (derivedRestrictScalars φ X).obj N) :=
  Equiv.ofBijective _ ((h K).choose_spec.choose_spec N)

/-- If every object of `D(X_ét, Λ)` admits a derived base change along `φ : Λ ⟶ Λ'`, the
derived base change `K ↦ K ⊗ᴸ_Λ Λ'` as a functor `D(X_ét, Λ) ⥤ D(X_ét, Λ')`, left adjoint to
restriction of scalars. -/
noncomputable def derivedBaseChange : 𝐃(X, Λ) ⥤ 𝐃(X, Λ') :=
  Adjunction.leftAdjointOfEquiv (derivedBaseChangeHomEquiv φ X h) fun K N N' g g' ↦ by
    simp only [derivedBaseChangeHomEquiv, Equiv.ofBijective_apply, Functor.map_comp,
      Category.assoc]

/-- The derived base change is left adjoint to restriction of scalars. -/
noncomputable def derivedBaseChangeAdjunction :
    derivedBaseChange φ X h ⊣ derivedRestrictScalars φ X :=
  Adjunction.adjunctionOfEquivLeft _ _

noncomputable instance : (derivedBaseChange φ X h).CommShift ℤ :=
  (derivedBaseChangeAdjunction φ X h).leftAdjointCommShift ℤ

/-- The derived base change is a triangulated functor, being left adjoint to the triangulated
restriction of scalars. -/
instance : (derivedBaseChange φ X h).IsTriangulated :=
  have := (derivedBaseChangeAdjunction φ X h).commShift_of_rightAdjoint ℤ
  (derivedBaseChangeAdjunction φ X h).isTriangulated_leftAdjoint

/-- The derived base change is linear along `φ`. -/
lemma derivedBaseChange_map_smul (r : Λ) {K₁ K₂ : 𝐃(X, Λ)} (f : K₁ ⟶ K₂) :
    (derivedBaseChange φ X h).map (r • f) = φ r • (derivedBaseChange φ X h).map f := by
  let adj := derivedBaseChangeAdjunction φ X h
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, derivedRestrictScalars_map_smul,
    Linear.comp_smul, adj.unit_naturality, adj.unit_naturality, Linear.smul_comp]

end BaseChangeFunctor

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

omit [Algebra ℚ_[l] L] [IsScalarTower ℚ_[l] L (PadicAlgCl l)] [FiniteDimensional ℚ_[l] L] in
variable (Y) in
/-- Every object of `D(Y_ét, 𝒪_E)` has a derived base change along `𝒪_E ⟶ 𝒪_L`, the latter being
flat (`PadicAlgCl.integersShrinkMap_flat`). -/
theorem exists_isDerivedBaseChange_integers
    (K : 𝐃(Y, Shrink.{u + 1} (PadicAlgCl.integers l E))) :
    ∃ (K' : 𝐃(Y, Shrink.{u + 1} (PadicAlgCl.integers l L)))
      (η : K ⟶ (derivedRestrictScalars (PadicAlgCl.integersShrinkMap l E L) Y).obj K'),
      IsDerivedBaseChange η :=
  exists_isDerivedBaseChange _ Y (PadicAlgCl.integersShrinkMap_flat l E L) K

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


variable {l E L} in
/-- `derivedCompleteIntegralScalarExtension`, as a functor between the full subcategories of
derived complete objects. -/
noncomputable abbrev derivedCompleteIntegralScalarExtensionAux
    (h : ∀ K : 𝐃(Y, Shrink.{u + 1} (PadicAlgCl.integers l E)),
      ∃ (K' : 𝐃(Y, Shrink.{u + 1} (PadicAlgCl.integers l L)))
        (η : K ⟶ (derivedRestrictScalars (PadicAlgCl.integersShrinkMap l E L) Y).obj K'),
        IsDerivedBaseChange η)
    (hc : ∀ K, _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E K →
      _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l L
        ((derivedBaseChange (PadicAlgCl.integersShrinkMap l E L) Y h).obj K)) :
    (_root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E).FullSubcategory ⥤
      (_root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l L).FullSubcategory :=
  (_root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l L).lift
    ((_root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E).ι ⋙
      derivedBaseChange (PadicAlgCl.integersShrinkMap l E L) Y h) fun K ↦ hc _ K.property

variable {l E L} in
/-- The derived base change `D_comp(Y_ét, 𝒪_E) ⥤ D_comp(Y_ét, 𝒪_L)` between the integral stages,
given the existence of derived base changes (`h`) and their derived completeness (`hc`). -/
noncomputable def derivedCompleteIntegralScalarExtension
    (h : ∀ K : 𝐃(Y, Shrink.{u + 1} (PadicAlgCl.integers l E)),
      ∃ (K' : 𝐃(Y, Shrink.{u + 1} (PadicAlgCl.integers l L)))
        (η : K ⟶ (derivedRestrictScalars (PadicAlgCl.integersShrinkMap l E L) Y).obj K'),
        IsDerivedBaseChange η)
    (hc : ∀ K, _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E K →
      _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l L
        ((derivedBaseChange (PadicAlgCl.integersShrinkMap l E L) Y h).obj K)) :
    DerivedCategoryDerivedCompleteIntegral Y.smallEtaleTopology l E ⥤
      DerivedCategoryDerivedCompleteIntegral Y.smallEtaleTopology l L :=
  derivedCompleteIntegralScalarExtensionAux h hc

section

variable {l E L}
  {h : ∀ K : 𝐃(Y, Shrink.{u + 1} (PadicAlgCl.integers l E)),
      ∃ (K' : 𝐃(Y, Shrink.{u + 1} (PadicAlgCl.integers l L)))
        (η : K ⟶ (derivedRestrictScalars (PadicAlgCl.integersShrinkMap l E L) Y).obj K'),
        IsDerivedBaseChange η}
  {hc : ∀ K, _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E K →
      _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l L
        ((derivedBaseChange (PadicAlgCl.integersShrinkMap l E L) Y h).obj K)}

noncomputable instance : (derivedCompleteIntegralScalarExtension h hc).CommShift ℤ :=
  inferInstanceAs ((derivedCompleteIntegralScalarExtensionAux h hc).CommShift ℤ)

instance : (derivedCompleteIntegralScalarExtension h hc).IsTriangulated :=
  inferInstanceAs (derivedCompleteIntegralScalarExtensionAux h hc).IsTriangulated

omit [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]
  [Algebra ℚ_[l] L] [IsScalarTower ℚ_[l] L (PadicAlgCl l)] [FiniteDimensional ℚ_[l] L] in
lemma derivedCompleteIntegralScalarExtension_map_smul
    (r : Shrink.{u + 1} (PadicAlgCl.integers l E)) {K₁ K₂} (f : K₁ ⟶ K₂) :
    (derivedCompleteIntegralScalarExtension h hc).map (r • f) =
      PadicAlgCl.integersShrinkMap l E L r • (derivedCompleteIntegralScalarExtension h hc).map f :=
  ObjectProperty.hom_ext _ (derivedBaseChange_map_smul _ Y h r f.hom)

omit [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]
  [Algebra ℚ_[l] L] [IsScalarTower ℚ_[l] L (PadicAlgCl l)] [FiniteDimensional ℚ_[l] L] in
lemma integersShrinkMap_nonZeroDivisors_le :
    nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E)) ≤
      (nonZeroDivisors _).comap (PadicAlgCl.integersShrinkMap l E L) := fun _ hx ↦
  PadicAlgCl.integersShrinkMap_mem_nonZeroDivisors l E L hx

variable (h hc) in
/-- The scalar extension `- ⊗_E L : D_comp(Y_ét, E) ⥤ D_comp(Y_ét, L)` of blueprint
`def-weil-rationalization-karoubi`: the functor induced on the rationalizations by the derived
base change, given its existence (`h`) and its preservation of derived completeness (`hc`). -/
noncomputable abbrev derivedCompleteRationalScalarExtension :
    DerivedCategoryDerivedCompleteRational Y.smallEtaleTopology l E ⥤
      DerivedCategoryDerivedCompleteRational Y.smallEtaleTopology l L :=
  Rationalization.mapOfRingHom (PadicAlgCl.integersShrinkMap l E L)
    integersShrinkMap_nonZeroDivisors_le (derivedCompleteIntegralScalarExtension h hc)
    derivedCompleteIntegralScalarExtension_map_smul

/-- Given that the derived base change `K ↦ K ⊗ᴸ_{𝒪_E} 𝒪_L` exists on `D(Y_ét, 𝒪_E)` (`h`) and
carries derived complete objects to derived complete objects (`hc`), the scalar extension `- ⊗_E L : D_comp(Y_ét, E) ⥤
D_comp(Y_ét, L)`, induced on the rationalizations by the derived base change, is a triangulated
functor: it commutes with shifts and carries distinguished triangles to distinguished triangles.

As in the blueprint, it is the composite of the derived base change, which is triangulated as the
left adjoint of the triangulated restriction of scalars, and of the rationalization; the induced
functor on the rationalizations is triangulated
(`CategoryTheory.Rationalization.isTriangulated_mapOfRingHom`). By
`AlgebraicGeometry.Etale.nonempty_iso_fromIntegral_of_isDerivedBaseChange` it does not depend on
the integral representatives. -/
instance isTriangulated_derivedCompleteRationalScalarExtension :
    (derivedCompleteRationalScalarExtension h hc).IsTriangulated :=
  inferInstance

/-- The scalar extension of the rationalization of an integral object `K` is the rationalization
of its derived base change. -/
noncomputable def derivedCompleteRationalScalarExtensionFromIntegralIso
    (K : DerivedCategoryDerivedCompleteIntegral Y.smallEtaleTopology l E) :
    (derivedCompleteRationalScalarExtension h hc).obj
        ((DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj K) ≅
      (DerivedCategoryDerivedCompleteRational.fromIntegral _ l L).obj
        ((derivedCompleteIntegralScalarExtension h hc).obj K) :=
  (Localization.Lifting.iso (Rationalization.Q _ _)
    (Rationalization.W (nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E))) _)
    (derivedCompleteIntegralScalarExtension h hc ⋙ Rationalization.Q _ _)
    (derivedCompleteRationalScalarExtension h hc)).app K

end

variable (Y) in
/-- Derived base change along `𝒪_E ⟶ 𝒪_L` carries derived complete objects to derived complete
objects. This is the completeness part of the definition of the scalar extension
(`def-weil-rationalization-karoubi`); see the implementation notes of this file for its status. -/
theorem derivedCompleteIntegral_derivedBaseChange_integers
    (K : 𝐃(Y, Shrink.{u + 1} (PadicAlgCl.integers l E)))
    (hK : _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E K) :
    _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l L
      ((derivedBaseChange (PadicAlgCl.integersShrinkMap l E L) Y
        (exists_isDerivedBaseChange_integers l E L Y)).obj K) :=
  sorry

variable (Y) in
/-- The scalar extension `- ⊗_E L : D_comp(Y_ét, E) ⥤ D_comp(Y_ét, L)` of blueprint
`def-weil-rationalization-karoubi`: on an integral representative `K`, the rationalization of
the derived base change `K ⊗ᴸ_{𝒪_E} 𝒪_L`. -/
noncomputable abbrev rationalScalarExtension :
    DerivedCategoryDerivedCompleteRational Y.smallEtaleTopology l E ⥤
      DerivedCategoryDerivedCompleteRational Y.smallEtaleTopology l L :=
  derivedCompleteRationalScalarExtension (exists_isDerivedBaseChange_integers l E L Y)
    (derivedCompleteIntegral_derivedBaseChange_integers l E L Y)

/-- Blueprint `lem-weil-scalar-extension-exact-triangulated`: Scalar extension is an exact
triangulated functor.

Let `E ⊆ L` be finite extensions of `ℚ_ℓ` inside `ℚ̄_ℓ`. The scalar extension
`- ⊗_E L : D_comp(Y_ét, E) ⥤ D_comp(Y_ét, L)`
(`AlgebraicGeometry.Etale.rationalScalarExtension`) is a triangulated functor: it commutes with shifts and carries distinguished triangles to
distinguished triangles. As in the blueprint, it is the composite of the derived base change,
triangulated as the left adjoint of the triangulated restriction of scalars, and of the
rationalization (`CategoryTheory.Rationalization.isTriangulated_mapOfRingHom`); by
`AlgebraicGeometry.Etale.nonempty_iso_fromIntegral_of_isDerivedBaseChange` it does not depend on
the integral representatives. -/
instance isTriangulated_rationalScalarExtension :
    (rationalScalarExtension l E L Y).IsTriangulated :=
  inferInstance

end Rational

end Etale

end AlgebraicGeometry
