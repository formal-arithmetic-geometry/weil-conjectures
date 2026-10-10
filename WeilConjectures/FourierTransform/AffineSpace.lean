/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.FourierTransform.Defs
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace

/-!

# The Fourier–Deligne transform on affine space

The Fourier–Deligne transform of `WeilConjectures.FourierTransform.Defs` is stated for an
arbitrary pair of `S`-schemes with a pairing. Its main case is affine `n`-space `𝔸(n; S)`
paired with itself by the standard pairing `⟨x, ξ⟩ = ∑ᵢ xᵢ ξᵢ` and shifted by the relative
dimension `r = #n`; this file records that datum and the computation of the transform of
the two simplest complexes, the constant sheaf and the skyscraper at the origin.

The affine-space data themselves — the standard pairing, the zero section and the
reflection `x ↦ -x` — are in
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace`; they have nothing to do with étale
sheaves.

## Main definitions

- `AlgebraicGeometry.Etale.affineFourierTransform`: the Fourier–Deligne transform of
  `𝔸(n; S)` with the standard pairing.
- `AlgebraicGeometry.Etale.skyscraperZero`: the skyscraper `δ₀` at the origin.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_unit` and
  `AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_skyscraperZero`: the transform
  exchanges the constant sheaf and the skyscraper at the origin.
- `AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_inv`: the transform for the
  inverse character is the transform of the reflected input.

## Coefficients

Coefficient hypotheses follow the classes in `WeilConjectures.FourierTransform.Defs`.

## Implementation notes

The statements only assert that an isomorphism *exists*. Later uses will need specific,
coherent isomorphisms, which `Classical.choice` cannot provide.

The transform of the constant sheaf is computed from the stalk formula
(`AlgebraicGeometry.Etale.nonempty_iso_fourierTransform_geometricStalk`) and
`H_c^*(𝔸^r, Λ) ≅ Λ(-r)[-2r]`, which needs `Λ` finite with exponent invertible on `S`. The
transform of the skyscraper is compact-support base change of `Rp₂,!` along the zero section.
The comparison of the transforms for `ψ` and `ψ⁻¹` is base change of `Rp₂,!` along the
isomorphism `ι × 1`, over the identity of the second factor
(`AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_of_isIso`).

TODO: upgrade these back to `Iso` constructions once they can be built.

## Blueprint

The `sk-*` labels quoted below are block names of the *sketch* blueprint, a separate
repository; they are not labels of `blueprint/src` and so are not checked by the build.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open AlgebraicGeometry.AffineSpace

section Automorphism

variable (Λ : Type (u + 1)) [CommRing Λ]
variable {P V V' : Scheme.{u}} (q₁ : P ⟶ V) (q₂ : P ⟶ V') [HasCompactification q₂]
  [QuasiCompact q₂]

/-- Compact-support base change along an automorphism `σ` over `V'`. -/
private lemma kt_bc [Finite Λ] (σ : P ⟶ P) [IsIso σ] (h₂ : σ ≫ q₂ = q₂) :
    Nonempty (R(q₂)_![ModuleCat.{u + 1} Λ] ≅
      L((σ)^*[ModuleCat.{u + 1} Λ]) ⋙ R(q₂)_![ModuleCat.{u + 1} Λ]) := by
  let A := ModuleCat.{u + 1} Λ
  have sq : IsPullback σ q₂ q₂ (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨h₂.trans (Category.comp_id _).symm⟩
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  let idIso : L((𝟙 V')^*[A]) ≅ 𝟭 _ :=
    Functor.leftDerivedFunctorNatIso _ (Etale.upperStarId A _) ≪≫
      (𝟭 _).leftDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryIdIso _
  exact ⟨(Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ idIso.symm ≪≫
      asIso (rightDerivedLowerShriekBaseChangeMap Λ sq)⟩

/-- `D(q₁^*) ⋙ Lσ^* ≅ D(τ^*) ⋙ D(q₁^*)` for `σ ≫ q₁ = q₁ ≫ τ`. -/
private lemma kt_pc (σ : P ⟶ P) (τ : V ⟶ V) (h₁ : σ ≫ q₁ = q₁ ≫ τ) :
    Nonempty (D((q₁)^*[ModuleCat.{u + 1} Λ]) ⋙ L((σ)^*[ModuleCat.{u + 1} Λ]) ≅
      D((τ)^*[ModuleCat.{u + 1} Λ]) ⋙ D((q₁)^*[ModuleCat.{u + 1} Λ])) := by
  let A := ModuleCat.{u + 1} Λ
  let ι {X Y : Scheme.{u}} (f : X ⟶ Y) := leftDerivedUpperStarIsoMapDerivedCategory A f
  exact ⟨Functor.isoWhiskerRight (ι q₁).symm _ ≪≫
      (leftDerivedUpperStarComp A σ q₁ (q₁ ≫ τ) h₁.symm).symm ≪≫
      leftDerivedUpperStarComp A q₁ τ ≪≫
      Functor.isoWhiskerRight (ι _) _ ≪≫ Functor.isoWhiskerLeft _ (ι _)⟩

/-- `Lσ^*` commutes with tensoring by `𝒦`. -/
private lemma kt_tens (σ : P ⟶ P)
    (𝒦 : DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty (derivedTensorRight (ModuleCat.{u + 1} Λ) P 𝒦 ⋙ L((σ)^*[ModuleCat.{u + 1} Λ]) ≅
      L((σ)^*[ModuleCat.{u + 1} Λ]) ⋙ derivedTensorRight (ModuleCat.{u + 1} Λ) P
        (L((σ)^*[ModuleCat.{u + 1} Λ]).obj 𝒦)) :=
  ⟨derivedTensorRightCompLeftDerivedUpperStarIso _ σ 𝒦⟩

/-- A kernel transform `K ↦ Rq₂,!(q₁^* K ⊗ᴸ 𝒦)[a]` is unchanged by an automorphism `σ` of
`P` over `V'`: if `σ` lies over the endomorphism `τ` of `V` and `Lσ^* 𝒦 ≅ 𝒦'`, then
`Rq₂,!(q₁^* K ⊗ᴸ 𝒦)[a] ≅ Rq₂,!(q₁^* τ^* K ⊗ᴸ 𝒦')[a]`, naturally in `K`. This is
compact-support base change along the cartesian square with sides `σ`, `q₂`, `q₂` and `𝟙`,
together with the monoidality of `Lσ^*`. -/
theorem nonempty_iso_kernelTransform_of_isIso [Finite Λ] (σ : P ⟶ P) [IsIso σ] (τ : V ⟶ V)
    (h₁ : σ ≫ q₁ = q₁ ≫ τ) (h₂ : σ ≫ q₂ = q₂)
    (𝒦 𝒦' : DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (e : L((σ)^*[ModuleCat.{u + 1} Λ]).obj 𝒦 ≅ 𝒦') (a : ℤ) :
    Nonempty (D((q₁)^*[ModuleCat.{u + 1} Λ]) ⋙ derivedTensorRight _ P 𝒦 ⋙
        R(q₂)_![ModuleCat.{u + 1} Λ] ⋙ shiftFunctor _ a ≅
      D((τ)^*[ModuleCat.{u + 1} Λ]) ⋙ D((q₁)^*[ModuleCat.{u + 1} Λ]) ⋙
        derivedTensorRight _ P 𝒦' ⋙ R(q₂)_![ModuleCat.{u + 1} Λ] ⋙ shiftFunctor _ a) := by
  obtain ⟨bc⟩ := kt_bc Λ q₂ σ h₂
  obtain ⟨pc⟩ := kt_pc Λ q₁ σ τ h₁
  obtain ⟨tens⟩ := kt_tens Λ σ 𝒦
  let X := R(q₂)_![ModuleCat.{u + 1} Λ] ⋙
    shiftFunctor (DerivedCategory (Sheaf V'.smallEtaleTopology (ModuleCat.{u + 1} Λ))) a
  -- every reassociation is explicit, the kernel being slow to unfold derived functors
  exact ⟨Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      (Functor.isoWhiskerRight bc (shiftFunctor _ a) ≪≫ Functor.associator _ _ _)) ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight tens X ≪≫ Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight pc _ ≪≫
      Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      (Functor.isoWhiskerRight ((derivedTensor _ P).flip.mapIso e) X))⟩

/-- If `R ⋙ T ≅ (- ⊗ N) ⋙ R` and `N ≅ U` with `U ⊗ U ≅ U`, then `T (R U) ≅ R U`. This is stated
for abstract functors so that the kernel never unfolds the concrete derived functors it is
applied to. -/
private lemma nonempty_iso_of_iso_comp_flip {C D : Type*} [Category C] [Category D]
    (R : C ⥤ D) (T : D ⥤ D) (B : C ⥤ C ⥤ C) {N U : C} (pf : R ⋙ T ≅ B.flip.obj N ⋙ R)
    (e : N ≅ U) (l : (B.obj U).obj U ≅ U) : Nonempty (T.obj (R.obj U) ≅ R.obj U) :=
  ⟨pf.app U ≪≫ R.mapIso ((B.obj U).mapIso e ≪≫ l)⟩

/-- `(F ⋙ G ⋙ H ⋙ K).obj X = K.obj (H.obj (G.obj (F.obj X)))`, stated for abstract functors so
that the kernel never unfolds the concrete derived functors it is applied to. -/
private lemma _root_.CategoryTheory.Functor.comp_obj_comp_obj_comp_obj_eq
    {C₁ C₂ C₃ C₄ C₅ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    [Category C₅] (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) (H : C₃ ⥤ C₄) (K : C₄ ⥤ C₅) (X : C₁) :
    (F ⋙ G ⋙ H ⋙ K).obj X = K.obj (H.obj (G.obj (F.obj X))) :=
  rfl

/-- `q₁^* Rz_* Λ ≅ Rz'_! Λ`, for `z'` the base change of the proper `z` along `q₁`. -/
private lemma kt_sky₁ [Finite Λ] {T : Scheme.{u}} (z : T ⟶ V) [IsProper z] (z' : V' ⟶ P)
    (g : V' ⟶ T) [HasCompactification z'] [QuasiCompact z'] (sq : IsPullback g z' z q₁) :
    Nonempty ((D((q₁)^*[ModuleCat.{u + 1} Λ])).obj
        ((R((z)_*[ModuleCat.{u + 1} Λ])).obj (𝟙_ _)) ≅
      (R(z')_![ModuleCat.{u + 1} Λ]).obj (𝟙_ _)) := by
  let A := ModuleCat.{u + 1} Λ
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  obtain ⟨pz⟩ := nonempty_iso_rightDerivedLowerShriek_rightDerivedLowerStar A z
  exact ⟨(leftDerivedUpperStarIsoMapDerivedCategory A q₁).symm.app _ ≪≫
      (L((q₁)^*[A])).mapIso (pz.symm.app _) ≪≫
      (asIso (rightDerivedLowerShriekBaseChangeMap Λ sq)).app _ ≪≫
      (R(z')_![A]).mapIso (leftDerivedUpperStarUnitIso A g)⟩

/-- `Rz'_! Λ ⊗ᴸ 𝒦 ≅ Rz'_!(Λ ⊗ᴸ z'^* 𝒦) ≅ Rz'_! Λ` when `z'^* 𝒦 ≅ Λ`. -/
private lemma kt_sky₂ [Finite Λ] (z' : V' ⟶ P) [HasCompactification z']
    (𝒦 : DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (e : L((z')^*[ModuleCat.{u + 1} Λ]).obj 𝒦 ≅ 𝟙_ _) :
    Nonempty ((derivedTensorRight _ P 𝒦).obj ((R(z')_![ModuleCat.{u + 1} Λ]).obj (𝟙_ _)) ≅
      (R(z')_![ModuleCat.{u + 1} Λ]).obj (𝟙_ _)) := by
  let A := ModuleCat.{u + 1} Λ
  obtain ⟨pf⟩ := nonempty_iso_rightDerivedLowerShriek_comp_derivedTensorRight A z' 𝒦
    (fun K ↦ hasProjectionFormula_of_finite Λ _ K 𝒦)
  exact nonempty_iso_of_iso_comp_flip _ _ (derivedTensor A V') pf e (derivedTensorLeftUnitor A V' _)

omit [QuasiCompact q₂] in
/-- `Rq₂,! Rz'_! Λ ≅ Λ` for a section `z'` of `q₂`. -/
private lemma kt_sky₃ [Finite Λ] (z' : V' ⟶ P) [HasCompactification z'] (hz : z' ≫ q₂ = 𝟙 V') :
    Nonempty ((R(q₂)_![ModuleCat.{u + 1} Λ]).obj ((R(z')_![ModuleCat.{u + 1} Λ]).obj (𝟙_ _)) ≅
      𝟙_ _) := by
  let A := ModuleCat.{u + 1} Λ
  have : HasCompactification (z' ≫ q₂) := .of_eq hz.symm
  obtain ⟨pid⟩ := nonempty_iso_rightDerivedLowerShriek_rightDerivedLowerStar A (𝟙 V')
  obtain ⟨c⟩ := nonempty_iso_rightDerivedLowerShriek_comp Λ z' q₂
  have hcongr {X Y : Scheme.{u}} {f f' : X ⟶ Y} [HasCompactification f]
      [HasCompactification f'] (h : f = f') : Nonempty (R(f)_![A] ≅ R(f')_![A]) := by
    subst h
    exact ⟨Iso.refl _⟩
  obtain ⟨cc⟩ := hcongr hz
  exact ⟨(c.app _).symm ≪≫ cc.app _ ≪≫ pid.app _ ≪≫ (rightDerivedLowerStarIdIso Λ V').app _⟩

omit [QuasiCompact q₂] in
/-- The kernel transform `Rq₂,!(q₁^*(-) ⊗ᴸ 𝒦)` of a skyscraper `Rz_* Λ` along a proper
`z : T ⟶ V`: if the base change `z'` of `z` along `q₁` is a section of `q₂` and the kernel is
trivial along `z'`, then the transform of `Rz_* Λ` is `Λ`. This is `Rz_* = Rz_!`,
compact-support base change along `q₁`, the projection formula for `z'` and the composition
law `R(z' ≫ q₂)_! = R(𝟙)_!`. -/
theorem nonempty_iso_kernelTransform_obj_rightDerivedLowerStar [Finite Λ] {T : Scheme.{u}}
    (z : T ⟶ V) [IsProper z] (z' : V' ⟶ P) (g : V' ⟶ T) [HasCompactification z']
    [QuasiCompact z'] (sq : IsPullback g z' z q₁) (hz : z' ≫ q₂ = 𝟙 V')
    (𝒦 : DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (e : L((z')^*[ModuleCat.{u + 1} Λ]).obj 𝒦 ≅ 𝟙_ _) (a : ℤ) :
    Nonempty ((D((q₁)^*[ModuleCat.{u + 1} Λ]) ⋙ derivedTensorRight _ P 𝒦 ⋙
        R(q₂)_![ModuleCat.{u + 1} Λ] ⋙ shiftFunctor _ a).obj
          ((R((z)_*[ModuleCat.{u + 1} Λ])).obj (𝟙_ _)) ≅ (shiftFunctor _ a).obj (𝟙_ _)) := by
  obtain ⟨s₁⟩ := kt_sky₁ Λ q₁ z z' g sq
  obtain ⟨s₂⟩ := kt_sky₂ Λ z' 𝒦 e
  obtain ⟨s₃⟩ := kt_sky₃ Λ q₂ z' hz
  exact ⟨eqToIso (Functor.comp_obj_comp_obj_comp_obj_eq _ _ _ _ _) ≪≫ (shiftFunctor _ a).mapIso
    ((R(q₂)_![ModuleCat.{u + 1} Λ]).mapIso ((derivedTensorRight _ P 𝒦).mapIso s₁ ≪≫ s₂) ≪≫ s₃)⟩

/-- The derived pullback of a sheaf placed in degree zero is the pullback of the sheaf, placed
in degree zero. -/
lemma nonempty_iso_leftDerivedUpperStar_singleFunctor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (e : (f)^*[ModuleCat.{u + 1} Λ].obj F ≅ G) :
    Nonempty (L((f)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.singleFunctor _ 0).obj F) ≅
      (DerivedCategory.singleFunctor _ 0).obj G) :=
  ⟨(leftDerivedUpperStarIsoMapDerivedCategory _ f).app _ ≪≫
    (((f)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso e⟩

end Automorphism

section NegProd

variable (n : Type u) (S : Scheme.{u})

/-- The automorphism `ι × 1 : (x, ξ) ↦ (-x, ξ)` of `𝔸(n; S) ×_S 𝔸(n; S)`. -/
noncomputable def negProd : pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) ⟶
    pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) :=
  pullback.map _ _ _ _ (neg n S) (𝟙 _) (𝟙 S) (by simp [neg_over]) (by simp)

@[reassoc (attr := simp)]
lemma negProd_fst : negProd n S ≫ pullback.fst _ _ = pullback.fst _ _ ≫ neg n S :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma negProd_snd : negProd n S ≫ pullback.snd _ _ = pullback.snd _ _ :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

@[reassoc (attr := simp)]
lemma negProd_negProd : negProd n S ≫ negProd n S = 𝟙 _ := by
  ext <;> simp [AffineSpace.neg_comp_neg]

instance : IsIso (negProd n S) := ⟨negProd n S, negProd_negProd n S, negProd_negProd n S⟩

lemma negProd_appTop_stdPairing [Fintype n] :
    (negProd n S).appTop (stdPairing n S) = -stdPairing n S := by
  simp only [stdPairing, map_sum, map_mul, ← neg_mul, ← Finset.sum_neg_distrib]
  congr 1
  ext i
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    ← Scheme.Hom.comp_appTop, negProd_fst, negProd_snd, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, neg_appTop_coord, map_neg]

end NegProd

variable (Λ : Type (u + 1)) [CommRing Λ] {p : ℕ} [Fact p.Prime] [Invertible (p : Λ)]
variable (n : Type u) [Fintype n] (S : Scheme.{u})
variable [CharP Γ(pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S), ⊤) p]
variable [HasCompactification (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))]

/-- The Fourier–Deligne transform of affine `n`-space over `S`: the transform of
`AlgebraicGeometry.Etale.fourierTransform` for `𝔸(n; S)` paired with itself by the standard
pairing `⟨x, ξ⟩ = ∑ᵢ xᵢ ξᵢ` and shifted by the relative dimension `r = #n`. On the affine
line this is `FT_ψ(K) = Rp₂,!(p₁^* K ⊗ᴸ ℒ_{ψ(xξ)})[1]`. -/
noncomputable def affineFourierTransform (Ψ : AddChar (ZMod p) Λ) :
    DerivedCategory (Sheaf (𝔸(n; S)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf (𝔸(n; S)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  fourierTransform Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ (stdPairing n S) (Fintype.card n)

/-- The skyscraper `δ₀` at the origin of `𝔸(n; S)`: the direct image of the constant sheaf
`Λ` along the zero section. -/
noncomputable def skyscraperZero :
    DerivedCategory (Sheaf (𝔸(n; S)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (R((zeroSection n S)_*[ModuleCat.{u + 1} Λ])).obj (𝟙_ _)

/-- The Fourier–Deligne transform of the constant sheaf on `𝔸(n; S)` is the skyscraper at
the origin of the dual, Tate twisted and shifted by the relative dimension `r = #n`:

`FT_ψ(Λ) ≅ δ₀(-r)[-r]`.

On the affine line, the blueprint's case, this reads `FT_ψ(Λ) ≅ δ₀(-1)[-1]`.

The character must be **nontrivial** in the strong sense that `Ψ 1 - 1` is a unit of `Λ`:
the proof uses `H_c^*(𝔸¹, ℒ_ψ) = 0`, and the `ψ`-isotypic part of `H_c^*(𝔸¹, Λ)` is killed
by `Ψ 1 - 1`. For `Ψ = 1` the kernel is the constant sheaf and the transform of `Λ` is
`Λ(-r)[-r]`, supported everywhere. Asking `Ψ ≠ 1` is not enough when `Λ` is not a domain:
for `Λ = 𝔽_ℓ × 𝔽_ℓ` and `Ψ = (ψ₀, 1)` the transform has the trivial-character transform as a
factor.

Class: torsion; decided by the cohomology of `𝔸^r`, `H_c^*(𝔸^r, Λ) ≅ Λ(-r)[-2r]`, which needs
`[Finite Λ] [HasInvertibleExponent Λ S]`.
(sketch blueprint: `sk-prop-first-formula`) -/
theorem nonempty_iso_affineFourierTransform_unit [Finite Λ] [HasInvertibleExponent Λ S]
    [HasTateTwist Λ] [HasTateTwist.IsNormalized Λ] (Ψ : AddChar (ZMod p) Λ)
    (hΨ : IsUnit (Ψ 1 - 1)) :
    Nonempty ((affineFourierTransform Λ n S Ψ).obj (𝟙_ _) ≅
        (shiftFunctor _ (-(Fintype.card n : ℤ))).obj
          ((tateTwist Λ (𝔸(n; S)) (-(Fintype.card n : ℤ))).obj
            (skyscraperZero Λ n S))) :=
  sorry

/-- The Fourier–Deligne transform of the skyscraper at the origin of `𝔸(n; S)` is the
constant sheaf, shifted by the relative dimension `r = #n`:

`FT_ψ(δ₀) ≅ Λ[r]`.

On the affine line, the blueprint's case, this reads `FT_ψ(δ₀) ≅ Λ[1]`. Unlike
`AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_unit` this holds for every
character: the kernel restricted to `{0} ×_S 𝔸(n; S)` is the Artin–Schreier sheaf of the zero
function.

Class: torsion; decided by compact-support base change of `Rp₂,!` along the zero section,
which needs `[Finite Λ]`. The proof
(`AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_obj_rightDerivedLowerStar`) writes
`δ₀ = Rz_* Λ = Rz_! Λ`, moves `p₁^*` past it by base change, applies the projection formula for
the base change `ξ ↦ (0, ξ)` of `z`, along which the kernel is trivial, and ends with
`R(p₂ ∘ (0, 1))_! = R(𝟙)_!`.
(sketch blueprint: `sk-prop-first-formula`) -/
theorem nonempty_iso_affineFourierTransform_skyscraperZero [Finite Λ] (Ψ : AddChar (ZMod p) Λ) :
    Nonempty ((affineFourierTransform Λ n S Ψ).obj (skyscraperZero Λ n S) ≅
        (shiftFunctor _ (Fintype.card n : ℤ)).obj (𝟙_ _)) := by
  let A := ModuleCat.{u + 1} Λ
  -- the base change `ξ ↦ (0, ξ)` of the zero section along the first projection
  let z' : 𝔸(n; S) ⟶ pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) :=
    pullback.lift ((𝔸(n; S) ↘ S) ≫ zeroSection n S) (𝟙 _) (by simp)
  have hz₁ : z' ≫ pullback.fst (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) = (𝔸(n; S) ↘ S) ≫ zeroSection n S :=
    pullback.lift_fst _ _ _
  have hz₂ : z' ≫ pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) = 𝟙 _ := pullback.lift_snd _ _ _
  have sq : IsPullback (𝔸(n; S) ↘ S) z' (zeroSection n S)
      (pullback.fst (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)) := by
    refine IsPullback.of_bot ?_ hz₁.symm
      (IsPullback.of_hasPullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))
    rw [hz₂, zeroSection_comp_over]
    exact IsPullback.of_vert_isIso ⟨by simp⟩
  have : IsClosedImmersion z' := MorphismProperty.of_isPullback sq inferInstance
  -- `𝔸(n; S)` has characteristic `p`, being a retract of `𝔸(n; S) ×_S 𝔸(n; S)`
  have hinj : Function.Injective (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)).appTop.hom := by
    refine Function.LeftInverse.injective (g := z'.appTop.hom) fun x ↦ ?_
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hz₂, Scheme.Hom.id_appTop,
      CommRingCat.id_apply]
  have : CharP Γ(𝔸(n; S), ⊤) p := ⟨fun m ↦ by
    rw [← CharP.cast_eq_zero_iff Γ(pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S), ⊤) p,
      ← map_natCast (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)).appTop.hom,
      map_eq_zero_iff _ hinj]⟩
  -- the pairing vanishes along `z'`
  have hb : z'.appTop (stdPairing n S) = 0 := by
    rw [stdPairing, map_sum]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [map_mul, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hz₁, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply, zeroSection_appTop_coord, map_zero, zero_mul]
  let := 𝔸(n; S).overSpecZModOfCharP p
  obtain ⟨e₀⟩ := nonempty_iso_artinSchreierSheafOf_zero 𝔸(n; S)
    (Ψ.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom) (Λ := Λ)
  obtain ⟨e⟩ := nonempty_iso_leftDerivedUpperStar_singleFunctor Λ z'
    (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ (stdPairing n S)) (𝟙_ _)
    (artinSchreierSheafZModPullbackIso z' Ψ (stdPairing n S) ≪≫
      eqToIso (congrArg (artinSchreierSheafZMod _ Ψ) hb) ≪≫ e₀)
  -- no abbreviation for `𝔸(n; S) ↘ S`: `set` would duplicate the instances mentioning it
  exact nonempty_iso_kernelTransform_obj_rightDerivedLowerStar Λ
    (pullback.fst (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)) (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))
    (zeroSection n S) z' (𝔸(n; S) ↘ S) sq hz₂ _ (e ≪≫ singleFunctorObjUnitIso A _) _

/-- The Fourier–Deligne transform for the inverse character is the transform of the reflected
input, `ι = AlgebraicGeometry.AffineSpace.neg` being `x ↦ -x`:

`FT_{ψ⁻¹}(K) ≅ FT_ψ(ι^* K)`,

naturally in `K`:

```
                 ι^*
     D(𝔸(n; S)) ─────▶ D(𝔸(n; S))
              ╲             │
        FT_ψ⁻¹  ╲           │ FT_ψ
                  ▶         ▼
                    D(𝔸(n; S))
```

The kernel of `FT_{ψ⁻¹}` is the pullback of the kernel of `FT_ψ` along `ι × 1`, by
`AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheafOf_inv` and `b(-x, ξ) = -b(x, ξ)`.
It holds for every character.

The proof is compact-support base change of `Rp₂,!` along the cartesian square with sides
`ι × 1`, `p₂`, `p₂` and `𝟙`, so the same compactification of `p₂` is used on both sides;
`[Finite Λ]` enters through that base change
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`).
(sketch blueprint: `sk-def-ft`, remark; `lem-fd-as-lisse`) -/
theorem nonempty_iso_affineFourierTransform_inv [Finite Λ] (Ψ : AddChar (ZMod p) Λ) :
    Nonempty (affineFourierTransform Λ n S Ψ⁻¹ ≅
        D((neg n S)^*[ModuleCat.{u + 1} Λ]) ⋙ affineFourierTransform Λ n S Ψ) := by
  set π := 𝔸(n; S) ↘ S
  let := (pullback π π).overSpecZModOfCharP p
  have hΨ : Ψ⁻¹.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom =
      (Ψ.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom)⁻¹ := by
    ext; simp
  -- `σ^* 𝒦_{ψ⁻¹} = ℒ_{ψ⁻¹, -b} ≅ ℒ_{ψ, b} = 𝒦_ψ`, `σ = ι × 1`
  obtain ⟨e₀⟩ := nonempty_iso_artinSchreierSheafOf_neg_inv (pullback π π)
    (Ψ⁻¹.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom) (stdPairing n S)
  obtain ⟨e⟩ := nonempty_iso_leftDerivedUpperStar_singleFunctor Λ (negProd n S)
    (fourierKernel Λ π π Ψ⁻¹ (stdPairing n S)) (fourierKernel Λ π π Ψ (stdPairing n S))
    (artinSchreierSheafZModPullbackIso (negProd n S) Ψ⁻¹ (stdPairing n S) ≪≫
      eqToIso (congrArg (artinSchreierSheafZMod _ Ψ⁻¹) (negProd_appTop_stdPairing n S)) ≪≫
      e₀ ≪≫ eqToIso (congrArg (artinSchreierSheafOf (pullback π π) · (stdPairing n S))
        (by rw [hΨ, inv_inv])))
  exact nonempty_iso_kernelTransform_of_isIso Λ (pullback.fst π π) (pullback.snd π π)
    (negProd n S) (neg n S) (negProd_fst n S) (negProd_snd n S) _ _ e _

end AlgebraicGeometry.Etale
