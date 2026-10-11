/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Orientation
public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom

/-!

# Duality against pullback

Let `f : X ⟶ Y` be a morphism admitting a compactification. The Verdier dual exchanges the
derived pullback and the exceptional inverse image:

`𝔻_X Lf^* ≅ Rf^! 𝔻_Y`.

It is the evaluation at `N = ω_Y` of the internal-Hom form

`Rf^! RHom_Y(K, N) ≅ RHom_X(Lf^* K, Rf^! N)`,

natural in `K` and `N`, combined with `Rf^! ω_Y ≅ ω_X`. For `f` smooth of pure relative
dimension `d` with an orientation, substituting smooth purity `Rf^! ≅ Lf^*(-)(d)[2d]` gives
`𝔻_X Lf^* K ≅ (Lf^* 𝔻_Y K)(d)[2d]`.

As the blueprint remark `rem-sf-kv-formal` explains, given biduality the first statement turns
the Künneth–Verdier theorem into the statement that Verdier duality commutes with external
products, `𝔻_{X×Y}(M ⊠ N) ≅ 𝔻_X M ⊠ 𝔻_Y N`, which is not formal.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_rightDerivedUpperShriek_derivedHom_iso`
  (`cor-sf-duality-pullback`): `Rf^! RHom_Y(K, N) ≅ RHom_X(Lf^* K, Rf^! N)`, for a general
  coefficient category in which the projection formula holds.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_derivedHom`
  (`cor-sf-duality-pullback`): the same at finite coefficients.
- `AlgebraicGeometry.Etale.nonempty_iso_verdierDual_leftDerivedUpperStar`
  (`cor-sf-duality-pullback`): `𝔻_X Lf^* ≅ Rf^! 𝔻_Y` as functors on `D(Y_ét, Λ)ᵒᵖ`.
- `AlgebraicGeometry.Etale.Orientation.nonempty_iso_verdierDual_leftDerivedUpperStar`
  (`cor-sf-duality-pullback`): `𝔻_X Lf^* K ≅ (Lf^* 𝔻_Y K)(d)[2d]` for an oriented smooth `f`.

## Implementation notes

The blueprint obtains `𝔻_X Lf^* ≅ Rf^! 𝔻_Y` by passing to right adjoints in the Verdier
exchange `𝔻_Y Rf_! ≅ Rf_* 𝔻_X`, using biduality to see that `𝔻_Y` is its own adjoint. Here the
same mate calculus is applied one step earlier, to the projection formula itself: the
internal-Hom form is the conjugate of `PF : Rf_! M ⊗ᴸ K ≅ Rf_!(M ⊗ᴸ Lf^* K)` under the
adjunctions `K ⊗ᴸ Rf_!(-) ⊣ Rf^! RHom(K, -)` and `Rf_!(Lf^* K ⊗ᴸ -) ⊣ RHom(Lf^* K, Rf^! -)`,
exactly as the tensor–Hom exchange (`AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIso`)
is. This avoids biduality, so the isomorphism holds on all of `D(Y_ét, Λ)` and not only on
`Dᵇctf`. Its naturality in `f` is not recorded.

The symmetry of `⊗ᴸ` is only available as `Nonempty`
(`AlgebraicGeometry.Etale.nonempty_iso_derivedTensor_flip`), so the isomorphisms are asserted
as `Nonempty (_ ≅ _)`, as for the other comparison isomorphisms of this directory.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section General

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [Etale.UpperStarPreservesFlat A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [(R(f)_![A]).IsLeftAdjoint]

/-- Blueprint `cor-sf-duality-pullback`: Duality against pullback, internal-Hom form.

Let `f : X ⟶ Y` admit a compactification, and assume the projection formula for `f`
(axiom (A3) of `def-sf-datum`). Then

`Rf^! RHom_Y(K, N) ≅ RHom_X(Lf^* K, Rf^! N)`,

naturally in `K` and `N`, i.e. as bifunctors `D(Y_ét)ᵒᵖ ⥤ D(Y_ét) ⥤ D(X_ét)`.

The bifunctor `(K, M) ↦ K ⊗ᴸ Rf_! M` is left adjoint, with the parameter `K`, to
`(K, N) ↦ Rf^! RHom_Y(K, N)`, and `(K, M) ↦ Rf_!(Lf^* K ⊗ᴸ M)` is left adjoint to
`(K, N) ↦ RHom_X(Lf^* K, Rf^! N)`. The projection formula, together with the symmetry of
`⊗ᴸ`, identifies the two left adjoints, and the isomorphism is the conjugate
(`CategoryTheory.ParametrizedAdjunction.conjugateIso`). -/
theorem nonempty_rightDerivedUpperShriek_derivedHom_iso [IsIso (projectionMap A f)] :
    Nonempty (RHom(Y)[A] ⋙ (Functor.whiskeringRight _ _ _).obj R(f)^![A] ≅
      L((f)^*[A]).op ⋙ RHom(X)[A] ⋙ (Functor.whiskeringLeft _ _ _).obj R(f)^![A]) := by
  obtain ⟨βX⟩ := nonempty_iso_derivedTensor_flip A X
  obtain ⟨βY⟩ := nonempty_iso_derivedTensor_flip A Y
  -- `Rf_!(Lf^* K ⊗ᴸ M) ≅ Rf_!(M ⊗ᴸ Lf^* K) ≅ Rf_! M ⊗ᴸ K ≅ K ⊗ᴸ Rf_! M`
  let e : L((f)^*[A]) ⋙ -⊗ᴸ-(X)[A] ⋙ (Functor.whiskeringLeft _ _ _).obj (𝟭 _) ⋙
        (Functor.whiskeringRight _ _ _).obj R(f)_![A] ≅
      -⊗ᴸ-(Y)[A] ⋙ (Functor.whiskeringLeft _ _ _).obj R(f)_![A] ⋙
        (Functor.whiskeringRight _ _ _).obj (𝟭 _) :=
    NatIso.ofComponents (fun K ↦ NatIso.ofComponents (fun M ↦
      (R(f)_![A]).mapIso ((βX.app _).app M) ≪≫
        (asIso (((projectionMap A f).app M).app K)).symm ≪≫ (βY.app _).app K)
      (fun {M M'} g ↦ by
        have h₁ := (βX.hom.app (L((f)^*[A]).obj K)).naturality g
        have h₂ := congr_app ((projectionMap A f).naturality g) K
        have h₃ := congr_app (βY.hom.naturality ((R(f)_![A]).map g)) K
        dsimp at h₁ h₂ h₃ ⊢
        simp only [Category.assoc, ← Functor.map_comp_assoc, h₁]
        rw [Functor.map_comp_assoc, IsIso.eq_inv_comp, ← reassoc_of% h₂]
        simp [h₃]))
      (fun {K K'} g ↦ by
        ext M
        have h₁ := congr_app (βX.hom.naturality (L((f)^*[A]).map g)) M
        have h₂ := ((projectionMap A f).app M).naturality g
        have h₃ := (βY.hom.app ((R(f)_![A]).obj M)).naturality g
        dsimp at h₁ h₂ h₃ ⊢
        simp only [Category.assoc, ← Functor.map_comp_assoc, h₁]
        rw [Functor.map_comp_assoc, IsIso.eq_inv_comp, ← reassoc_of% h₂]
        simp [h₃])
  exact ⟨((derivedTensorHomAdjunction₂ A Y).comp (rightDerivedUpperShriekAdjunction A f)
      Adjunction.id).conjugateIso
    (((derivedTensorHomAdjunction₂ A X).precomp L((f)^*[A])).comp Adjunction.id
      (rightDerivedUpperShriekAdjunction A f)) e⟩

end General

section Finite

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
  [HasCompactification f]

/-- Blueprint `cor-sf-duality-pullback`: Duality against pullback, internal-Hom form.

For a morphism `f : X ⟶ Y` admitting a compactification and a finite coefficient ring `Λ`,

`Rf^! RHom_Y(K, N) ≅ RHom_X(Lf^* K, Rf^! N)`,

naturally in `K` and `N`. This is
`AlgebraicGeometry.Etale.nonempty_rightDerivedUpperShriek_derivedHom_iso` at
`A = ModuleCat Λ`, the projection formula holding at finite coefficients
(`AlgebraicGeometry.Etale.isIso_projectionMap_of_finite`). -/
theorem nonempty_iso_rightDerivedUpperShriek_derivedHom :
    Nonempty (RHom(Y)[ModuleCat.{u + 1} Λ] ⋙
        (Functor.whiskeringRight _ _ _).obj R(f)^![ModuleCat.{u + 1} Λ] ≅
      L((f)^*[ModuleCat.{u + 1} Λ]).op ⋙ RHom(X)[ModuleCat.{u + 1} Λ] ⋙
        (Functor.whiskeringLeft _ _ _).obj R(f)^![ModuleCat.{u + 1} Λ]) :=
  have := isIso_projectionMap_of_finite Λ f
  nonempty_rightDerivedUpperShriek_derivedHom_iso _ f

variable {S : Scheme.{u}} (aY : Y ⟶ S) [HasCompactification aY] [HasCompactification (f ≫ aY)]
  [QuasiCompact (f ≫ aY)]

/-- Blueprint `cor-sf-duality-pullback`: Duality against pullback.

Let `f : X ⟶ Y` be a morphism over a base `S`, with structure morphisms `a_Y : Y ⟶ S` and
`a_X = f ≫ a_Y`, all admitting a compactification, and let `Λ` be a finite coefficient ring.
Then the Verdier duals `𝔻_Y = RHom_Y(-, ω_Y)` and `𝔻_X = RHom_X(-, ω_X)` satisfy

`𝔻_X Lf^* ≅ Rf^! 𝔻_Y`

as functors `D(Y_ét, Λ)ᵒᵖ ⥤ D(X_ét, Λ)`.

The blueprint deduces this from the Verdier exchange `𝔻_Y Rf_! ≅ Rf_* 𝔻_X`
(`thm-sf-verdier-exchange`) by passing to right adjoints, using biduality to identify the
adjoint of `𝔻_Y` with `𝔻_Y`, and so states it on `Dᵇctf`. The same mate calculus applied to
the projection formula gives the internal-Hom form
`Rf^! RHom_Y(K, N) ≅ RHom_X(Lf^* K, Rf^! N)`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_derivedHom`) without
biduality; at `N = ω_Y`, with `Rf^! ω_Y ≅ ω_X`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_dualizingComplex`), it is the
statement, on all of `D(Y_ét, Λ)`. -/
theorem nonempty_iso_verdierDual_leftDerivedUpperStar :
    Nonempty (L((f)^*[ModuleCat.{u + 1} Λ]).op ⋙ verdierDual _ (f ≫ aY) ≅
      verdierDual _ aY ⋙ R(f)^![ModuleCat.{u + 1} Λ]) := by
  obtain ⟨e₁⟩ := nonempty_iso_rightDerivedUpperShriek_derivedHom Λ f
  obtain ⟨e₂⟩ := nonempty_iso_rightDerivedUpperShriek_dualizingComplex Λ f aY
  exact ⟨NatIso.ofComponents
    (fun K ↦ ((RHom(X)[ModuleCat.{u + 1} Λ]).obj
        (op ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K.unop))).mapIso e₂.symm ≪≫
      ((e₁.app K).app (dualizingComplex _ aY)).symm)
    (fun {K K'} g ↦ by
      have h := congr_app (e₁.inv.naturality g) (dualizingComplex _ aY)
      dsimp [verdierDual] at h ⊢
      simp only [Category.assoc, h, ← NatTrans.naturality_assoc]
      rfl)⟩

end Finite

section Orientation

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {k : Type u} [Field k]
  [HasInvertibleExponent Λ (Spec (.of k))] {X Y : Scheme.{u}} {d : ℕ} {f : X ⟶ Y}
  [IsSeparated f] [HasCompactification f] (aY : Y ⟶ Spec (.of k)) [IsSeparated aY]
  [LocallyOfFiniteType aY] [QuasiCompact aY] [HasCompactification aY]
  [HasCompactification (f ≫ aY)] [QuasiCompact (f ≫ aY)]

/-- Blueprint `cor-sf-duality-pullback`: Duality against pullback, oriented smooth case.

Let `Y` be separated of finite type over a field `k`, let `Λ` be a finite coefficient ring
whose exponent is invertible on `k`, and let `f : X ⟶ Y` be separated, smooth of pure relative
dimension `d`, with an orientation `o`. Then for `K ∈ Dᵇctf(Y, Λ)`

`𝔻_X Lf^* K ≅ (Lf^* 𝔻_Y K)(d)[2d]`.

As in the blueprint, this substitutes the orientation into
`𝔻_X Lf^* K ≅ Rf^! 𝔻_Y K` (`AlgebraicGeometry.Etale.nonempty_iso_verdierDual_leftDerivedUpperStar`):
the smooth purity map `Rf^! L ≅ (Lf^* L)(d)[2d]` (`AlgebraicGeometry.Etale.smoothPurityIso`)
is built from the orientation `ω_f ≅ Λ_X(d)[2d]` and the tensor formula
`Rf^! L ≅ Lf^* L ⊗ᴸ ω_f` of `sk-prop-cohsm`, applied to `L = 𝔻_Y K`, which lies in
`Dᵇctf(Y, Λ)` by `sk-prop-sf-biduality-general`. -/
theorem Orientation.nonempty_iso_verdierDual_leftDerivedUpperStar (o : Orientation Λ f d)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ Y K) :
    Nonempty ((verdierDual _ (f ≫ aY)).obj (op ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ≅
      (twistShift Λ X d).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj ((verdierDual _ aY).obj (op K)))) := by
  have := o.smoothOfRelativeDimension
  have : HasInvertibleExponent Λ X := HasInvertibleExponent.of_hom (f ≫ aY)
  obtain ⟨e⟩ := nonempty_iso_verdierDual_leftDerivedUpperStar Λ f aY
  obtain ⟨φ⟩ := nonempty_iso_rightDerivedUpperShriek_obj_derivedTensor Λ (d := d) f
    ((verdierDual _ aY).obj (op K)) (constructibleFiniteTor_verdierDual Λ aY hK)
  exact ⟨e.app (op K) ≪≫ (smoothPurityIso Λ f _ o.twistShiftIso.symm φ).symm⟩

end Orientation

end Etale

end AlgebraicGeometry
