/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.ArtinSchreier
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass
import WeilConjectures.AlgebraicGeometry.AffineSpace.LinearForm
import WeilConjectures.FourierTransform.AffineSpace.ArtinSchreierVanishing

/-!
Compact-support vanishing for finite-field Artin--Schreier characters of sum zero,
after arbitrary base change and an invertible linear change of coordinates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.Etale
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
variable {k : Type u} [Field k] [Fintype k] [Invertible (Fintype.card k : Λ)]
variable [HasTateTwist Λ] [HasTateTwist.IsNormalized Λ]
variable [HasInvertibleExponent Λ (Spec (.of k))]
variable (Ψ : AddChar k Λ) (hΨ : ∑ a : k, Ψ a = 0)
include hΨ in
private theorem finiteField_coord_vanishing (T : Scheme.{u}) (g : T ⟶ Spec (.of k)) :
    let X := 𝔸(PUnit.{u + 1}; T)
    letI : X.Over (Spec (.of k)) := ⟨X ↘ T ≫ g⟩
    IsZero ((R(X ↘ T)_![ModuleCat.{u + 1} Λ]).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        (artinSchreierSheafOf X Ψ (AffineSpace.coord T PUnit.unit)))) := by
  dsimp only
  let X := 𝔸(PUnit.{u + 1}; T)
  let Sk := Spec (CommRingCat.of k)
  let Xk := 𝔸(PUnit.{u + 1}; Sk)
  let : X.Over Sk := ⟨X ↘ T ≫ g⟩
  let e : X ⟶ Xk := AffineSpace.map PUnit g
  have sq := AffineSpace.isPullback_map (n := PUnit.{u + 1}) g
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  have hmap : AffineSpace.homOfVector (X ↘ Sk)
      (fun _ ↦ AffineSpace.coord T PUnit.unit) = e := by
    apply AffineSpace.hom_ext
    · simp [e]
      rfl
    · intro i
      cases i
      simp only [e, AffineSpace.homOfVector_appTop_coord]
      exact (AffineSpace.map_appTop_coord g PUnit.unit).symm
  let eL : artinSchreierSheafOf X Ψ (AffineSpace.coord T PUnit.unit) ≅
      (e)^*[ModuleCat.{u + 1} Λ].obj (artinSchreierSheaf Ψ) :=
    eqToIso (by rw [artinSchreierSheafOf, hmap])
  obtain ⟨es⟩ := nonempty_iso_leftDerivedUpperStar_singleFunctor Λ e
    (artinSchreierSheaf Ψ) _ (Iso.refl _)
  refine (((L((g)^*[ModuleCat.{u + 1} Λ])).map_isZero
    (isZero_rightDerivedLowerShriek_artinSchreierSheaf Ψ hΨ)).of_iso ?_)
  exact (R(X ↘ T)_![ModuleCat.{u + 1} Λ]).mapIso
    ((DerivedCategory.singleFunctor _ 0).mapIso eL ≪≫ es.symm) ≪≫
      (asIso (rightDerivedLowerShriekBaseChangeMap Λ sq)).symm.app _
end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale
open AlgebraicGeometry.AffineSpace
variable (Λ : Type (u + 1)) [CommRing Λ]
variable {k : Type u} [Field k] [Fintype k] [Invertible (Fintype.card k : Λ)]
variable [HasInvertibleExponent Λ (Spec (.of k))]
private theorem finiteField_pullback_linear_vanishing [Finite Λ]
    [HasTateTwist Λ] [HasTateTwist.IsNormalized Λ] {n : Type u} [Fintype n]
    {S T : Scheme.{u}} (g : T ⟶ S) (aT : T ⟶ Spec (.of k))
    {c : n → Γ(T, ⊤)} {i : n} (hc : IsUnit (c i))
    (Ψ : AddChar k Λ) (hΨ : ∑ a, Ψ a = 0) :
    let : (pullback (𝔸(n; S) ↘ S) g).Over (Spec (.of k)) :=
      ⟨pullback.snd _ _ ≫ aT⟩
    IsZero ((R(pullback.snd (𝔸(n; S) ↘ S) g)_![ModuleCat.{u + 1} Λ]).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        (artinSchreierSheafOf (pullback (𝔸(n; S) ↘ S) g) Ψ (linearForm g c)))) := by
  classical
  dsimp only
  let A := ModuleCat.{u + 1} Λ
  have := isIso_linearCoordHom g hc
  have := isIso_linearCoordInv g hc
  let Sk := Spec (CommRingCat.of k)
  let B := 𝔸({j // j ≠ i}; T)
  let Y := 𝔸(PUnit.{u + 1}; B)
  let : (pullback (𝔸(n; S) ↘ S) g).Over Sk := ⟨pullback.snd _ _ ≫ aT⟩
  let : Y.Over Sk := ⟨Y ↘ B ≫ B ↘ T ≫ aT⟩
  have : (linearCoordHom g c i).IsOver Sk :=
    ⟨by
      change linearCoordHom g c i ≫ (Y ↘ B ≫ B ↘ T ≫ aT) =
        pullback.snd (𝔸(n; S) ↘ S) g ≫ aT
      exact linearCoordHom_over_assoc g c i aT⟩
  -- `q` is the base change of `𝔸¹(𝔸(n ∖ {i}; T)) ⟶ 𝔸(n ∖ {i}; T) ⟶ T` along the change of
  -- variables
  have sq : IsPullback (linearCoordHom g c i) (pullback.snd (𝔸(n; S) ↘ S) g)
      (𝔸(PUnit.{u + 1}; 𝔸({j // j ≠ i}; T)) ↘ 𝔸({j // j ≠ i}; T) ≫ 𝔸({j // j ≠ i}; T) ↘ T)
      (𝟙 T) :=
    IsPullback.of_horiz_isIso ⟨by rw [linearCoordHom_over, Category.comp_id]⟩
  have : HasCompactification
      (𝔸(PUnit.{u + 1}; 𝔸({j // j ≠ i}; T)) ↘ 𝔸({j // j ≠ i}; T) ≫ 𝔸({j // j ≠ i}; T) ↘ T) :=
    .of_isPullback (IsPullback.of_horiz_isIso (fst := linearCoordInv g hc)
      (f := pullback.snd (𝔸(n; S) ↘ S) g) (g := 𝟙 T)
      ⟨by rw [linearCoordInv_snd, Category.comp_id]⟩)
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  obtain ⟨c₁⟩ := nonempty_iso_rightDerivedLowerShriek_comp Λ
    (𝔸(PUnit.{u + 1}; 𝔸({j // j ≠ i}; T)) ↘ 𝔸({j // j ≠ i}; T)) (𝔸({j // j ≠ i}; T) ↘ T)
  -- the change of variables pulls `ℒ_{ψ(y)}` back to `ℒ_{ψ(ℓ)}`
  obtain ⟨e⟩ := nonempty_iso_leftDerivedUpperStar_singleFunctor Λ (linearCoordHom g c i) _ _
    (artinSchreierSheafOfPullbackIso (linearCoordHom g c i) Ψ (coord _ PUnit.unit) ≪≫
      eqToIso (congrArg _ (linearCoordHom_appTop_coord g c i)))
  have h₀ := finiteField_coord_vanishing Λ Ψ hΨ B (B ↘ T ≫ aT)
  refine ((L((𝟙 T)^*[A])).map_isZero ((c₁.app _).symm.isZero_iff.1
    ((R(𝔸({j // j ≠ i}; T) ↘ T)_![A]).map_isZero h₀))).of_iso ?_
  exact (R(pullback.snd (𝔸(n; S) ↘ S) g)_![A]).mapIso e.symm ≪≫
    ((asIso (rightDerivedLowerShriekBaseChangeMap Λ sq)).app _).symm


end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale
open AlgebraicGeometry.AffineSpace
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
variable {k : Type u} [Field k] [Fintype k] [Invertible (Fintype.card k : Λ)]
variable [HasInvertibleExponent Λ (Spec (.of k))]
variable [HasTateTwist Λ] [HasTateTwist.IsNormalized Λ]
set_option maxHeartbeats 800000 in
-- The comparison of pullback sheaves unfolds several affine-space structure maps.
/-- A finite-field Artin--Schreier character of sum zero has vanishing compact-support
integral along every linear form having a unit coefficient.
Source: the affine-line vanishing proof in `ArtinSchreierVanishing` and the coordinate
argument in `UnitVanishing`, generalized from prime-field characters to arbitrary finite fields.

Base change the finite-field affine-line vanishing theorem to the affine space of the
remaining coordinates over `S`. The invertible linear coordinate change with first coordinate
`∑ j, c j * x j` identifies the sheaf with the pullback of the coordinate sheaf on that line.
Compact-support base change and composition carry its zero direct image to zero.
Finally identify affine space with its pullback along the identity of `S`.
(blueprint: lem-fd-finite-field-affine-vanishing) -/
theorem isZero_rightDerivedLowerShriek_finiteField_linearForm
    {n : Type u} [Fintype n] (S : Scheme.{u}) (aS : S ⟶ Spec (.of k))
    (c : n → Γ(S, ⊤)) (i : n) (hc : IsUnit (c i))
    (Ψ : AddChar k Λ) (hΨ : ∑ a, Ψ a = 0) :
    let X := 𝔸(n; S)
    let : X.Over (Spec (.of k)) := ⟨X ↘ S ≫ aS⟩
    IsZero ((R(X ↘ S)_![ModuleCat.{u + 1} Λ]).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        (artinSchreierSheafOf X Ψ
          (∑ j, coord S j * (X ↘ S).appTop (c j))))) := by
  classical
  dsimp only
  let X := 𝔸(n; S)
  let q : X ⟶ S := X ↘ S
  let P := pullback q (𝟙 S)
  let Sk := Spec (CommRingCat.of k)
  let : X.Over Sk := ⟨q ≫ aS⟩
  let : P.Over Sk := ⟨pullback.snd q (𝟙 S) ≫ aS⟩
  have sq₀ : IsPullback (𝟙 X) q q (𝟙 S) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  let e : X ≅ P := sq₀.isoPullback
  have heq : e.hom ≫ pullback.snd q (𝟙 S) = q := sq₀.isoPullback_hom_snd
  have hef : e.hom ≫ pullback.fst q (𝟙 S) = 𝟙 X := sq₀.isoPullback_hom_fst
  have : e.hom.IsOver Sk := ⟨by
    change e.hom ≫ (pullback.snd q (𝟙 S) ≫ aS) = q ≫ aS
    rw [← Category.assoc, heq]⟩
  have sq : IsPullback e.hom q (pullback.snd q (𝟙 S)) (𝟙 S) :=
    IsPullback.of_horiz_isIso ⟨by rw [heq, Category.comp_id]⟩
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  have hz := finiteField_pullback_linear_vanishing Λ (𝟙 S) aS hc Ψ hΨ
  obtain ⟨es⟩ := nonempty_iso_leftDerivedUpperStar_singleFunctor Λ e.hom
    (artinSchreierSheafOf P Ψ (linearForm (𝟙 S) c))
    (artinSchreierSheafOf X Ψ (∑ j, coord S j * q.appTop (c j)))
    (artinSchreierSheafOfPullbackIso e.hom Ψ (linearForm (𝟙 S) c) ≪≫
      eqToIso (by
        congr 1
        simp only [linearForm, map_sum, map_mul]
        congr 1
        ext j
        rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hef,
          Scheme.Hom.id_appTop, CommRingCat.id_apply,
          ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, heq]))
  refine ((L((𝟙 S)^*[ModuleCat.{u + 1} Λ])).map_isZero hz).of_iso ?_
  exact (R(q)_![ModuleCat.{u + 1} Λ]).mapIso es.symm ≪≫
    ((asIso (rightDerivedLowerShriekBaseChangeMap Λ sq)).app _).symm
end AlgebraicGeometry.Etale
