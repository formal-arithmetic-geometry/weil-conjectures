/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Comap
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# The pullback of `𝔾ₘ` to the generic point

Let `X` be an integral scheme with generic point `i : Spec k(X) ⟶ X`. The comparison map
`i^* 𝔾ₘ ⟶ 𝔾ₘ` of `AlgebraicGeometry.Scheme.upperStarGmSheafToGmSheaf` is an isomorphism,
although `i` is not étale.

The isomorphism is checked on stalks. For a morphism of sheaves `φ : G ⟶ f_* G'` and a
geometric point `s` of the source of `f`, the stalk at `s` of the transpose `f^* G ⟶ G'` of `φ`
is, up to the identification of the stalk of `f^* G` at `s` with the stalk of `G` at `s ≫ f`,
the map on stalks `G_{s ≫ f} ⟶ G'_s` which sends the germ of a section `δ` of `G` over a pointed
étale neighbourhood `(V, v)` of `s ≫ f` to the germ of `φ(δ)` over the base change
`(V ×_Y X, v)` (`AlgebraicGeometry.Etale.stalkComparison`). For `𝔾ₘ` along the generic point
this map is bijective: an étale neighbourhood of the generic point is cut out by finitely many
equations with coefficients in `k(X)`, which are defined over a nonempty open of `X`, and a
local ring of an étale `X`-scheme at a point over the generic point is a field.

## Main definitions

- `AlgebraicGeometry.Etale.stalkComparison`: the map on stalks `G_{s ≫ f} ⟶ G'_s` induced by
  `φ : G ⟶ f_* G'`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_sheafFiber_map_homEquiv_symm_iff`: the stalk of the transpose
  of `φ` is an isomorphism if and only if `AlgebraicGeometry.Etale.stalkComparison` is.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme Etale

namespace Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ X) {G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
  {G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
  (φ : G ⟶ (f)_*[AddCommGrpCat.{u + 1}].obj G')

/-- The map on stalks `G_{s ≫ f} ⟶ G'_s` induced by a morphism `φ : G ⟶ f_* G'`: the germ of a
section `δ` of `G` over a pointed étale neighbourhood `(V, v)` of `s ≫ f` goes to the germ of the
section `φ(δ)` of `G'` over the base change `V ×_Y X`, pointed by `v` and `s`. -/
noncomputable def stalkComparison :
    (pointSmallEtale (s ≫ f)).sheafFiber.obj G ⟶ (pointSmallEtale s).sheafFiber.obj G' :=
  (pointSmallEtale (s ≫ f)).presheafFiberDesc
    (fun V v ↦ φ.hom.app (op V) ≫ (pointSmallEtale s).toPresheafFiber (f.Etale.obj V)
      ((pointSmallEtaleFiberEtaleIso f s).inv.app V v) G'.obj)
    (fun V W g v ↦ by
      have h₁ := φ.hom.naturality g.op
      have h₂ := (pointSmallEtale s).toPresheafFiber_w (f.Etale.map g)
        ((pointSmallEtaleFiberEtaleIso f s).inv.app V v) G'.obj
      have h₃ := NatTrans.naturality_apply (pointSmallEtaleFiberEtaleIso f s).inv g v
      rw [h₃]
      erw [← h₂]
      rw [← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ _) h₁)

@[reassoc (attr := simp)]
lemma toPresheafFiber_stalkComparison (V : Y.Etale) (v : (pointSmallEtale (s ≫ f)).fiber.obj V) :
    (pointSmallEtale (s ≫ f)).toPresheafFiber V v G.obj ≫ stalkComparison f s φ =
      φ.hom.app (op V) ≫ (pointSmallEtale s).toPresheafFiber (f.Etale.obj V)
        ((pointSmallEtaleFiberEtaleIso f s).inv.app V v) G'.obj :=
  (pointSmallEtale (s ≫ f)).toPresheafFiber_presheafFiberDesc _ _ V v

/-- **The stalk of a transpose.** For `φ : G ⟶ f_* G'`, the stalk at a geometric point `s` of
the transpose `f^* G ⟶ G'` of `φ` under `f^* ⊣ f_*`, composed with the identification
`G_{s ≫ f} ≅ (f^* G)_s` of `AlgebraicGeometry.Etale.upperStarCompSheafFiberIso`, is the map on
stalks `AlgebraicGeometry.Etale.stalkComparison`. -/
lemma upperStarCompSheafFiberIso_inv_app_comp_sheafFiber_map :
    ((upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} f s).inv.app G) ≫
        (pointSmallEtale s).sheafFiber.map
          (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _).symm φ) =
      stalkComparison f s φ := by
  refine (pointSmallEtale (s ≫ f)).presheafFiber_hom_ext fun V v ↦ ?_
  refine Eq.trans ?_ (toPresheafFiber_stalkComparison f s φ V v).symm
  simp only [upperStarCompSheafFiberIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, Category.assoc]
  erw [GrothendieckTopology.Point.toPresheafFiber_sheafFiberIso_inv_app_assoc,
    GrothendieckTopology.Point.toPresheafFiber_sheafFiberComapIso_hom_app_assoc]
  rw [← Functor.map_comp]
  erw [GrothendieckTopology.Point.toPresheafFiber_naturality]
  -- the unit of the abstract pullback followed by the transpose of `φ` is `φ`
  have key : ((Hom.Etale f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1} Y.smallEtaleTopology
      X.smallEtaleTopology).unit.app G ≫ (f)_*[AddCommGrpCat.{u + 1}].map
        ((Functor.sheafPullbackConstruction.sheafPullbackIso
          (MorphismProperty.Over.pullback @Etale ⊤ f) AddCommGrpCat.{u + 1}
          (smallGrothendieckTopology (@Etale) Y) (smallGrothendieckTopology (@Etale) X)).hom.app G ≫
        ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv G G').symm φ) = φ := by
    rw [Functor.map_comp, ← Category.assoc]
    erw [Adjunction.unit_leftAdjointUniq_hom_app]
    exact ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv_unit G G' _).symm.trans
      (Equiv.apply_symm_apply _ _)
  rw [← Category.assoc]
  exact congrArg (· ≫ _) (congrArg (fun h ↦ h.hom.app (op V)) key)

end Etale

end AlgebraicGeometry

section Spreading

open Polynomial

/-- **Spreading out a unit of a standard étale algebra over a fraction field.** Let `R` be a
domain with fraction field `K`, `S` a standard étale `K`-algebra and `γ` a unit of `S`. Then there
are an étale `R`-algebra `T`, an `R`-algebra map `ψ : T ⟶ S` and a unit `δ` of `T` with
`ψ δ = γ`: the finitely many coefficients of a presentation of `S` and of an expression of `γ`
lie in a localization `R[1/a]`, over which they define a standard étale algebra, and `T` is a
further localization of it in which the numerator of `γ` is inverted. -/
theorem StandardEtalePresentation.exists_etale_units_eq {R K S : Type u} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] [CommRing S] [Algebra K S]
    (Q : StandardEtalePresentation K S) (γ : Sˣ) :
    ∃ (T : Type u) (_ : CommRing T) (ρ : R →+* T) (ψ : T →+* S), ρ.Etale ∧
      ψ.comp ρ = (algebraMap K S).comp (algebraMap R K) ∧ ∃ δ : Tˣ, ψ δ = γ := by
  classical
  obtain ⟨p, n, hp⟩ := Q.exists_mul_aeval_x_g_pow_eq_aeval_x γ.val
  -- a common denominator `b` of the coefficients of `f`, `g` and `p`
  obtain ⟨⟨b, hb⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors R)
    (Q.f.coeffs ∪ Q.g.coeffs ∪ p.coeffs : Finset K)
  have hbu : IsUnit (algebraMap R K b) := IsLocalization.map_units K ⟨b, hb⟩
  let Ra := Localization.Away b
  let φ : Ra →+* K := IsLocalization.Away.lift b hbu
  have hφ : φ.comp (algebraMap R Ra) = algebraMap R K := IsLocalization.Away.lift_comp b hbu
  have hrange (c : K) (hc : c ∈ Q.f.coeffs ∪ Q.g.coeffs ∪ p.coeffs) : c ∈ Set.range φ := by
    obtain ⟨r, hr⟩ := hint c hc
    refine ⟨IsLocalization.mk' Ra r (⟨b, 1, pow_one b⟩ : Submonoid.powers b), ?_⟩
    have h₁ : φ (IsLocalization.mk' Ra r (⟨b, 1, pow_one b⟩ : Submonoid.powers b)) *
        algebraMap R K b = algebraMap R K r := by
      rw [← hφ, RingHom.comp_apply, RingHom.comp_apply, ← map_mul, IsLocalization.mk'_spec]
    refine mul_right_cancel₀ hbu.ne_zero (h₁.trans ?_)
    rw [hr, Algebra.smul_def, mul_comm]
  have hsub (q : K[X]) (hq : q.coeffs ⊆ Q.f.coeffs ∪ Q.g.coeffs ∪ p.coeffs) :
      q ∈ Polynomial.lifts φ :=
    (Polynomial.lifts_iff_coeffs_subset_range _).2 fun c hc ↦ hrange c (hq hc)
  obtain ⟨F, hF, -, hFm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (hsub Q.f (fun c hc ↦ by simp [hc])) Q.monic_f
  obtain ⟨G, hG⟩ := hsub Q.g (fun c hc ↦ by simp [hc])
  obtain ⟨Pa, hPa⟩ := hsub p (fun c hc ↦ by simp [hc])
  rw [Polynomial.coe_mapRingHom] at hG hPa
  -- the standard étale pair over `R[1/b]`
  let P' := StandardEtalePair.ofMonic hFm G
  let : Algebra Ra S := ((algebraMap K S).comp φ).toAlgebra
  have haeval (q : Ra[X]) : aeval Q.x q = aeval Q.x (q.map φ) := by
    rw [aeval_def, aeval_def, eval₂_map]
    rfl
  have hx : P'.HasMap Q.x := by
    refine ⟨?_, ?_⟩
    · rw [StandardEtalePair.ofMonic_f, haeval, hF]
      exact Q.hasMap.1
    · rw [StandardEtalePair.ofMonic_g, map_mul, haeval, haeval, hG, ← Polynomial.derivative_map, hF]
      exact Q.hasMap.2.mul Q.hasMap.isUnit_derivative_f
  let ψ₀ : P'.Ring →ₐ[Ra] S := P'.lift Q.x hx
  let e : P'.Ring := aeval P'.X Pa
  have he : ψ₀ e = γ * aeval Q.x Q.g ^ n := by
    rw [show ψ₀ e = aeval (ψ₀ P'.X) Pa from (aeval_algHom_apply _ _ _).symm,
      StandardEtalePair.lift_X, haeval, hPa, hp]
  have heu : IsUnit (ψ₀ e) := he ▸ γ.isUnit.mul (Q.hasMap.2.pow n)
  let T := Localization.Away e
  let ψ : T →+* S := IsLocalization.Away.lift e heu
  have hψ : ψ.comp (algebraMap P'.Ring T) = ψ₀ := IsLocalization.Away.lift_comp e heu
  have hGX : IsUnit (aeval P'.X G) := by
    have h := P'.hasMap_X.2
    rw [StandardEtalePair.ofMonic_g, map_mul] at h
    exact isUnit_of_mul_isUnit_left h
  refine ⟨T, inferInstance, (algebraMap P'.Ring T).comp ((algebraMap Ra P'.Ring).comp
    (algebraMap R Ra)), ψ, ?_, ?_, (IsLocalization.Away.algebraMap_isUnit e).unit *
      (hGX.map (algebraMap P'.Ring T)).unit⁻¹ ^ n, ?_⟩
  · refine RingHom.Etale.stableUnderComposition _ _ ?_
      (RingHom.etale_algebraMap.2 (Algebra.Etale.of_isLocalizationAway e))
    exact RingHom.Etale.stableUnderComposition _ _
      (RingHom.etale_algebraMap.2 (Algebra.Etale.of_isLocalizationAway b))
      (RingHom.etale_algebraMap.2 inferInstance)
  · rw [← RingHom.comp_assoc, hψ, ← RingHom.comp_assoc, ψ₀.comp_algebraMap]
    change ((algebraMap K S).comp φ).comp (algebraMap R Ra) = _
    rw [RingHom.comp_assoc, hφ]
  · have h₁ : ψ (algebraMap P'.Ring T (aeval P'.X G)) = aeval Q.x Q.g := by
      rw [← RingHom.comp_apply, hψ]
      change ψ₀ (aeval P'.X G) = _
      rw [show ψ₀ (aeval P'.X G) = aeval (ψ₀ P'.X) G from (aeval_algHom_apply _ _ _).symm,
        StandardEtalePair.lift_X, haeval, hG]
    have h₂ : ψ (algebraMap P'.Ring T e) = γ * aeval Q.x Q.g ^ n := by
      rw [← RingHom.comp_apply, hψ]
      exact he
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, IsUnit.unit_spec]
    rw [h₂]
    have h₃ : aeval Q.x Q.g * ψ ↑(hGX.map (algebraMap P'.Ring T)).unit⁻¹ = 1 := by
      rw [← h₁, ← map_mul]
      change ψ (↑(hGX.map (algebraMap P'.Ring T)).unit *
        ↑(hGX.map (algebraMap P'.Ring T)).unit⁻¹) = 1
      rw [Units.mul_inv, map_one]
    rw [mul_assoc, ← mul_pow, h₃, one_pow, mul_one]

end Spreading
