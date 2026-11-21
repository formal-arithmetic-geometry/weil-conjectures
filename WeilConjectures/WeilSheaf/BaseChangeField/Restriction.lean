/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.BaseChangeField
public import WeilConjectures.WeilSheaf.BaseChangeField.Geometric
public import WeilConjectures.WeilSheaf.BaseChangeField.Transport

/-!
# Restriction of Weil sheaves to a finite extension of the base field

Let `θ : Ȳ ≅ Ȳ'` identify the geometric fibers of a `k₀`-scheme `Y` and a `k₀'`-scheme `Y'`,
with `θ ≫ Fr' = Frʳ ≫ θ`. The transport `(K, φ) ↦ (θ_* K, θ_* φ_r)` of pro-étale Weil sheaves
(`AlgebraicGeometry.ProEtaleWeilSheaf.transport`) preserves constructibility and lisseness, since
`θ_*` is the pullback along `θ⁻¹`; so it restricts to Weil sheaves.

For a finite extension `K` of `k₀` and `θ` the identification of the geometric fibers of `X` and
of `X_K = X ×_{k₀} K` (`AlgebraicGeometry.Scheme.Hom.geometricFiberBaseChangeIso`), this is the
restriction `F ↦ F_K` of Weil sheaves on `X` to `X_K`.

## Main definitions

- `AlgebraicGeometry.WeilSheaf.transport`: the transport of Weil sheaves along `θ`.
- `AlgebraicGeometry.WeilSheaf.baseChangeField`: the restriction `F ↦ F_K` to `X_K`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.IsLisse.transport`: the transport of a lisse Weil sheaf is lisse.
-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.WeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
  {k₀' : Type u} [Field k₀'] [Finite k₀'] [Fact (ringChar k₀' ≠ l)]
  {Y' : Scheme.{u}} [Y'.Over (Spec (CommRingCat.of k₀'))]
  (θ : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber ≅
    (Y' ↘ Spec (CommRingCat.of k₀')).geometricFiber) (r : ℕ)
  (hθ : θ.hom ≫ (Y' ↘ Spec (CommRingCat.of k₀')).geometricGaloisFrobenius.asIso.hom =
    ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ r).asIso.hom ≫ θ.hom)

/-- The pushforward `θ_*` along an identification of geometric fibers is the pullback along
`θ⁻¹`. -/
def adicLowerStarIsoUpperStarInv : (θ.hom)_*ᵃ[l] ≅ (θ.inv)^*ᵃ[l] :=
  (adicUpperStarIsoLowerStarInv l θ.symm).symm

omit [Finite k₀] [Fact (ringChar k₀ ≠ l)] [Finite k₀'] [Fact (ringChar k₀' ≠ l)] in
variable {θ} in
/-- The pushforward of a constructible sheaf along an identification of geometric fibers is
constructible. -/
theorem _root_.AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.lowerStar_hom
    {F : AdicSheaf l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    (hF : IsAdicConstructibleSheaf F) : IsAdicConstructibleSheaf ((θ.hom)_*ᵃ[l].obj F) :=
  (hF.upperStar θ.inv).of_iso ((adicLowerStarIsoUpperStarInv θ).app F).symm

/-- The transport `(F, φ) ↦ (θ_* F, θ_* φ_r)` of Weil sheaves on `Y` relative to `k₀` to Weil
sheaves on `Y'` relative to `k₀'`, along an identification `θ : Ȳ ≅ Ȳ'` of the geometric fibers
with `θ ≫ Fr' = Frʳ ≫ θ` (`AlgebraicGeometry.ProEtaleWeilSheaf.transport`). -/
def transport : WeilSheaf k₀ l Y ⥤ WeilSheaf k₀' l Y' :=
  (objectProperty k₀ l Y).liftFullSubcategory (objectProperty k₀' l Y')
    (ProEtaleWeilSheaf.transport θ r hθ) fun _ hF ↦ IsAdicConstructibleSheaf.lowerStar_hom hF

@[simp]
lemma transport_obj_obj (F : WeilSheaf k₀ l Y) :
    ((transport θ r hθ).obj F).obj = (ProEtaleWeilSheaf.transport θ r hθ).obj F.obj :=
  rfl

instance : (transport (l := l) θ r hθ).Additive :=
  ObjectProperty.liftFullSubcategory_additive _ _ _ _

variable {θ r hθ} in
/-- The transport of a lisse Weil sheaf is lisse. -/
theorem IsLisse.transport {F : WeilSheaf k₀ l Y} (hF : F.IsLisse) :
    ((WeilSheaf.transport θ r hθ).obj F).IsLisse :=
  (IsAdicLisseSheaf.upperStar θ.inv hF).of_iso ((adicLowerStarIsoUpperStarInv θ).app _).symm

section BaseChangeField

open Scheme.Hom

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] (K : Type u) [Field K] [Finite K]
  [Algebra k₀ K] [Fact (ringChar K ≠ l)]

omit [Finite k₀] [Finite K] in
variable (X) in
/-- The cartesian square exhibiting `X_K = X ×_{k₀} K` as the base change of `X`. -/
lemma isPullback_baseChangeField :
    IsPullback (pullback.fst (X ↘ Spec (CommRingCat.of k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
      (X.baseChangeField k₀ K ↘ Spec (CommRingCat.of K)) (X ↘ Spec (CommRingCat.of k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) :=
  IsPullback.of_hasPullback _ _

/-- The restriction `F ↦ F_K` of Weil sheaves on `X` to `X_K = X ×_{k₀} K` for a finite
extension `K` of `k₀`: the transport along the identification
`X ⊗_{k₀} k̄ ≅ X_K ⊗_K k̄` of geometric fibers, under which the geometric Frobenius of `K` is the
`[K : k₀]`-th power of that of `k₀`. -/
def baseChangeField : WeilSheaf k₀ l X ⥤ WeilSheaf K l (X.baseChangeField k₀ K) :=
  transport (geometricFiberBaseChangeIso (isPullback_baseChangeField X K)) (Module.finrank k₀ K)
    (geometricFiberBaseChangeIso_hom_comp_geometricGaloisFrobenius _ _
      Module.natCard_eq_pow_finrank)

/-- The restriction of a lisse Weil sheaf to `X_K` is lisse. -/
theorem IsLisse.baseChangeField {F : WeilSheaf k₀ l X} (hF : F.IsLisse) :
    ((WeilSheaf.baseChangeField K).obj F).IsLisse :=
  hF.transport

end BaseChangeField

end AlgebraicGeometry.WeilSheaf
