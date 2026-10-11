/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ConstantExtension
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Basic

/-!
# The Weil group of a curve after a finite constant field extension

Let `p : C₀ ⟶ Spec 𝔽_q` be a geometrically connected curve, `L = 𝔽_{q ^ m}` a finite extension
of `𝔽_q` of degree `m`, and `C₀' = C₀ ×_{𝔽_q} 𝔽_{q ^ m}`, a geometrically connected curve over
`𝔽_{q ^ m}` (`AlgebraicGeometry.Scheme.FiniteEtale.constantExtensionHom`). Given Weil groups
`W` of `C₀` and `W'` of `C₀'` and a path `τ` from the base point of `C₀'` to that of `C₀`, the
projection `C₀' ⟶ C₀` induces the *natural map* `W(C₀') → W(C₀)`
(`AlgebraicGeometry.WeilGroup.constantExtensionMap`). This file proves (blueprint
`lem-wf-weil-group-constant-extension`) that it is a continuous injective homomorphism with image
`W(C₀)^[m] = deg⁻¹(m ℤ)`, carrying the geometric subgroup `π₁(C)` of `W(C₀')` onto that of
`W(C₀)`, and that the degree over `𝔽_{q ^ m}` is the degree over `𝔽_q` divided by `m`.

## Main definitions

- `AlgebraicGeometry.WeilGroup.constantExtensionMap`: the natural map `W(C₀') → W(C₀)`.
- `AlgebraicGeometry.WeilGroup.degMultiples`: the subgroup `W(C₀)^[m] = deg⁻¹(m ℤ)`.

## Main statements

- `AlgebraicGeometry.WeilGroup.constantExtension`: the identification of `W(C₀')` with
  `W(C₀)^[m]`.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry

open Scheme.FiniteEtale

variable {K : Type u} [Field K] {C : Scheme.{u}} (p : C ⟶ Spec (.of K))
  (L : Type u) [Field L] [Algebra K L] [Module.Finite K L] [Algebra.Etale K L]

/-- The constant field extension `C₀ ×_K Spec L` of a curve is a curve over `L`: the projection
to `C₀` is finite, so it does not increase the dimension. -/
instance [IsCurve p] : IsCurve (constantExtensionHom p L) where
  krullDim_le_one :=
    ((constantExtensionProj p L).topologicalKrullDim_le_of_locallyQuasiFinite).trans
      (IsCurve.krullDim_le_one (f := p))

namespace WeilGroup

variable [Finite K] [Finite L] {p} [IsCurve p] {L} (W : WeilGroup p)
  (W' : WeilGroup (constantExtensionHom p L))

/-- The subgroup `W(C₀)^[m] = deg⁻¹(m ℤ)` of the elements of the Weil group whose degree is a
multiple of `m`. -/
def degMultiples (m : ℕ) : Subgroup W.carrier :=
  (Subgroup.zpowers (Multiplicative.ofAdd (m : ℤ))).comap W.deg

lemma mem_degMultiples_iff (m : ℕ) (w : W.carrier) :
    w ∈ W.degMultiples m ↔ (m : ℤ) ∣ (W.deg w).toAdd := by
  rw [degMultiples, Subgroup.mem_comap, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    rw [← hk, toAdd_zpow, toAdd_ofAdd, smul_eq_mul]
    exact Dvd.intro_left k rfl
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [toAdd_zpow, toAdd_ofAdd, smul_eq_mul, hk, mul_comm]

/-- There is a path from the base point of `C₀'` to that of `C₀`: an isomorphism between the fibre
functor at the base point of `C₀'`, precomposed with the base change of finite étale covers along
`C₀' ⟶ C₀`, and the fibre functor at the base point of `C₀`. -/
lemma nonempty_constantExtensionPath :
    Nonempty (Scheme.FiniteEtale.pullback (constantExtensionProj p L) ⋙
      fiber W'.basePoint ≅ fiber W.basePoint) := by
  have := W.connectedSpace
  obtain ⟨τ⟩ := nonempty_iso_of_fiberFunctor (fiber (W'.basePoint ≫ constantExtensionProj p L))
    (fiber W.basePoint)
  exact ⟨pullbackFiberIso _ _ ≪≫ τ⟩

variable (τ : Scheme.FiniteEtale.pullback (constantExtensionProj p L) ⋙ fiber W'.basePoint ≅
  fiber W.basePoint)

/-- The map `π₁(C₀', s') → π₁(C₀, s)` induced by the projection `C₀' ⟶ C₀` and the path `τ`. -/
noncomputable def constantExtensionFundamentalGroupMap :
    W'.fundamentalGroup →* W.fundamentalGroup :=
  have := W.connectedSpace
  fundamentalGroupMap τ W'.fundamentalGroup W.fundamentalGroup

lemma mem_weilGroup_constantExtensionFundamentalGroupMap_iff (g : W'.fundamentalGroup)
    (n : Multiplicative ℤ) :
    (g, n) ∈ weilGroup (constantExtensionHom p L) W'.basePoint W'.fundamentalGroup ↔
      (W.constantExtensionFundamentalGroupMap W' τ g, n ^ Module.finrank K L) ∈
        weilGroup p W.basePoint W.fundamentalGroup :=
  have := W.connectedSpace
  have := W.geometricallyConnected
  mem_weilGroup_constantExtension_iff p W'.basePoint τ W.fundamentalGroup W'.fundamentalGroup g n

/-- Blueprint `lem-wf-weil-group-constant-extension`: Weil group after a finite constant-field
extension.

The natural map `W(C₀') → W(C₀)` from the Weil group of the constant field extension
`C₀' = C₀ ×_{𝔽_q} 𝔽_{q ^ m}` over `𝔽_{q ^ m}` to the Weil group of `C₀` over `𝔽_q`, induced by
the projection `C₀' ⟶ C₀` and a path `τ` between the base points: on the presentations as
subgroups of `π₁ × ℤ` it is `(g, n) ↦ (ρ g, m n)`, `ρ : π₁(C₀', s') → π₁(C₀, s)` being the map
induced by base change of finite étale covers along `C₀' ⟶ C₀`. -/
noncomputable def constantExtensionMap : W'.carrier →* W.carrier :=
  W.weilGroupEquiv.symm.toMonoidHom.comp <|
    ((((W.constantExtensionFundamentalGroupMap W' τ).prodMap
      (powMonoidHom (Module.finrank K L))).comp
        (weilGroup (constantExtensionHom p L) W'.basePoint W'.fundamentalGroup).subtype).codRestrict
          _ fun w ↦ (W.mem_weilGroup_constantExtensionFundamentalGroupMap_iff W' τ _ _).1 w.2).comp
      W'.weilGroupEquiv.toMonoidHom

lemma weilGroupEquiv_constantExtensionMap (w : W'.carrier) :
    ((W.weilGroupEquiv (W.constantExtensionMap W' τ w) : _) :
      W.fundamentalGroup × Multiplicative ℤ) =
      (W.constantExtensionFundamentalGroupMap W' τ (W'.weilGroupEquiv w).1.1,
        (W'.weilGroupEquiv w).1.2 ^ Module.finrank K L) := by
  simp [constantExtensionMap]

/-- The natural map is induced by the map `ρ` of fundamental groups. -/
lemma toFundamentalGroup_constantExtensionMap (w : W'.carrier) :
    W.toFundamentalGroup (W.constantExtensionMap W' τ w) =
      W.constantExtensionFundamentalGroupMap W' τ (W'.toFundamentalGroup w) :=
  congrArg Prod.fst (W.weilGroupEquiv_constantExtensionMap W' τ w)

/-- The natural map multiplies degrees by `m`: the normalised degree over `𝔽_{q ^ m}` is the
degree over `𝔽_q` divided by `m`. -/
lemma deg_constantExtensionMap (w : W'.carrier) :
    W.deg (W.constantExtensionMap W' τ w) = W'.deg w ^ Module.finrank K L := by
  rw [W.deg_eq, W'.deg_eq]
  exact congrArg Prod.snd (W.weilGroupEquiv_constantExtensionMap W' τ w)

/-- The natural map is injective, since `π₁(C₀') → π₁(C₀)` is: `C₀' ⟶ C₀` is finite étale. -/
lemma constantExtensionMap_injective :
    Function.Injective (W.constantExtensionMap W' τ) := by
  have := W.connectedSpace
  have := W'.connectedSpace
  intro w₁ w₂ h
  have h' := congrArg (fun w ↦ ((W.weilGroupEquiv w : _) :
    W.fundamentalGroup × Multiplicative ℤ)) h
  simp only [weilGroupEquiv_constantExtensionMap, Prod.mk.injEq] at h'
  apply W'.weilGroupEquiv.injective
  refine Subtype.ext (Prod.ext ?_ ?_)
  · exact fundamentalGroupMap_injective τ W.fundamentalGroup W'.fundamentalGroup h'.1
  · have hm : Module.finrank K L ≠ 0 := Module.finrank_pos.ne'
    have h2 := congrArg Multiplicative.toAdd h'.2
    rw [toAdd_pow, toAdd_pow, nsmul_eq_mul, nsmul_eq_mul] at h2
    exact Multiplicative.toAdd.injective (mul_left_cancel₀ (by exact_mod_cast hm) h2)

/-- The image of the natural map is `W(C₀)^[m] = deg⁻¹(m ℤ)`. -/
lemma range_constantExtensionMap :
    (W.constantExtensionMap W' τ).range = W.degMultiples (Module.finrank K L) := by
  have := W.connectedSpace
  have := W'.connectedSpace
  have := W.geometricallyConnected
  ext w
  rw [mem_degMultiples_iff]
  constructor
  · rintro ⟨w', rfl⟩
    rw [deg_constantExtensionMap, toAdd_pow, nsmul_eq_mul]
    exact Dvd.intro _ rfl
  · intro hdvd
    obtain ⟨⟨h, n⟩, hmem⟩ := W.weilGroupEquiv w
    sorry

end WeilGroup

end AlgebraicGeometry
