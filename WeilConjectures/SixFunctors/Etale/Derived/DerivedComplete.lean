/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.IntegralCoefficient
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect

/-!
# Derived completeness and the six operations

Let `Λ` be a domain and `I` a principal ideal of `Λ`, so that every `Λ/Iⁿ` is a perfect
`Λ`-module. This file records that the operations used by Poincaré duality carry objects of
`D(X_ét, Λ)` that are derived complete for `I` (`DerivedCategory.derivedComplete`) to derived
complete objects. At the integral stage `Λ = 𝒪_E`, `I = 𝔪_E` of the `ℓ`-adic formalism these
say that the operations restrict to the adic categories `D_comp(−, 𝒪_E)` of
`DerivedCategory.derivedCompleteIntegral`. Together with
`AlgebraicGeometry.Etale.derivedCompleteIntegral_rightDerivedUpperShriek` (in
`WeilConjectures.EtaleCohomology.Purity.Smooth.Transport`), for `Rf^!`, this places every
object of the derived Poincaré pairing at `Λ = 𝒪_E` in the adic category.

## Main statements

- `AlgebraicGeometry.Etale.derivedComplete_rightDerivedLowerStar`: `Rf_*` preserves derived
  completeness.
- `AlgebraicGeometry.Etale.derivedComplete_rightDerivedLowerShriek`: so does `Rf_!`.
- `AlgebraicGeometry.Etale.derivedComplete_coefficientDual`: so does the coefficient dual
  `K ↦ K^∨`, provided the constant complex `Λ_X` is itself derived complete.

The `derivedCompleteIntegral_*` versions are their specialisations to `𝒪_E`.

## Implementation notes

The hypotheses on `(Λ, I)` are only used to make each `Λ/Iⁿ` perfect, through
`AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerStar`. For `𝒪_E` the
ideal `𝔪_E` is principal when `E` is finite over `ℚ_ℓ`
(`PadicAlgCl.isPrincipal_maximalIdealShrink`), which is why the specialisations assume it.

The blueprint states `sk-thm-transport` at the three stages `𝒪_E`, `E` and `ℚ̄_ℓ`. Only the
integral stage `𝒪_E` is stated here, and only its non-formal part: that the operations preserve
derived completeness. The `E` stage would be the image of these statements under the
rationalization `DerivedCategoryDerivedCompleteRational.fromIntegral`, and the `ℚ̄_ℓ` stage
their colimit over finite extensions `E/ℚ_ℓ`, a colimit category the repository does not have;
neither is stated. Which coefficient category carries the `E` and `ℚ̄_ℓ` stages is not decided
here.
-/

@[expose] public section

universe w u

open CategoryTheory Opposite

open scoped CategoryTheory.Functor

namespace CategoryTheory.Pretriangulated.IsHomotopyLimit

open Limits

variable {C : Type*} [Category C] [Limits.HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

set_option backward.defeqAttrib.useBackward true in
/-- A cone over a tower whose legs are isomorphisms from level `1` on is a homotopy limit
cone: the term at level `0` does not matter. Its Milnor triangle is split, `1 - t` having the
section with components `y ↦ y₀` at `0` and `y ↦ -∑_{1 ≤ k < n} y_k` at `n ≥ 1` (transported
along the transition isomorphisms). -/
lemma of_isIso_π_succ {F : ℕᵒᵖ ⥤ C} (c : Cone F) [∀ n : ℕ, IsIso (c.π.app (op (n + 1)))]
    [HasProduct fun n : ℕ ↦ F.obj (op n)] : IsHomotopyLimit c := by
  let P : Fan fun n : ℕ ↦ F.obj (op n) := Fan.mk _ (Pi.π _)
  let hP : IsLimit P := productIsProduct _
  let ρ (n : ℕ) : F.obj (op (n + 1)) ⟶ c.pt := inv (c.π.app (op (n + 1)))
  let g (n : ℕ) : P.pt ⟶ c.pt := P.proj (n + 1) ≫ ρ n
  have hτ (k : ℕ) : F.map (homOfLE (k + 1).le_succ).op ≫ ρ k = ρ (k + 1) := by
    refine IsIso.eq_inv_of_hom_inv_id ?_
    rw [← Category.assoc, c.w, IsIso.hom_inv_id]
  have hg (k : ℕ) : (𝟙 P.pt - towerShift hP) ≫ g k = g k - g (k + 1) := by
    simp only [g, Preadditive.sub_comp, Category.id_comp, towerShift, Fan.IsLimit.fac_assoc,
      Category.assoc, hτ]
  have hgπ (n : ℕ) : g n ≫ c.π.app (op (n + 1)) = P.proj (n + 1) := by simp [g, ρ]
  have hgπ₀ : g 0 ≫ c.π.app (op 0) = P.proj 1 ≫ F.map (homOfLE (Nat.zero_le 1)).op := by
    simp only [g, ρ, Category.assoc]
    rw [← c.w (homOfLE (Nat.zero_le 1)).op, IsIso.inv_hom_id_assoc]
  let ℓ : c.pt ⟶ P.pt := Fan.IsLimit.lift hP fun n ↦ c.π.app (op n)
  let s : ∀ n : ℕ, P.pt ⟶ F.obj (op n)
    | 0 => P.proj 0
    | n + 1 => -(∑ k ∈ Finset.range n, g k) ≫ c.π.app (op (n + 1))
  let σ : P.pt ⟶ P.pt := Fan.IsLimit.lift hP s
  have hℓg : ℓ ≫ g 0 = 𝟙 _ := by simp [ℓ, g, ρ]
  have hℓt : ℓ ≫ (𝟙 P.pt - towerShift hP) = 0 := Fan.IsLimit.hom_ext hP _ _ fun n ↦ by
    simp [ℓ, Preadditive.sub_comp, towerShift, c.w]
  have hσg : σ ≫ g 0 = 0 := by simp [σ, g, s]
  have hσt : σ ≫ (𝟙 P.pt - towerShift hP) = 𝟙 _ := Fan.IsLimit.hom_ext hP _ _ fun n ↦ by
    cases n with
    | zero =>
      simp [σ, s, Preadditive.sub_comp, towerShift]
    | succ n =>
      simp only [Preadditive.comp_sub, Category.comp_id, Preadditive.sub_comp, Category.assoc,
        towerShift, Fan.IsLimit.fac, Category.id_comp, σ, Fan.IsLimit.fac_assoc, s, c.w,
        Finset.sum_range_succ, Preadditive.neg_comp, Preadditive.add_comp, hgπ, neg_add_rev]
      abel
  have hsplit : g 0 ≫ ℓ + (𝟙 P.pt - towerShift hP) ≫ σ = 𝟙 _ :=
    Fan.IsLimit.hom_ext hP _ _ fun n ↦ by
      cases n with
      | zero =>
        simp only [Preadditive.add_comp, Category.assoc, Fan.IsLimit.fac, ℓ, σ, s, hgπ₀,
          Preadditive.sub_comp, Category.id_comp, towerShift, Category.id_comp]
        simp [P]
      | succ n =>
        have h₁ : (g 0 ≫ ℓ) ≫ P.proj (n + 1) = g 0 ≫ c.π.app (op (n + 1)) := by
          simp [ℓ]
        have h₂ : ((𝟙 P.pt - towerShift hP) ≫ σ) ≫ P.proj (n + 1) =
            -(g 0 - g n) ≫ c.π.app (op (n + 1)) := by
          rw [Category.assoc, Fan.IsLimit.fac, Preadditive.comp_neg, ← Category.assoc,
            Preadditive.comp_sum]
          simp only [hg, Finset.sum_range_sub']
        rw [Preadditive.add_comp, h₁, h₂, Preadditive.sub_comp, hgπ, Category.id_comp]
        abel
  let e : P.pt ≅ c.pt ⊞ P.pt :=
    { hom := biprod.lift (g 0) (𝟙 P.pt - towerShift hP)
      inv := biprod.desc ℓ σ
      hom_inv_id := by rw [biprod.lift_desc, hsplit]
      inv_hom_id := by
        apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
          simp [hℓg, hℓt, hσg, hσt] }
  refine ⟨P, hP, 0, isomorphic_distinguished _ (binaryBiproductTriangle_distinguished c.pt P.pt)
    _ (Triangle.isoMk _ _ (Iso.refl _) e (Iso.refl _) ?_ ?_ ?_)⟩
  · apply biprod.hom_ext <;> simp [e, hℓg, hℓt, ℓ]
  · simp [e]
  · simp

end CategoryTheory.Pretriangulated.IsHomotopyLimit

namespace DerivedCategory

open Limits

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R]

/-- Every object of `D(J, R)` is derived complete for the zero ideal: the reductions
`K ⟶ K ⊗ᴸ R/0ⁿ` are isomorphisms for `n ≥ 1`, so the tower is constant from level `1` on. -/
lemma derivedComplete_bot (K : _root_.DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    derivedComplete J ⊥ K := by
  have := (sheafTensorStructure J R).isIso_ε
  have (n : ℕ) : IsIso ((derivedCompletionCone J ⊥ K).π.app (op (n + 1))) := by
    have hp : (⊥ : Ideal R) ^ (n + 1) = ⊥ := Ideal.bot_pow n.succ_ne_zero
    have : IsIso (ModuleCat.ofHom (Submodule.mkQ ((⊥ : Ideal R) ^ (n + 1)))) := by
      rw [← Submodule.coe_quotEquivOfEqBot_symm _ hp]
      exact (Submodule.quotEquivOfEqBot _ hp).symm.toModuleIso.isIso_hom
    have h₁ : IsIso ((quotPowCone J (⊥ : Ideal R)).π.app (op (n + 1))) := by
      simp only [quotPowCone, Cone.extend_π, NatTrans.comp_app, Functor.const_map_app,
        Functor.mapCone_π_app, Sheaf.quotPowCone, Ideal.quotPowCone]
      infer_instance
    simp only [derivedCompletionCone, Cone.extend_π, NatTrans.comp_app, Functor.const_map_app,
      Functor.mapCone_π_app]
    infer_instance
  exact CategoryTheory.Pretriangulated.IsHomotopyLimit.of_isIso_π_succ _

end DerivedCategory

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

set_option hygiene false in
/-- The constant complex `Λ_X`: the constant sheaf `Λ` on `X_ét`, placed in degree `0`. It is
the monoidal unit of `D(X_ét, Λ)` up to `DerivedCategory.εSingleFunctorZero`; it is spelled this
way so that the monoidal structure of the derived category stays out of the statements below
(see the implementation notes of `WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs`).
-/
local notation "Λ_(" X ", " Λ ")" =>
  (_root_.DerivedCategory.singleFunctor (Sheaf (Scheme.smallEtaleTopology X)
    (ModuleCat.{u + 1} Λ)) 0).obj
      ((constantSheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ))

section General

variable {Λ : Type (u + 1)} [CommRing Λ] [IsDomain Λ] (I : Ideal Λ) (hI : I.IsPrincipal)

include hI

/-- **`Rf_*` preserves derived completeness.** For a principal ideal `I` of a domain `Λ` and
every morphism `f : X ⟶ Y`, the derived direct image `Rf_*` carries objects of `D(X_ét, Λ)`
that are derived complete for `I` to derived complete objects of `D(Y_ét, Λ)`. -/
theorem derivedComplete_rightDerivedLowerStar {X Y : Scheme.{u}} (f : X ⟶ Y) (K : 𝐃(X, Λ))
    (hK : DerivedCategory.derivedComplete X.smallEtaleTopology I K) :
    DerivedCategory.derivedComplete Y.smallEtaleTopology I
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) := by
  -- For `I = (ϖ)` with `ϖ ≠ 0`, derived completeness is right orthogonality to the objects on
  -- which `ϖ` acts invertibly. Such objects are preserved by the `Λ`-linear left adjoint `Lf^*`
  -- of `Rf_*`, so maps from them to `Rf_* K` vanish by adjunction. For `I = 0` every object is
  -- derived complete.
  obtain ⟨ϖ, hIϖ⟩ := hI.principal
  by_cases h0 : ϖ = 0
  · rw [hIϖ, h0, Submodule.span_singleton_eq_bot.mpr rfl]
    exact DerivedCategory.derivedComplete_bot _ _
  have hϖ : ϖ ∈ nonZeroDivisors Λ := mem_nonZeroDivisors_of_ne_zero h0
  rw [DerivedCategory.derivedComplete_iff_rightOrthogonal hϖ hIϖ] at hK ⊢
  intro M φ hM
  let adj := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f
  have hM' : IsIso (ϖ • 𝟙 ((L((f)^*[ModuleCat.{u + 1} Λ])).obj M)) := by
    have : IsIso (ϖ • 𝟙 M) := hM
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_smul]
    infer_instance
  rw [← (adj.homEquiv _ _).apply_symm_apply φ, hK ((adj.homEquiv _ _).symm φ) hM',
    Adjunction.homEquiv_unit, Functor.map_zero, Limits.comp_zero]

/-- **`Rf_!` preserves derived completeness.** For a principal ideal `I` of a domain `Λ` and
`f : X ⟶ Y` admitting a compactification, `Rf_!` carries objects of `D(X_ét, Λ)` that are
derived complete for `I` to derived complete objects of `D(Y_ét, Λ)`. For `Y = Spec k` this
says that `RΓ_c(X, K)` is derived complete. -/
theorem derivedComplete_rightDerivedLowerShriek {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] (K : 𝐃(X, Λ))
    (hK : DerivedCategory.derivedComplete X.smallEtaleTopology I K) :
    DerivedCategory.derivedComplete Y.smallEtaleTopology I
      ((R(f)_![ModuleCat.{u + 1} Λ]).obj K) :=
  -- Proof sketch: for the chosen compactification `f = g ∘ j`, with `j` an open immersion and
  -- `g` proper, `Rf_! = Rg_* j_!`, and `Rg_*` preserves derived completeness by
  -- `derivedComplete_rightDerivedLowerStar`. It remains to see that `j_! K` is derived
  -- complete. This is the non-formal step and it is open here: `j_!` is a left adjoint, so it
  -- commutes with `– ⊗ᴸ Λ/Iⁿ` (projection formula for `j`) but need not preserve the
  -- products in the Milnor triangle of `K`. A possible route is the triangle
  -- `j_! K → Rj_* K → i_* i^* Rj_* K` for the closed complement `i`: `Rj_* K` and `i_*` of a
  -- complete object are complete by the argument for `Rf_*`, so it suffices that `i^*`
  -- preserves completeness of `Rj_* K`. Should that fail, `Rf_!` on the adic category has to
  -- be defined as the derived completion of `Rg_* j_!`.
  sorry

/-- **The coefficient dual preserves derived completeness.** For a principal ideal `I` of a
domain `Λ` and a scheme `X` on which the constant complex `Λ_X` is derived complete for
`I`, the coefficient dual `K^∨ = RHom(K, Λ_X)` of an object `K` of `D(X_ét, Λ)` that is derived
complete for `I` is derived complete.

The hypothesis on `Λ_X` is not automatic: if `π₀(X)` is an infinite profinite space, the global
sections of `Λ_X` are the locally constant functions `π₀(X) → Λ`, whereas those of
`lim_n (Λ/Iⁿ)_X` are the continuous ones. -/
theorem derivedComplete_coefficientDual {X : Scheme.{u}}
    (hΛ : DerivedCategory.derivedComplete X.smallEtaleTopology I Λ_(X, Λ)) (K : 𝐃(X, Λ))
    (hK : DerivedCategory.derivedComplete X.smallEtaleTopology I K) :
    DerivedCategory.derivedComplete X.smallEtaleTopology I
      ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) X).obj (op K)) :=
  -- Proof sketch: `Λ_X` is the monoidal unit up to the isomorphism
  -- `DerivedCategory.εSingleFunctorZero`, and derived completeness is invariant under
  -- isomorphism. `RHom(K, –)` is triangulated and, being right adjoint to `K ⊗ᴸ –`, preserves
  -- products, so it carries the homotopy limit `Λ_X ⟶ Λ_X ⊗ᴸ Λ/Iⁿ` given by `hΛ` to a
  -- homotopy limit (`IsHomotopyLimit.map`). Since `Iⁿ = (πⁿ)` and `Λ/Iⁿ` is the
  -- cone of `πⁿ : Λ → Λ`, the triangulated `Λ`-linear functor `RHom(K, –)` satisfies
  -- `RHom(K, Λ_X ⊗ᴸ Λ/Iⁿ) ≅ RHom(K, Λ_X) ⊗ᴸ Λ/Iⁿ`, naturally in `n`; transporting the
  -- homotopy limit along these isomorphisms shows that `K^∨` is derived complete. The
  -- hypothesis `hK` is not needed by this argument.
  sorry

end General

section Integral

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Small.{u + 1} E] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E]

/-- Blueprint `sk-thm-transport`: Transport through the coefficient stages.

**`Rf_*` preserves derived completeness at the integral stage.** For `E` finite over `ℚ_ℓ` and
every morphism `f : X ⟶ Y`, `Rf_*` carries derived-complete objects of `D(X_ét, 𝒪_E)` to
derived-complete objects of `D(Y_ét, 𝒪_E)`. -/
theorem derivedCompleteIntegral_rightDerivedLowerStar {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : 𝐃(X, Shrink.{u + 1} (PadicAlgCl.integers l E)))
    (hK : DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E K) :
    DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E
      ((R((f)_*[ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))])).obj K) :=
  derivedComplete_rightDerivedLowerStar _ (PadicAlgCl.isPrincipal_maximalIdealShrink l E) f K hK

/-- Blueprint `sk-thm-transport`: Transport through the coefficient stages.

**`Rf_!` preserves derived completeness at the integral stage.** For `E` finite over `ℚ_ℓ` and
`f : X ⟶ Y` admitting a compactification, `Rf_!` carries derived-complete objects of
`D(X_ét, 𝒪_E)` to derived-complete objects of `D(Y_ét, 𝒪_E)`. For `Y = Spec k` this says that
`RΓ_c(X, K)` is an object of the adic category `D_comp(Spec k, 𝒪_E)`. -/
theorem derivedCompleteIntegral_rightDerivedLowerShriek {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] (K : 𝐃(X, Shrink.{u + 1} (PadicAlgCl.integers l E)))
    (hK : DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E K) :
    DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E
      ((R(f)_![ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))]).obj K) :=
  derivedComplete_rightDerivedLowerShriek _ (PadicAlgCl.isPrincipal_maximalIdealShrink l E) f K
    hK

/-- Blueprint `sk-thm-transport`: Transport through the coefficient stages.

**The dual at the integral stage.** For `E` finite over `ℚ_ℓ` and a scheme `X` on which the
constant complex `𝒪_E` is derived complete, the coefficient dual `K^∨ = RHom(K, 𝒪_E)` of a
derived-complete object of `D(X_ét, 𝒪_E)` is derived complete. -/
theorem derivedCompleteIntegral_coefficientDual {X : Scheme.{u}}
    (hΛ : DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E
      Λ_(X, Shrink.{u + 1} (PadicAlgCl.integers l E)))
    (K : 𝐃(X, Shrink.{u + 1} (PadicAlgCl.integers l E)))
    (hK : DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E K) :
    DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E
      ((DerivedCategory.coefficientDual
        (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))) X).obj (op K)) :=
  -- This is `derivedComplete_coefficientDual _ (PadicAlgCl.isPrincipal_maximalIdealShrink l E)
  -- hΛ K hK`, which elaborates but times out in the kernel: the statement here carries the ring
  -- instance `Shrink.instRing`, the instantiated general statement carries
  -- `CommRing.toRing Shrink.instCommRing`, and the two have to be unfolded against each other
  -- inside every monoidal and closed structure that `coefficientDual` depends on.
  sorry

end Integral

end Etale

end AlgebraicGeometry
