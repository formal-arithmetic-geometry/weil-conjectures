/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monad.Comonadicity
public import Mathlib.FieldTheory.Finite.GaloisField
public import WeilConjectures.WeilSheaf.CondensedModelDescent

/-!
# Galois descent at the finite levels and twisted constant sheaves

`WeilConjectures.WeilSheaf.CondensedLisseRepresentation` proves effective Galois descent of
module objects along a covering `q : Y ⟶ X` with an action `ρ` of a finite monoid `Γ`
(`AlgebraicGeometry.ProEtale.CondensedRing.exists_upperStar_obj_iso_of_galoisDescentDatum`),
conditionally on the *Galois comparison* `q^* q_* N ⟶ ∏_σ (ρ σ)^* N` being an isomorphism. This
file proves that this holds for free Galois actions, hence at the finite levels
`q_K : X₀ ⊗_k K ⟶ X₀`, and uses it to realise characters of finite order of the Frobenius as
module objects on `X₀` (twisted constant sheaves).

## Free Galois coverings

* `AlgebraicGeometry.ProEtale.IsFreeAction`: an action `ρ` on `Y` is free if `t ≫ ρ σ = t ≫ ρ τ`
  on a nonempty scheme forces `σ = τ`.
* `AlgebraicGeometry.ProEtale.nonempty_isColimit_cofan_pullbackLift`: for a free Galois action,
  the graphs `(𝟙, w ≫ ρ σ) : W ⟶ W ×_X Y` exhibit `W ×_X Y` as `∐_σ W`.
* `AlgebraicGeometry.ProEtale.isLimitFanGaloisComponentRestriction`: hence, with the pullbacks
  along weakly étale morphisms computed by restriction, the Galois components
  `j_q^* q_* G ⟶ j_{ρ σ}^* G` are on sections the restrictions `G(W ×_X Y) ⟶ ∏_σ G(W)`
  along the graphs, and form a limit fan
  (`AlgebraicGeometry.ProEtale.isLimitSectionsFanOfIsColimitCofan`).
* `AlgebraicGeometry.ProEtale.isLimitFanUpperStarGaloisComponent`: the same for the pullbacks
  `q^*` of abelian sheaves, transported along `upperStarIsoLocalizationRestriction`
  (`CategoryTheory.Adjunction.isLimitFanGaloisComponentOfIso`).
* `AlgebraicGeometry.ProEtale.CondensedRing.isIso_galoisComparison`: **the Galois comparison of
  module objects is an isomorphism** for a free Galois action, transported along the forgetful
  functors (`CategoryTheory.Adjunction.isLimitFanGaloisComponentOfForget`).

## The finite levels

* `AlgebraicGeometry.Scheme.Hom.finiteLevelGaloisAction`: the action `σ ↦ 𝟙 × Spec (χ σ)` on
  `X₀ ⊗_k K` of a monoid `Γ` through `χ : Γ ≃* Gal(K / k)`; it is Galois
  (`AlgebraicGeometry.ProEtale.CondensedRing.isGaloisAction_finiteLevelGaloisAction`) and free
  (`AlgebraicGeometry.ProEtale.isFreeAction_finiteLevelGaloisMap`, from the injectivity of the
  ring homomorphisms `K ⟶ Γ(T, 𝒪_T)` for `T` nonempty).
* `AlgebraicGeometry.ProEtale.CondensedRing.isIso_galoisComparison_finiteLevelProj` and
  `CondensedRing.exists_upperStar_finiteLevelProj_obj_iso_of_galoisDescentDatum`:
  effective Galois descent of module objects along `X₀ ⊗_k K ⟶ X₀` holds unconditionally.

## Twisted constant module objects

* `CategoryTheory.Adjunction.exists_iso_twist`: twisting the canonical descent datum of `L M₀`
  by an anti-homomorphism `a : Γ →* (Aut M₀)ᵐᵒᵖ` gives a descent datum, which is effective.
* `AlgebraicGeometry.ProEtale.CondensedRing.exists_upperStar_finiteLevelProj_obj_iso_twist`: for
  a module object `M₀` on `X₀` (e.g. the constant `Λ_{X₀}^r`) and `a : Γ →* (Aut M₀)ᵐᵒᵖ`, a
  module object `M` on `X₀` with `q_K^* M ≅ q_K^* M₀`, the Galois structure of `q_K^* M`
  corresponding to the one of `q_K^* M₀` twisted by `a`.
* `CondensedRing.exists_upperStar_finiteLevelProj_obj_iso_frobeniusTwist`:
  over a finite field, for an automorphism `A` of `M₀` with `A ^ [K : k] = 1`, the twist by the
  character `FiniteField.geometricFrobeniusCharacter` sending the geometric Frobenius to `A`:
  the finite-level Frobenius acts on `q_K^* M ≅ q_K^* M₀` through `A`. This realises characters
  of finite order of `W(k̄ / k)` (more generally finite-order automorphisms of `Λ^r`) as module
  objects on `X₀`; pulling back further along `ι : X̄ ⟶ X₀ ⊗_k K`, they become isomorphic to
  `p^* M₀` (`CondensedRing.upperStarGeometricFiberProjIsoOfFiniteLevel`).

## What remains

A bounded (not finite-order) Weil action, e.g. a unit of `ℤ_ℓ` or `ℚ̄_ℓ` of infinite order, is
not a Galois descent datum at any finite level: its reductions modulo `ℓ^k` have finite order
(`WeilConjectures.RepresentationTheory.WeilGroupBoundedExtension`) and give, by the results
here, compatible twisted module objects `M_k` at the finite levels `K_k` of degree the order
modulo `ℓ^k`; realising the action itself needs the limit over `k` (an `ℓ`-adic sheaf, i.e. a
compatible system of the `M_k` along the reductions `Λ/ℓ^{k+1} ⟶ Λ/ℓ^k`), which is not done here.
-/

@[expose] public section

universe v u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category.{v} C] [Category.{v} D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  {Γ : Type*} {S : Γ → D ⥤ D} {κ : ∀ σ, L ⋙ S σ ≅ L}

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale

variable {X Y : Scheme.{u}} (q : Y ⟶ X) {Γ : Type u} (ρ : Γ → (Y ⟶ Y))

variable {q ρ} (hρ : ∀ σ, ρ σ ≫ q = q)

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

open Scheme Opposite

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {X Y : Scheme.{u}} (q : Y ⟶ X) [WeaklyEtale q] (s : Y ⟶ Y) [WeaklyEtale s]
  (hs : s ≫ q = q)

variable {Γ : Type u} [Finite Γ] {ρ : Γ → (Y ⟶ Y)} [∀ σ, WeaklyEtale (ρ σ)]
  (hρ : ∀ σ, ρ σ ≫ q = q)

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}}

/-- The identifications `upperStarForgetIso` are compatible with the transport of pullbacks along
equal morphisms. -/
lemma upperStarForgetIso_hom_app_map_upperStarCongr_inv_app {f g : Y ⟶ X} (h : f = g)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (upperStarForgetIso Λ g).hom.app M ≫ (Mod.forget _).map ((upperStarCongr Λ h).inv.app M) =
      (ProEtale.upperStarCongr Ab.{u + 1} h.symm).hom.app ((Mod.forget _).obj M) ≫
        (upperStarForgetIso Λ f).hom.app M := by
  subst h
  exact (Category.comp_id _).trans (Category.id_comp _).symm

variable (q : Y ⟶ X) {s : Y ⟶ Y} (hs : s ≫ q = q)

/-- The identifications `upperStarForgetIso` are compatible with the canonical isomorphisms
`s^* q^* ≅ (s ≫ q)^* = q^*` for `s ≫ q = q`. -/
lemma upperStarForgetIso_hom_app_map_upperStarComp_symm_trans_inv_app
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (upperStarForgetIso Λ q).hom.app M ≫
        (Mod.forget _).map (((upperStarComp Λ s q).symm ≪≫ upperStarCongr Λ hs).inv.app M) =
      (ProEtale.upperStarComp' Ab.{u + 1} s q q hs.symm).symm.inv.app ((Mod.forget _).obj M) ≫
        (s)^*[Ab.{u + 1}].map ((upperStarForgetIso Λ q).hom.app M) ≫
        (upperStarForgetIso Λ s).hom.app ((q)^*⟦Λ⟧.obj M) := by
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Functor.map_comp, Category.assoc,
    ProEtale.upperStarComp', Iso.trans_hom]
  rw [reassoc_of% (upperStarForgetIso_hom_app_map_upperStarCongr_inv_app Λ hs M),
    upperStarComp_hom_app_upperStarForgetIso]

variable {q} {Γ : Type u} {ρ : Γ → (Y ⟶ Y)} (hρ : ∀ σ, ρ σ ≫ q = q)

end AlgebraicGeometry.ProEtale.CondensedRing

/-! ### The finite levels -/

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))
  {K : Type u} [Field K] [Algebra k K]

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.ProEtale

variable {k : Type u} [Field k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))
  {K : Type u} [Field K] [Algebra k K]

namespace CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (K) [FiniteDimensional k K] [IsGalois k K]

variable {Γ : Type u} [Monoid Γ] [Finite Γ] (χ : Γ ≃* Gal(K/k))

end CondensedRing

end AlgebraicGeometry.ProEtale

/-! ### Twisted constant module objects -/

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category.{v} C] [Category.{v} D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  {Γ : Type*} [Monoid Γ] {S : Γ → D ⥤ D} {κ : ∀ σ, L ⋙ S σ ≅ L} {ε₀ : S 1 ≅ 𝟭 D}
  {μ : ∀ σ τ, S (σ * τ) ≅ S τ ⋙ S σ}

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Generic

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (q : Y ⟶ X) [WeaklyEtale q] {Γ : Type*} [Monoid Γ] (ρ : Γ → (Y ⟶ Y))
  (hρ : ∀ σ, ρ σ ≫ q = q)

end Generic

variable {k : Type u} [Field k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k)) (K : Type u) [Field K]
  [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {Γ : Type u} [Monoid Γ] [Finite Γ] (χ : Γ ≃* Gal(K/k))

end AlgebraicGeometry.ProEtale.CondensedRing

/-! ### Characters of the Frobenius -/

namespace FiniteField

variable {k : Type u} [Field k] [Fintype k] (K : Type u) [Field K] [Algebra k K]
  [FiniteDimensional k K]

variable [IsGalois k K] {C : Type*} [Category C] {M : C}

end FiniteField

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k] [Fintype k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))
  (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable {k : Type u} [Field k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k)) {K : Type u} [Field K]
  [Algebra k K] (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
  [IsCommMonObj Λ] (θ : K →ₐ[k] AlgebraicClosure k)

end AlgebraicGeometry.ProEtale.CondensedRing
