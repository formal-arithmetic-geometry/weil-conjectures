/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientCoefficients
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientResolutionNormalization
import all WeilConjectures.AlgebraicGeometry.BoundedConstructibleExtendScalars
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Full restriction along native coefficient quotients

Source: the principal quotient and finite local model steps of integral Hom reduction.
(blueprint: lem-sf-native-quotient-restriction-full). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace CategoryTheory.Mod

/-- Restriction along an epimorphism of ring objects is full.
Source: scalar descent in the principal quotient argument.
(blueprint: lem-sf-native-quotient-restriction-full).
Proof: precompose the required S-linearity equation with phi tensor M. This is
an epimorphism because tensor is a left adjoint. The result is R-linearity. -/
theorem full_comap_of_epi
    {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    {R S : C} [MonObj R] [MonObj S] (φ : R ⟶ S) [IsMonHom φ] [Epi φ] :
    (Mod.comap φ : Mod C S ⥤ Mod C R).Full where
  map_surjective {M N} f := by
    have hf := Mod.act_hom f
    have he : Epi (φ ▷ M.X) := by
      change Epi ((tensorRight M.X).map φ)
      infer_instance
    have hl : γ[S, M.X] ≫ f.hom = S ◁ f.hom ≫ γ[S, N.X] := by
      apply (cancel_epi (φ ▷ M.X)).mp
      change (φ ▷ M.X ≫ γ[S, M.X]) ≫ f.hom =
        R ◁ f.hom ≫ (φ ▷ N.X ≫ γ[S, N.X]) at hf
      rw [Category.assoc] at hf
      exact hf.trans (whisker_exchange_assoc φ
        (show M.X ⟶ N.X from f.hom) γ[S, N.X])
    exact ⟨Mod.homMk f.hom hl, rfl⟩

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale.IntegralQuotient
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- The actual integral reduction is an epimorphism after pullback to the scheme.
Source: the normalized principal resolution.
(blueprint: lem-sf-native-quotient-restriction-full).
Proof: the normalized coefficient sequence has its projection as a cokernel.
The exact forgetful functor sends this projection to the coefficient map. -/
theorem epi_coefficientMap_reduction (n : ℕ) :
    Epi (coefficientMap (reduction l E n) T) := by
  obtain ⟨_, _, _, _, _, hn⟩ :=
    (integral_quotient_resolution_normalization l E).2.2 T
  obtain ⟨_, ⟨h, ⟨hc⟩, _⟩, _⟩ := hn n
  have : Epi (projection l E T n) := epi_of_isColimit_cofork hc
  exact (Mod.forget _).map_epi (projection l E T n)

/-- The actual finite quotient map is an epimorphism after pullback.
Source: the normalized principal resolution and its quotient factorization.
(blueprint: lem-sf-native-quotient-restriction-full).
Proof: composing this map with the integral reduction gives the smaller
integral reduction, an epimorphism. Cancel its first factor. -/
theorem epi_coefficientMap_finiteMap (r n : ℕ) (h : n ≤ r) :
    Epi (coefficientMap (finiteMap l E r n h) T) := by
  have := epi_coefficientMap_reduction l E T n
  apply epi_of_epi_fac (f := coefficientMap (reduction l E r) T)
    (h := coefficientMap (reduction l E n) T)
  rw [← coefficientMap_comp, reduction_comp]

end AlgebraicGeometry.ProEtale.IntegralQuotient

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Constructibility is reflected by restriction along an epimorphism of ring objects.
Source: finite quotient scalar descent and preservation of finite presentations.
(blueprint: lem-sf-native-quotient-restriction-full).
Proof: scalar extension preserves local finite presentations on each stratum.
Since scalar restriction is fully faithful, the scalar-adjunction counit is an
isomorphism from extension of the restricted object back to the input. -/
theorem constructible_of_comap_of_epi
    (T : Scheme.{u})
    (R S : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [Epi φ]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) S)
    (hM : IsConstructibleModuleObject R ((Mod.comap φ).obj M)) :
    IsConstructibleModuleObject S M := by
  have := Mod.full_comap_of_epi φ
  exact _root_.constructible_of_iso
    (asIso ((Mod.extendRestrictAdjunction φ).counit.app M))
    (AlgebraicGeometry.ProEtale.constructible_extend R S φ hM)

end AlgebraicGeometry.ProEtale.CondensedRing
