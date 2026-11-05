/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monad.Comonadicity
public import WeilConjectures.WeilSheaf.CondensedModelFiniteLevel

/-!
# Effective descent of objects along pro-étale coverings and Galois descent data

To realise a representation of the arithmetic fundamental group (or a Weil sheaf on the geometric
fibre `X̄`) as a lisse `ℚ̲̄_ℓ`-sheaf on the model `X₀` in the condensed model, one has to descend
*objects* along the coverings `X₀ ⊗_k K ⟶ X₀` and `X̄ ⟶ X₀`; descent of *morphisms* is
`WeilConjectures.WeilSheaf.CondensedModelDescent`. This file supplies the object-level tools.

## Effective descent (Beck)

* `CategoryTheory.Comonad.comonadicOfFaithfulOfPreservesFiniteLimits`,
  `CategoryTheory.Comonad.isEquivalence_comparison_of_faithful_of_preservesFiniteLimits`: a faithful
  left exact left adjoint out of an abelian category is comonadic; explicitly
  (`CategoryTheory.Comonad.isIso_map_equalizerι_comp_counit`) a coalgebra `(N, δ)` is `F M` for the
  equalizer `M` of `G δ, η_{G N} : G N ⇉ G F G N`.
* `AlgebraicGeometry.ProEtale.isEquivalence_comparison_upperStarLowerStarAdjunction_ab` and
  `AlgebraicGeometry.ProEtale.CondensedRing.isEquivalence_comparison_upperStarLowerStarAdjunction`:
  for a quasi-compact surjective weakly étale `q : Y ⟶ X`, abelian sheaves, resp. module objects
  over a condensed ring `Λ`, on `X` are equivalent to coalgebras over `q^* q_*`; in object form
  `AlgebraicGeometry.ProEtale.CondensedRing.exists_upperStar_obj_iso_of_coalgebra`. This applies to
  the geometric fibre `X̄ ⟶ X₀` (`isEquivalence_comparison_geometricFiberProj`) and to the finite
  levels `X₀ ⊗_k K ⟶ X₀` (`isEquivalence_comparison_finiteLevelProj`).

## Galois descent data

For `L ⊣ R` and endofunctors `S σ` (`σ` in a monoid `Γ`) with `κ σ : L ⋙ S σ ≅ L`
(`L = q^*`, `S σ = (ρ σ)^*` for an action `ρ` of `Γ` on `Y` over `X`), a *Galois descent datum* on
`N` is a family `ψ σ : N ⟶ S σ N`, trivial at `1` and satisfying the cocycle condition
(`CategoryTheory.Adjunction.IsGaloisDescentDatum`). The *Galois comparison*
`L R N ⟶ ∏_σ S σ N` (`CategoryTheory.Adjunction.galoisComparison`) has components `(κ σ)⁻¹` followed
by `S σ` of the counit.

* `CategoryTheory.Adjunction.galoisCoalgebra`: if the Galois comparisons of `N` and `L R N` are
  isomorphisms, a Galois descent datum on `N` is a coalgebra structure over `L ⋙ R`.
* `CategoryTheory.Adjunction.exists_iso_of_isGaloisDescentDatum`: combined with Beck's theorem, the
  datum is then effective, `N ≅ L M` compatibly with the data.
* `AlgebraicGeometry.ProEtale.CondensedRing.exists_upperStar_obj_iso_of_galoisDescentDatum`: the
  case of module objects over `Λ` along `q`, for an action `ρ` of a finite monoid `Γ` on `Y` over
  `X`, with the coherences of the canonical isomorphisms `(ρ σ)^* q^* ≅ q^*`
  (`AlgebraicGeometry.ProEtale.CondensedRing.upperStarComp_inv_app_upperStarCongr_hom_app_of_eq_id`
  and its multiplicative analogue `…_of_eq_comp`).

## What remains

The hypothesis of the last theorem that the Galois comparison `q^* q_* N ⟶ ∏_σ (ρ σ)^* N` is an
isomorphism is the geometric input `Y ×_X Y ≅ ∐_σ Y` of a finite Galois covering: on the sections
over `W ⟶ Y` it is the restriction `N(W ×_X Y) ⟶ ∏_σ N(W)` along the graphs `(𝟙, ρ σ)`, which is
bijective when these graphs form a disjoint open covering
(`AlgebraicGeometry.ProEtale.isLimitSectionsFanOfIsColimitCofan`), i.e. for a free
`AlgebraicGeometry.ProEtale.IsGaloisAction`. It is not proved here.
-/

@[expose] public section

universe v u' u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace CategoryTheory.Comonad

variable {C : Type u'} {D : Type*} [Category.{v} C] [Category.{v} D] [Abelian C]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Faithful] [PreservesFiniteLimits F]

end CategoryTheory.Comonad

/-! ### Effective descent along pro-étale coverings -/

namespace AlgebraicGeometry.ProEtale

variable {X Y : Scheme.{u}} (q : Y ⟶ X) [WeaklyEtale q] [Surjective q] [QuasiCompact q]

namespace CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

variable {k : Type u} [Field k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))

end CondensedRing

end AlgebraicGeometry.ProEtale

/-! ### Galois descent data and coalgebras -/

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category.{v} C] [Category.{v} D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  {Γ : Type*} (S : Γ → D ⥤ D) (κ : ∀ σ, L ⋙ S σ ≅ L)

variable [Monoid Γ] (ε₀ : S 1 ≅ 𝟭 D) (μ : ∀ σ τ, S (σ * τ) ≅ S τ ⋙ S σ)

variable {S κ ε₀ μ}

variable [HasLimitsOfShape (Discrete Γ) D]

end CategoryTheory.Adjunction

/-! ### Galois descent of module objects -/

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (q : Y ⟶ X)

variable [WeaklyEtale q] {Γ : Type*} [Monoid Γ] (ρ : Γ → (Y ⟶ Y)) (hρ : ∀ σ, ρ σ ≫ q = q)

end AlgebraicGeometry.ProEtale.CondensedRing
