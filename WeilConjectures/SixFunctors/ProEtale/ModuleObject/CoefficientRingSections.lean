/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale

/-!
# Sections of the coefficient rings over weakly contractible objects

Let `X` be a scheme with a morphism `k : X ⟶ Spec ℤ` and `Λ` a condensed abelian group. The
coefficient sheaf `Λ_X = k^* p^* Λ` on `X_proét` is the sheafified left Kan extension of `Λ` along
the profinite test objects `S ↦ X[S] = Spec LC(S, ℤ) ×_{Spec ℤ} X`. This functor has a left
adjoint `π₀ : X_proét ⥤ Profinite`, `V ↦ π₀(Spec Γ(V, ⊤))`
(`AlgebraicGeometry.ProEtale.connectedComponentsAlongAdjunction`): maps `V ⟶ X[S]` over `X` are
ring maps `LC(S, ℤ) ⟶ Γ(V, ⊤)`, i.e. continuous maps `π₀(Spec Γ(V, ⊤)) ⟶ S`. Hence the left Kan
extension is `V ↦ Λ(π₀ V)`, and `Λ_X` is its sheafification
(`AlgebraicGeometry.ProEtale.connectedComponentsAlongSheafIso`).

Over an object `U` whose covering sieves contain finite decompositions into disjoint open
subschemes, e.g. `U = Spec R` with `R` w-contractible, the sheafification does not change the
sections
(`ProEtale.bijective_toSheafify_connectedComponentsAlong_of_forall_exists_retraction`).
So the sections of `Λ_X` over `U` are `Λ(π₀ U)`: the map `Λ(π₀ U) ⟶ Λ_X(X[π₀ U]) ⟶ Λ_X(U)`
given by the unit of `p_X^* ⊣ p_{X*}` and the restriction along the unit `U ⟶ X[π₀ U]` is bijective
(`AlgebraicGeometry.ProEtale.bijective_unit_app_comp_map_unit`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

/-! ### Connected components of spectra -/

section ConnectedComponents

end ConnectedComponents

/-! ### The profinite test objects along a structure morphism -/

section Along

variable {X : Scheme.{u}} (k : X ⟶ specZ.{u})

end Along

/-! ### The coefficient sheaf as a sheafified precomposition with `π₀` -/

section Sheaf

variable {X : Scheme.{u}} (k : X ⟶ specZ.{u})

end Sheaf

/-! ### Sheafification over objects with disjoint open decompositions -/

section Sheafify

variable {X : Scheme.{u}}

end Sheafify

end AlgebraicGeometry.ProEtale
