/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.StrictlyHenselianTrait
public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.ProperBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerStarFullyFaithful
public import WeilConjectures.Compactification.Defs
import WeilConjectures.Tactic.ExactModProofs

/-!

# Reduction of the change of trait to proper models

Let `ι : R₁ ⟶ R₂` be a ring map with compatible maps `aᵢ : Rᵢ ⟶ Ωᵢ` (`c ∘ a₁ = a₂ ∘ ι`) and
`bᵢ : Rᵢ ⟶ κᵢ` (`d ∘ b₁ = b₂ ∘ ι`), let `N` be a model over `Spec R₁` along `q₁` (with cartesian
squares of geometric generic and special fibres), `M` its base change to `Spec R₂` and
`φ : M ⟶ N` the morphism of models (the situation of SGA 4½, [Th. finitude], Prop. 3.7).

A scheme `Z` over `Spec R₁` along `q` is a model of its geometric generic fibre `Z ×_{R₁} Ω₁` with
special fibre `Z ×_{R₁} κ₁` (`NearbyCyclesModel.ofOverTrait`); a morphism over `Spec ι` induces a
morphism of such models (`NearbyCyclesModel.ofOverTraitHom`). For a compactification
`c = (N.total ⟶[c.i] c.Z ⟶[c.g] Spec R₁)` of `q₁` (Nagata), the compactified model
`N̄ = ofOverTrait a₁ b₁ c.g` is proper over `Spec R₁`, its base change
`M̄ = ofOverTrait a₂ b₂ (c.Z ×_{R₁} Spec R₂ ⟶ Spec R₂)` maps to it by
`φ̄ = NearbyCyclesModel.compactificationHom`, and `N`, `M` are open in `N̄`, `M̄`
(`NearbyCyclesModel.Hom.toOfOverTrait`).

**Reduction to proper models.** If the pullback exchange of `φ̄` is invertible at every complex
bounded below of étale origin, so is that of `φ`
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_compactification`). Indeed nearby cycles
commute with open restriction (`NearbyCyclesModel.Hom.isIso_pullbackExchange_of_isOpenImmersion`),
so by the square law of the pullback exchanges the exchange of `φ` at `Lu^* L` is invertible if
that of `φ̄` at `L` is (`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_upperStar_of_square`); and
every `K` is `Lu^* Ru_* K` for the open immersion `u` of the geometric generic fibres, `Ru_* K`
being again of étale origin. This is the reduction to (pro)jective models at the start of the
proof of loc. cit., Prop. 3.7, with Nagata's compactification instead of a projective closure and
the direct image instead of the extension by zero.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

/-! ### The pullback exchange through a square with invertible sides -/

section Square

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' X₁ X₁' Z Z' Z₁ Z₁' : Scheme.{u}} {M : NearbyCyclesModel X X'}
  {M₁ : NearbyCyclesModel X₁ X₁'} {P : NearbyCyclesModel Z Z'} {P₁ : NearbyCyclesModel Z₁ Z₁'}
  {f₀ : Z ⟶ X} {f₀' : Z' ⟶ X'} {g : X ⟶ X₁} {g' : X' ⟶ X₁'} {k : Z ⟶ Z₁} {k' : Z' ⟶ Z₁'}
  {e : Z₁ ⟶ X₁} {e' : Z₁' ⟶ X₁'}

end Square

/-! ### Models given by the fibres of a scheme over a trait -/

section OverTrait

variable {R Ω κ : Type u} [CommRing R] [CommRing Ω] [CommRing κ]

variable {R₁ R₂ Ω₁ Ω₂ κ₁ κ₂ : Type u} [CommRing R₁] [CommRing R₂] [CommRing Ω₁] [CommRing Ω₂]
  [CommRing κ₁] [CommRing κ₂]

end OverTrait

/-! ### Reduction to proper models -/

section Compactification

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T] {R₁ R₂ Ω₁ Ω₂ κ₁ κ₂ : Type u} [CommRing R₁] [CommRing R₂] [CommRing Ω₁]
  [CommRing Ω₂] [CommRing κ₁] [CommRing κ₂] {a₁ : R₁ →+* Ω₁} {b₁ : R₁ →+* κ₁} {a₂ : R₂ →+* Ω₂}
  {b₂ : R₂ →+* κ₂} {ι : R₁ →+* R₂} {c : Ω₁ →+* Ω₂} {d : κ₁ →+* κ₂}
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}

end Compactification

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
