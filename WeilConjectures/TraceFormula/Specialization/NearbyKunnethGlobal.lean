/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.KunnethGeneric
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethProper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar
public import WeilConjectures.TraceFormula.Specialization.NearbyProperExchange
public import WeilConjectures.TraceFormula.OrdinaryKunnethGlobalSections
public import WeilConjectures.TraceFormula.Specialization.TraitProduct
public import WeilConjectures.Tactic.ExactModProofs

/-!

# Gabber's Künneth formula for nearby cycles: global sections

Let `M`, `N` be models of finite type over the henselian trait `S = Spec k'⟦t⟧`
over an arbitrary field `k'` along proper structure morphisms `q_M`, `q_N`, and let `P` be their
product over the trait. This file proves the global-sections step (blueprint
`sk-prop-tf-nearby-external-kunneth`, equation (4)) of Illusie's proof of Gabber's Künneth
formula: the direct image `R(a_{P_s})_* Π_{A,B}` of the Künneth map of nearby cycles to the
point `Spec k'` is an isomorphism
(`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.isIso_lowerStar_kunnethMap`).
Equivalently, the cone of `Π_{A,B}` has no global sections.

## Proof

After passing to the models of the geometric generic fibres
(`NearbyCyclesModel.isIso_map_kunnethMap_iff_toGeneric`), the structure morphisms are morphisms
of models `ψ : M ⟶ T` to the trait `T` as a model of its geometric generic point
(`NearbyCyclesModel.traitGenericModel`). The compatibility of the Künneth map with direct
images (blueprint `det-nearby-kunneth-proper`,
`NearbyCyclesModel.kunnethMap_comp_pushforwardExchange`) identifies `R(a_{P_s})_* Π_{A,B}`, up
to
* the proper exchanges `χ_ψ` (blueprint `det-sp-nearby-cycles-exchanges` (2),
  `NearbyCyclesModel.IsTraitModelOver.isIso_pushforwardExchange_toTraitGeneric_app`),
* the ordinary Künneth isomorphism `RΓ(X_s) ⊗ RΓ(Y_s) ≅ RΓ(X_s × Y_s)` over `k'` (blueprint
  `sk-lem-sf-kunneth-star`, `ProEtale.CondensedRing.isIso_lowerStarKunnethMap'_of_isPullback`),

with the Künneth map of the trait `T` at `(RΓ(X_η̄, A), RΓ(Y_η̄, B))` followed by the nearby cycles
of the ordinary Künneth isomorphism on the geometric generic fibres; the former is an isomorphism
because the nearby cycles of the trait are monoidal on bounded constructible complexes on the
geometric generic point; this last input is a hypothesis of
`NearbyCyclesModel.isIso_lowerStar_kunnethMap`, supplied for `ℚ̄_ℓ`-coefficients by
`NearbyCyclesModel.isIso_kunnethMap_traitGenericModel_of_shiftDecomposition`
(`WeilConjectures.TraceFormula.Specialization.TraitNearbyMonoidal`).

## Implementation notes

The statements of the `ℚ̄_ℓ` inputs carry different `Precoherent Profinite` proofs (auxiliary proof
constants and the synthesized instance) inside the `MonObj` instances of `ℚ̄_ℓ`; comparing them
makes the unifier and the kernel unfold the derived categories. The inputs are therefore applied
with `exact_mod_proofs`, which identifies these proofs by casts.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

/-! ### The trait as a model of its geometric generic point -/

section TraitGeneric

variable (k' : Type u) [Field k']

variable {k'}

variable {X : Scheme.{u}} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

end TraitGeneric

end NearbyCyclesModel

/-! ### Fibres of a product over the trait -/

section Pasting

variable {C : Type*} [Category C] {Pt Mt Nt S Z X Y s : C} {φ₁ : Pt ⟶ Mt} {φ₂ : Pt ⟶ Nt}
  {qM : Mt ⟶ S} {qN : Nt ⟶ S} {iP : Z ⟶ Pt} {iM : X ⟶ Mt} {iN : Y ⟶ Nt} {hX : X ⟶ s}
  {hY : Y ⟶ s} {hZ : Z ⟶ s} {c : s ⟶ S} {f₁ : Z ⟶ X} {f₂ : Z ⟶ Y}

end Pasting

namespace NearbyCyclesModel

section Product

variable {k' : Type u} [Field k'] {X Y Z : Scheme.{u}} {X' Y' Z' : Over (Spec (.of k'))}
  {M : NearbyCyclesModel X X'.left} {N : NearbyCyclesModel Y Y'.left}
  {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X} {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y}
  {f₂' : Z'.left ⟶ Y'.left} {φ₁ : P.Hom M f₁ f₁'} {φ₂ : P.Hom N f₂ f₂'}
  {qM : M.total ⟶ trait k'} {gM : M.generic ⟶ Spec (.of (traitGenericField k'))}
  {qN : N.total ⟶ trait k'} {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}

end Product

/-! ### The proper exchange and the nearby cycles of the trait -/

section Exchange

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k'] [Fact (ringChar k' ≠ ℓ)] {X : Scheme.{u}}
  {X' : Over (Spec (.of k'))}
  {M : NearbyCyclesModel X X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

end Exchange

/-! ### Transport along pullbacks, for general coefficients -/

section Transport

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

variable {X Y Z X' Y' Z' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {P : NearbyCyclesModel Z Z'} {f₁ : Z ⟶ X} {f₁' : Z' ⟶ X'} {f₂ : Z ⟶ Y} {f₂' : Z' ⟶ Y'}

end Transport

/-! ### The global-sections step, for general coefficients -/

section GlobalAbstract

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {k' : Type u} [Field k'] {X Y Z : Scheme.{u}} {X' Y' Z' : Over (Spec (.of k'))}
  {M : NearbyCyclesModel X X'.left} {N : NearbyCyclesModel Y Y'.left}
  {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X} {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y}
  {f₂' : Z'.left ⟶ Y'.left} {φ₁ : P.Hom M f₁ f₁'} {φ₂ : P.Hom N f₂ f₂'}
  {qM : M.total ⟶ trait k'} {gM : M.generic ⟶ Spec (.of (traitGenericField k'))}
  {qN : N.total ⟶ trait k'} {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}

end GlobalAbstract

/-! ### The global-sections step -/

section TraitGenericField

variable (ℓ : ℕ) {k' : Type u} [Field k']

end TraitGenericField

section Global

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

variable {X Y Z : Scheme.{u}} {X' Y' Z' : Over (Spec (.of k'))}
  {M : NearbyCyclesModel X X'.left} {N : NearbyCyclesModel Y Y'.left}
  {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X} {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y}
  {f₂' : Z'.left ⟶ Y'.left} {φ₁ : P.Hom M f₁ f₁'} {φ₂ : P.Hom N f₂ f₂'}
  {qM : M.total ⟶ trait k'} {gM : M.generic ⟶ Spec (.of (traitGenericField k'))}
  {qN : N.total ⟶ trait k'} {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}

end Global

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
