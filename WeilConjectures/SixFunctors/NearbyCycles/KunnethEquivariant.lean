/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.AutAction
public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeId
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalCompDerived

/-!

# Equivariance of the Künneth map of nearby cycles

Let `φ₁ : P ⟶ M` and `φ₂ : P ⟶ N` be morphisms of models, and let `σ_M`, `σ_N`, `σ_P` be
morphisms of models over the identities (for instance automorphisms of the geometric generic
fibres over the generic point of the trait) compatible with `φ₁` and `φ₂`. Then the Künneth map
`Π_{A,B} : Lf₁'^* Ψ_M A ⊗ Lf₂'^* Ψ_N B ⟶ Ψ_P (Lf₁^* A ⊗ Lf₂^* B)` is equivariant for the actions
`NearbyCyclesModel.Hom.autAction` of `σ_M`, `σ_N` on the source and of `σ_P` on the target
(`NearbyCyclesModel.kunnethMap_autAction`).

This is the compatibility of the Künneth map with pullbacks
(`NearbyCyclesModel.map_kunnethMap_comp_pullbackExchange`) for the identities, transported along
the identity isomorphisms `L(𝟙)^* ≅ 𝟭`, which are monoidal
(`ProEtale.CondensedRing.leftDerivedUpperStarTensor_id`) and compatible with the pullback
comparisons of the squares with identity sides
(`ProEtale.CondensedRing.pullbackSquareComparison_hom_app_id_right`).

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

namespace NearbyCyclesModel

/-! ### Abstract computation -/

section Abstract

variable {S D : Type*} [Category S] [MonoidalCategory S] [Category D]

variable {CM CN CP SM SN SP : Type*} [Category CM] [Category CN] [Category CP] [Category SM]
  [Category SN] [Category SP] [MonoidalCategory CP] [MonoidalCategory SP]
  {ΨM : CM ⥤ SM} {ΨN : CN ⥤ SN} {ΨP : CP ⥤ SP} {g₁ : CM ⥤ CP} {g₂ : CN ⥤ CP}
  {s₁ : SM ⥤ SP} {s₂ : SN ⥤ SP}

end Abstract

variable {X X' Y Y' Z Z' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {P : NearbyCyclesModel Z Z'} {f₁ : Z ⟶ X} {f₁' : Z' ⟶ X'} {f₂ : Z ⟶ Y} {f₂' : Z' ⟶ Y'}

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
