/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ToPadicAlgClCompatibility
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekInterchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek
import WeilConjectures.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility

/-!

# Compatibility of `Rf^!` with `E ⟶ ℚ̄_ℓ`: (Push) for a proper morphism

Second part of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.UpperShriekCompatibility`
(see there): **(Push)** for a proper `g`, `Rg_*^E ⋙ T_Y ≅ T_Z ⋙ Rg_*^{ℚ̄_ℓ}`
(`ProEtale.CondensedRing.boundedConstructibleLowerStarToPadicAlgClIso`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-! ### (Push) for a proper morphism -/

section LowerStar

variable {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y) [IsProper g.left]

attribute [local irreducible] derivedPushHom in
-- The unused(-section)-variables linters walk the large elaborated derived-category terms (~50 s).
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- **(Push)** is an isomorphism on bounded constructible complexes, for the inclusion
`E ⟶ ℚ̄_ℓ` and a proper morphism `g`: the restriction of
`ProEtale.CondensedRing.derivedPushHom` to `Dᵇc(Z)⟦E⟧` is an isomorphism. The isomorphism on
all unbounded objects
(`ProEtale.CondensedRing.isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_of_isProper`)
needs the derived direct image to preserve coproducts, which fails in the ambient category
(`not_preservesColimitsOfShape_rightDerivedLowerStar_of_isAbelianVariety`); on bounded
constructible complexes only the copowers of an object of finite amplitude are involved: each
component is invertible by the bounded-below case
`ProEtale.CondensedRing.isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_app_of_isGE`. -/
theorem isIso_whiskerLeft_derivedPushHom_boundedConstructible :
    IsIso (Functor.whiskerLeft
      (boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) Z.left)).ι
      (derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) g.left)) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun K ↦ ?_
  have hK : DerivedCategory.TStructure.t.bounded K.obj := K.property.1
  obtain ⟨⟨N, hN⟩, -⟩ := hK
  have : K.obj.IsGE N := hN
  have h := isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_app_of_isGE ℓ g.left E K.obj N
  exact h

end LowerStar

end AlgebraicGeometry.ProEtale.CondensedRing
