/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.RestrictExtendScalarsColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ClosedImmersionExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ExtendScalarsConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.LisseDescentFiniteSubfield
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.SubfieldRestrictScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ConstructibleSheafDevissage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.HomFilteredColimitEllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicAlgClUnderived

/-!
# The uniform `Ext` bound for constructible `ℚ̄_ℓ`-sheaves, by dévissage

Blueprint `det-uniform-constructible-ext-rational`, coefficients `ℚ̄_ℓ`. Let `X` be a scheme with
noetherian underlying space. If, for every finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, constructible
`E_X`-modules satisfy the uniform `Ext` bound, so do constructible `ℚ̄_{ℓ,X}`-modules
(`ProEtale.hasUniformConstructibleExtBound_padicAlgClRingObj_of_padicSubfield`).

This proof does not use the 2-colimit description of `Dᵇc(X, ℚ̄_ℓ)`; instead both arguments of
`Hom(M[0], B[n])` are dévissé to the generators `Rc_* j_! Rc'_* L`, `L` lisse
(`ProEtale.CondensedRing.prop_singleFunctor_of_isConstructibleModuleObject`), which descend to
constructible sheaves `G` over finite subextensions by the descent of lisse sheaves
(`ProEtale.exists_iso_singleFunctor_extendScalars_of_lowerShriek`). The classes of objects with a
uniform vanishing are closed under extensions, so it remains to treat
`Hom((ℚ̄_ℓ ⊗ M)[0], (ℚ̄_ℓ ⊗ G)[n])` for constructible `K_X`-modules `M` and `G`: by adjunction this
is `Hom(M[0], Res(ℚ̄_ℓ ⊗ G)[n])`, and `Res(ℚ̄_ℓ ⊗ G) = colim_{F ⊇ K} Res(F ⊗ G)` is a filtered
colimit of constructible `K_X`-modules
(`CategoryTheory.Mod.isColimitRestrictExtendScalarsColimitCocone`), out of which `Hom(M[0], -[n])`
commutes (`homCommutesWithFilteredColimits_singleFunctor_of_isConstructibleModuleObject`)
(`ProEtale.eq_zero_of_singleFunctor_extendScalars_padicSubfieldRingObjToPadicAlgCl`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

open CondensedRing

section Adjunction

variable {X : Scheme.{u}} {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
  [IsCommMonObj R] [MonObj S] [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ]
  [PreservesFiniteLimits (Mod.extendScalars φ)]

end Adjunction

variable (ℓ : ℕ) [Fact ℓ.Prime]

namespace CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

end CondensedRing

end AlgebraicGeometry.ProEtale

