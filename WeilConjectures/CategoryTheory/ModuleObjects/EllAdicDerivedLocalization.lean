/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!

# Inverting `ℓ` on the full derived categories of `𝒪_E`- and `E`-modules

Let `X` be a scheme, `ℓ` a prime and `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ`, and let
`φ : 𝒪_{E,X} ⟶ E_X` be the inclusion of coefficient ring objects on `X_proét`
(`ProEtale.padicIntegersToPadicSubfield`). This file shows that the derived extension of
scalars
```
E ⊗ᴸ_{𝒪_E} - = L(extendScalars φ) : D(Mod_{𝒪_{E,X}}) ⥤ D(Mod_{E_X})
```
identifies `D(Mod_{E_X})` with the Verdier quotient of `D(Mod_{𝒪_{E,X}})` by the complexes `K`
with `E_X ⊗_{𝒪_{E,X}} Hᵠ(K) = 0` for all `q` (`ProEtale.rationallyAcyclic`): it is a
localization functor with respect to the morphisms whose mapping cone is such a complex
(`ProEtale.isLocalization_derivedExtendScalars`).

## Implementation details

Since `E_X` is defined by its sections and not as `𝒪_{E,X}[1/ℓ]`, the condition
"`Hᵠ(K)[1/ℓ] = 0`" is expressed as the vanishing of `E_X ⊗_{𝒪_{E,X}} Hᵠ(K)`; the two agree
since `E_X ⊗_{𝒪_{E,X}} M = colim(M --ℓ--> M --ℓ--> ⋯)`
(`CategoryTheory.Mod.isColimitExtendScalarsCocone`).

The proof follows the adjunction `E ⊗_{𝒪_E} - ⊣ comap φ`. Extension of scalars along `φ` is
exact (`ProEtale.preservesFiniteLimits_extendScalars_padicIntegersToPadicSubfield`), so both
functors derive levelwise, and the counit `E_X ⊗_{𝒪_{E,X}} N ⟶ N` is an isomorphism for every
`E_X`-module `N` (`CategoryTheory.Mod.isIso_extendRestrictAdjunction_counit`). Hence the derived
restriction of scalars is fully faithful, so that its left adjoint is the localization at the
morphisms it inverts (`CategoryTheory.Adjunction.isLocalization`), and these are the morphisms
whose cone has all `E_X ⊗ Hᵠ` zero, the levelwise derived functor being triangulated and
commuting with cohomology.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Pretriangulated

namespace AlgebraicGeometry.ProEtale

open Scheme

open scoped CondensedRing CategoryTheory.Obj

attribute [local irreducible] Mod.extendScalars CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- The counit `E_X ⊗_{𝒪_{E,X}} N ⟶ N` of extension and restriction of scalars along the
inclusion `𝒪_{E,X} ⟶ E_X` is an isomorphism for every `E_X`-module `N`. -/
instance isIso_extendRestrictAdjunction_counit_padicIntegersToPadicSubfield :
    IsIso (Mod.extendRestrictAdjunction (padicIntegersToPadicSubfield X ℓ E)).counit := by
  have adj : upperStarFromPoint X ⊣ _ := pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  have : (upperStarFromPoint X).IsLeftAdjoint := adj.isLeftAdjoint
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint (upperStarFromPoint X)
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    adj.leftAdjoint_preservesColimits
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (upperStarFromPoint X)
  have := Functor.additive_of_preservesBinaryBiproducts (upperStarFromPoint X)
  exact Mod.isIso_extendRestrictAdjunction_counit _
    (Mod.isColimitSmulSequenceCoconeMap (upperStarFromPoint X) _
      (Profinite.isColimitPadicIntegersRingObjSmulSequenceCocone ℓ E))
    (by rw [Profinite.padicIntegersRingObjToContinuousMapRingObjInvPow_zero])

/-- The complexes `K` of `𝒪_{E,X}`-modules all of whose cohomology sheaves are killed by
inverting `ℓ`: `E_X ⊗_{𝒪_{E,X}} Hᵠ(K) = 0` for all `q`. -/
def rationallyAcyclic :
    ObjectProperty (DerivedCategory
      (CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) :=
  fun K ↦ ∀ q : ℤ, IsZero ((Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).obj
    ((DerivedCategory.homologyFunctor _ q).obj K))

instance : (rationallyAcyclic X ℓ E).IsClosedUnderIsomorphisms where
  of_iso e hK q := (hK q).of_iso
    ((Mod.extendScalars _).mapIso ((DerivedCategory.homologyFunctor _ q).mapIso e)).symm

/-- The derived extension of scalars `E ⊗ᴸ_{𝒪_E} - : D(Mod_{𝒪_{E,X}}) ⥤ D(Mod_{E_X})` is a
localization functor with respect to the morphisms whose mapping cone `K` satisfies
`E_X ⊗_{𝒪_{E,X}} Hᵠ(K) = 0` for all `q`: `D(Mod_{E_X})` is the Verdier quotient of
`D(Mod_{𝒪_{E,X}})` by `rationallyAcyclic X ℓ E`. -/
theorem isLocalization_derivedExtendScalars :
    (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).leftDerivedFunctor.IsLocalization
      (rationallyAcyclic X ℓ E).trW := by
  let F := Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)
  let adj :=
    (Mod.extendRestrictAdjunction (padicIntegersToPadicSubfield X ℓ E)).mapDerivedCategoryAdjunction
  have h := adj.fullyFaithfulROfIsIsoCounit
  have := h.full
  have := h.faithful
  have hW : (MorphismProperty.isomorphisms _).inverseImage F.mapDerivedCategory =
      (rationallyAcyclic X ℓ E).trW := by
    ext K L f
    obtain ⟨Z, g, k, hT⟩ := distinguished_cocone_triangle f
    refine Iff.trans ?_ ((rationallyAcyclic X ℓ E).trW_iff_of_distinguished _ hT).symm
    rw [MorphismProperty.inverseImage_iff, MorphismProperty.isomorphisms.iff]
    have hFT := F.mapDerivedCategory.map_distinguished _ hT
    refine (Triangle.isZero₃_iff_isIso₁ _ hFT).symm.trans
      ((DerivedCategory.isZero_iff _).trans ?_)
    exact forall_congr' fun q ↦ ⟨fun hq ↦ hq.of_iso
      ((F.mapDerivedCategoryHomologyFunctorIso q).app Z),
      fun hq ↦ hq.of_iso ((F.mapDerivedCategoryHomologyFunctorIso q).app Z).symm⟩
  have := adj.isLocalization
  rw [hW] at this
  let e : F.leftDerivedFunctor ≅ F.mapDerivedCategory := F.leftDerivedFunctorIsoMapDerivedCategory
  exact Functor.IsLocalization.of_iso (rationallyAcyclic X ℓ E).trW e.symm

end AlgebraicGeometry.ProEtale
