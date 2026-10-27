/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.NormalScheme
public import WeilConjectures.TraceFormula.Additivity
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorPointwise

/-!

# Vanishing of the restricted specialization near a point: reduction to lisse generators

Let `X` be a `k`-scheme, `Z = V(I) ⊆ X` a closed subscheme, `e : N_⊥ Z ⟶ N_Z X` the zero section
of the special fibre of the deformation to the normal cone and `ζ ∈ Z`. The restriction
`Le^* Ψ_X(L)` of the specialization of a complex `L` on `X` *vanishes near* `ζ` if it is zero over
the inverse image in `N_⊥ Z ≅ Z ⊗ k'` of an open neighbourhood of `ζ` in `Z`
(`ProEtale.CondensedRing.nearbyCyclesVanishNear`). These complexes form a triangulated
subcategory stable under retracts
(`ProEtale.CondensedRing.isTriangulated_nearbyCyclesVanishNear`).

Consequently, for `ℚ̄_ℓ`-coefficients and a complex `L` with `Li^* L = 0`, which is the extension
by zero `j_! Lj^* L` of its restriction to the complement `j : X ∖ Z ⟶ X`, the vanishing of
`Le^* Ψ_X(L)` near `ζ` reduces to the extensions by zero `j_! N` of the lisse generators `N` of
`Dᵇc(X ∖ Z)⟦ℚ̲̄_ℓ⟧` (`ProEtale.CondensedRing.exists_isZero_upperStar_nearbyCycles_of_lowerShriek`).

## Unfinished

`ProEtale.CondensedRing.exists_isZero_upperStar_nearbyCycles_lowerShriek_lisseGenerator`, the case
of a lisse generator at a generic point of a principal divisor of a normal scheme, is `sorry`ed.

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated ZeroObject

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- A retract of a zero object is zero. -/
lemma isZero_of_retract {C : Type*} [Category C] [Preadditive C] {A B : C} (r : Retract B A)
    (hA : IsZero A) : IsZero B :=
  (IsZero.iff_id_eq_zero _).2 (by rw [← r.retract, hA.eq_of_src r.r 0, Limits.comp_zero])

section Abstract

variable {k : Type u} [Field k] (X : Over (Spec (.of k))) (I : X.left.IdealSheafData)
  (k' : Type u) [Field k'] [Algebra k k']
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The restriction `L ↦ (Le^* Ψ_X(L))|_W` of the specialization of a complex on `X` to the zero
section `N_⊥ Z ⟶ N_Z X`, further restricted to an open `W` of `N_⊥ Z`. -/
noncomputable def restrictedZeroSectionNearbyCycles
    (W : (deformationSpecialFibre (centre X I) ⊥ k').left.Opens) :=
  (deformationModel X I k').nearbyCycles Λ ⋙
    L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Λ⟧) ⋙ L((W.ι)^*⟦Λ⟧)

noncomputable instance (W : (deformationSpecialFibre (centre X I) ⊥ k').left.Opens) :
    (restrictedZeroSectionNearbyCycles X I k' Λ W).CommShift ℤ := by
  unfold restrictedZeroSectionNearbyCycles
  infer_instance

instance (W : (deformationSpecialFibre (centre X I) ⊥ k').left.Opens) :
    (restrictedZeroSectionNearbyCycles X I k' Λ W).IsTriangulated := by
  unfold restrictedZeroSectionNearbyCycles
  infer_instance

/-- Unfolding of `restrictedZeroSectionNearbyCycles`. -/
lemma restrictedZeroSectionNearbyCycles_obj
    (W : (deformationSpecialFibre (centre X I) ⊥ k').left.Opens)
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))) :
    (restrictedZeroSectionNearbyCycles X I k' Λ W).obj L =
      L((W.ι)^*⟦Λ⟧).obj (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Λ⟧).obj
        (((deformationModel X I k').nearbyCycles Λ).obj L)) :=
  rfl

/-- The complexes `L` on `X` whose specialization restricted to the zero section, `Le^* Ψ_X(L)`,
*vanishes near* a point `ζ` of the centre: its restriction to the inverse image in
`N_⊥ Z ≅ Z ⊗ k'` of some open neighbourhood of `ζ` in `Z` is zero. -/
def nearbyCyclesVanishNear (ζ : (centre X I).left) :
    ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))) :=
  fun L ↦ ∃ U : (centre X I).left.Opens, ζ ∈ U ∧
    IsZero ((restrictedZeroSectionNearbyCycles X I k' Λ
      ((constantSpecialFibreProj k' (centre X I)) ⁻¹ᵁ U)).obj L)

/-- If the vanishing over an open `W` of `N_⊥ Z` of the restricted specialization of `L₁` and `L₂`
implies that of `L₃`, then the vanishing near `ζ` for `L₁` and `L₂` implies that of `L₃`: two
neighbourhoods of `ζ` meet in a neighbourhood of `ζ`. -/
lemma nearbyCyclesVanishNear_of_two {ζ : (centre X I).left}
    {L₁ L₂ L₃ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))}
    (h : ∀ W : (deformationSpecialFibre (centre X I) ⊥ k').left.Opens,
      IsZero ((restrictedZeroSectionNearbyCycles X I k' Λ W).obj L₁) →
      IsZero ((restrictedZeroSectionNearbyCycles X I k' Λ W).obj L₂) →
      IsZero ((restrictedZeroSectionNearbyCycles X I k' Λ W).obj L₃))
    (h₁ : nearbyCyclesVanishNear X I k' Λ ζ L₁) (h₂ : nearbyCyclesVanishNear X I k' Λ ζ L₂) :
    nearbyCyclesVanishNear X I k' Λ ζ L₃ := by
  obtain ⟨U₁, hζ₁, hL₁⟩ := h₁
  obtain ⟨U₂, hζ₂, hL₂⟩ := h₂
  rw [restrictedZeroSectionNearbyCycles_obj] at hL₁ hL₂
  refine ⟨U₁ ⊓ U₂, ⟨hζ₁, hζ₂⟩, h _ ?_ ?_⟩
  · rw [restrictedZeroSectionNearbyCycles_obj]
    exact isZero_leftDerivedUpperStar_ι_obj_of_le Λ (Hom.preimage_mono _ inf_le_left) hL₁
  · rw [restrictedZeroSectionNearbyCycles_obj]
    exact isZero_leftDerivedUpperStar_ι_obj_of_le Λ (Hom.preimage_mono _ inf_le_right) hL₂

instance (ζ : (centre X I).left) :
    (nearbyCyclesVanishNear X I k' Λ ζ).IsClosedUnderIsomorphisms where
  of_iso e := fun ⟨U, hU, hL⟩ ↦ ⟨U, hU, hL.of_iso (Functor.mapIso _ e.symm)⟩

instance (ζ : (centre X I).left) :
    (nearbyCyclesVanishNear X I k' Λ ζ).IsStableUnderRetracts where
  of_retract r := fun ⟨U, hU, hL⟩ ↦ ⟨U, hU, isZero_of_retract (r.map _) hL⟩

/-- **The complexes whose restricted specialization vanishes near `ζ` form a triangulated
subcategory.** -/
instance isTriangulated_nearbyCyclesVanishNear (ζ : (centre X I).left) :
    (nearbyCyclesVanishNear X I k' Λ ζ).IsTriangulated where
  exists_zero := ⟨0, isZero_zero _, ⟨⊤, trivial, Functor.map_isZero _ (isZero_zero _)⟩⟩
  isStableUnderShiftBy n :=
    { le_shift L hL := by
        rw [ObjectProperty.prop_shift_iff]
        exact nearbyCyclesVanishNear_of_two X I k' Λ (L₁ := L) (L₂ := L)
          (fun W h _ ↦ ((shiftFunctor _ n).map_isZero h).of_iso
            (((restrictedZeroSectionNearbyCycles X I k' Λ W).commShiftIso n).app L)) hL hL }
  toIsTriangulatedClosed₂ := .mk' fun T hT h₁ h₃ ↦
    nearbyCyclesVanishNear_of_two X I k' Λ
      (fun W h₁' h₃' ↦ Triangle.isZero₂_of_isZero₁₃ _
        ((restrictedZeroSectionNearbyCycles X I k' Λ W).map_distinguished _ hT) h₁' h₃') h₁ h₃

end Abstract

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (k' : Type u) [Field k'] [Algebra k k']
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- **Reduction to the lisse generators**: if the restricted specialization `Le^* Ψ_X(j_! N)`
vanishes near `ζ` for the extensions by zero `j_! N` along the complement `j : X ∖ Z ⟶ X` of the
lisse generators `N` of `Dᵇc(X ∖ Z)⟦ℚ̲̄_ℓ⟧`, it does for every extension by zero `j_! N`. -/
theorem nearbyCyclesVanishNear_lowerShriek_of_lisseGenerator {I : X.left.IdealSheafData}
    (ζ : (centre X I).left)
    (h : ∀ N : Dᵇc((overRestrict X I.support.compl).left)⟦Profinite.padicAlgClRingObj ℓ⟧,
      lisseGenerator ℓ (overRestrict X I.support.compl) N →
      nearbyCyclesVanishNear X I k' (Profinite.padicAlgClRingObj ℓ) ζ
        ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
          (overRestrictι X I.support.compl)).obj N).obj)
    (N : Dᵇc((overRestrict X I.support.compl).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    nearbyCyclesVanishNear X I k' (Profinite.padicAlgClRingObj ℓ) ζ
      ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
        (overRestrictι X I.support.compl)).obj N).obj := by
  let Q := (nearbyCyclesVanishNear X I k' (Profinite.padicAlgClRingObj ℓ) ζ).inverseImage
    (boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
      (overRestrictι X I.support.compl) ⋙
      (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι)
  have : Q.IsStableUnderRetracts :=
    ⟨fun r hB ↦ (nearbyCyclesVanishNear X I k' _ ζ).prop_of_retract (r.map _) hB⟩
  exact (ObjectProperty.triangEnvelope_le_iff (Q := Q) _).mpr (fun N hN ↦ h N hN) _
    (triangEnvelope_lisseGenerator ℓ _ N)

/-- **The local computation at a generic point of a principal divisor for lisse generators**
(the local nearby-cycles computation of the proof of blueprint `det-sp-generic-divisor`, for
extensions by zero of lisse generators): let `X` be normal, `Z = V(h)` for a nonzero global
function `h`, `j : X ∖ Z ⟶ X` the complement, `N` a lisse generator of `Dᵇc(X ∖ Z)⟦ℚ̲̄_ℓ⟧` and `ζ`
a generic point of an irreducible component of `Z`. Then the restriction `Le^* Ψ_X(j_! N)` to the
zero section vanishes over a neighbourhood of `ζ`: the extension by zero is locally acyclic along
the divisor near `ζ`. Unfinished. -/
theorem exists_isZero_upperStar_nearbyCycles_lowerShriek_lisseGenerator [IsSepClosed k']
    [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] (hX : IsNormalScheme X.left)
    {h : Γ(X.left, ⊤)} (hh : h ≠ 0) {I : X.left.IdealSheafData}
    (hI : I = IdealSheafData.ofIdealTop (Ideal.span {h}))
    (N : Dᵇc((overRestrict X I.support.compl).left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hN : lisseGenerator ℓ (overRestrict X I.support.compl) N)
    (ζ : (centre X I).left) (hζ : closure {ζ} ∈ irreducibleComponents (centre X I).left) :
    ∃ U : (centre X I).left.Opens, ζ ∈ U ∧
      IsZero ((L((((constantSpecialFibreProj k' (centre X I)) ⁻¹ᵁ U).ι)^*⟦
        Profinite.padicAlgClRingObj ℓ⟧)).obj
        (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
          (((deformationModel X I k').nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
            ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
              (overRestrictι X I.support.compl)).obj N).obj))) :=
  sorry

/-- **Reduction of the local computation to the lisse generators**: for `L` with `Li^* L = 0`,
the restricted specialization `Le^* Ψ_X(L)` vanishes near `ζ` as soon as it does for the
extensions by zero `j_! N` of the lisse generators `N` of `Dᵇc(X ∖ Z)⟦ℚ̲̄_ℓ⟧`. Indeed the
open–closed triangle `j_! Lj^* L ⟶ L ⟶ Ri_* Li^* L ⟶` shows `L ≅ j_! Lj^* L`. -/
theorem exists_isZero_upperStar_nearbyCycles_of_lowerShriek {I : X.left.IdealSheafData}
    (ζ : (centre X I).left)
    (h : ∀ N : Dᵇc((overRestrict X I.support.compl).left)⟦Profinite.padicAlgClRingObj ℓ⟧,
      lisseGenerator ℓ (overRestrict X I.support.compl) N →
      nearbyCyclesVanishNear X I k' (Profinite.padicAlgClRingObj ℓ) ζ
        ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
          (overRestrictι X I.support.compl)).obj N).obj)
    (L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hL : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (centreι X I)).obj L)) :
    nearbyCyclesVanishNear X I k' (Profinite.padicAlgClRingObj ℓ) ζ L.obj := by
  obtain ⟨δ, hδ⟩ := exists_distTriang_openImmersionLowerShriek_openClosed
    (overRestrictι X I.support.compl) (centreι X I) (isCompl_range_overRestrictι_centreι I) L
  have h₃ : IsZero ((boundedConstructible _).ι.obj ((boundedConstructibleLowerStar ℓ
      (centreι X I)).obj ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (centreι X I)).obj L))) :=
    (boundedConstructible _).ι.map_isZero ((boundedConstructibleLowerStar ℓ _).map_isZero hL)
  have : IsIso ((boundedConstructible _).ι.map
      ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ
        (overRestrictι X I.support.compl)).counit.app L)) :=
    (Triangle.isZero₃_iff_isIso₁ _ hδ).1 h₃
  exact (nearbyCyclesVanishNear X I k' _ ζ).prop_of_iso (asIso ((boundedConstructible _).ι.map
    ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ
      (overRestrictι X I.support.compl)).counit.app L)))
    (nearbyCyclesVanishNear_lowerShriek_of_lisseGenerator k' ζ h _)

end AlgebraicGeometry.ProEtale.CondensedRing
