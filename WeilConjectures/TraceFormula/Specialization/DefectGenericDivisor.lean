/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.NormalScheme
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorPointwise

/-!

# Generic vanishing of the defect along a principal divisor

Let `X` be a normal separated `k`-scheme of finite type, `Z = V(h)` the effective Cartier divisor
of a nonzero global function `h`, and `L` a bounded constructible `ℚ̄_ℓ`-complex on `X` with
`Li^* L = 0`. The defect `C_{X,Z}(L)` of `ProEtale.CondensedRing.specializationDefect` vanishes at
every generic point of `Z`, that is, over a dense open subset of `Z`
(`ProEtale.CondensedRing.exists_dense_isZero_specializationDefect`). This is the node
`det-sp-generic-divisor` of the blueprint subsection `sk-lem-tf-sp-generic-divisor`, stated here
for `ℚ̄_ℓ`-coefficients as an input of the proof of blueprint
`det-sp-zero-section-affine-space`.

Since `Li^* L = 0`, the target `Ψ_Z(Li^* L)` of the zero-section map vanishes, so the defect is
`Le^* Ψ_X(L)[1]` (`ProEtale.CondensedRing.nonempty_specializationDefect_iso_shift`). By the
reduction to the generic points of `Z` (`genericallyVanishingDefect_of_forall_defectVanishesNear`),
the node follows from the vanishing of `Le^* Ψ_X(L)` near each generic point of `Z`
(`ProEtale.CondensedRing.exists_isZero_upperStar_nearbyCycles_of_isGeneric`).

## Unfinished

`ProEtale.CondensedRing.exists_isZero_upperStar_nearbyCycles_of_isGeneric` is `sorry`ed: it is the
local computation of nearby cycles along the divisor at a codimension-one point (blueprint
`det-sp-generic-divisor`, proof), which needs finite-coefficient nearby cycles over the trait
and their comparison with `ℚ̄_ℓ`-coefficients, not available yet.

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Shift

variable {k : Type u} [Field k] (X : Over (Spec (.of k))) (I : X.left.IdealSheafData)
  (k' : Type u) [Field k'] [Algebra k k']
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- A functor commuting with the shifts kills `B ≅ A[1]` if it kills `A`. -/
lemma isZero_obj_of_iso_shift_aux {C D : Type*} [Category C] [Category D] [HasShift C ℤ]
    [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] (F : C ⥤ D)
    [F.CommShift ℤ] {A B : C} (e : B ≅ (shiftFunctor C (1 : ℤ)).obj A) (h : IsZero (F.obj A)) :
    IsZero (F.obj B) :=
  (((shiftFunctor D (1 : ℤ)).map_isZero h).of_iso ((F.commShiftIso (1 : ℤ)).app A)).of_iso
    (F.mapIso e)

/-- If the target `Ψ_Z(Li^* L)` of the zero-section map vanishes, the defect is
`Le^* Ψ_X(L)[1]`. -/
theorem nonempty_specializationDefect_iso_shift
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left)))
    (hL : IsZero (((deformationModel (centre X I) ⊥ k').nearbyCycles Λ).obj
      (L(((centreι X I).left)^*⟦Λ⟧).obj L))) :
    Nonempty (specializationDefect X I k' Λ L ≅ (shiftFunctor _ (1 : ℤ)).obj
      (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Λ⟧).obj
        (((deformationModel X I k').nearbyCycles Λ).obj L))) := by
  obtain ⟨g, h, hT⟩ := exists_distTriang_specializationDefect X I k' Λ L
  obtain ⟨φ, -, -⟩ := exists_iso_of_arrow_iso _ _ hT (contractible_distinguished₂ _)
    (Arrow.isoMk (Iso.refl _) (hL.iso (isZero_zero _)) ((isZero_zero _).eq_of_tgt _ _))
  exact ⟨Triangle.π₃.mapIso φ⟩

/-- If `Ψ_Z(Li^* L) = 0`, the restriction of the defect to an open `W` of `N_⊥ Z` vanishes as soon
as the restriction of `Le^* Ψ_X(L)` does. -/
theorem isZero_restrict_specializationDefect_of_isZero
    (W : (deformationSpecialFibre (centre X I) ⊥ k').left.Opens)
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left)))
    (hL : IsZero (((deformationModel (centre X I) ⊥ k').nearbyCycles Λ).obj
      (L(((centreι X I).left)^*⟦Λ⟧).obj L)))
    (hW : IsZero ((L((W.ι)^*⟦Λ⟧)).obj (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Λ⟧).obj
      (((deformationModel X I k').nearbyCycles Λ).obj L)))) :
    IsZero ((L((W.ι)^*⟦Λ⟧)).obj (specializationDefect X I k' Λ L)) := by
  exact isZero_obj_of_iso_shift_aux _
    (nonempty_specializationDefect_iso_shift X I k' Λ L hL).some hW

end Shift

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (k' : Type u) [Field k'] [Algebra k k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- **Vanishing of the restricted specialization near a generic point of a principal divisor**
(the local computation of the proof of blueprint `det-sp-generic-divisor`): let `X` be normal,
`Z = V(h)` for a nonzero global function `h`, `L` bounded constructible with `Li^* L = 0`, and `ζ`
a generic point of an irreducible component of `Z` (a point of codimension one of `X`). Then the
restriction `Le^* Ψ_X(L)` of the specialization `Ψ_X(L)` of `L` to the zero section vanishes over a
neighbourhood of `ζ`. -/
theorem exists_isZero_upperStar_nearbyCycles_of_isGeneric (hX : IsNormalScheme X.left)
    {h : Γ(X.left, ⊤)} (hh : h ≠ 0) {I : X.left.IdealSheafData}
    (hI : I = IdealSheafData.ofIdealTop (Ideal.span {h}))
    (L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hL : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (centreι X I)).obj L))
    (ζ : (centre X I).left) (hζ : closure {ζ} ∈ irreducibleComponents (centre X I).left) :
    ∃ U : (centre X I).left.Opens, ζ ∈ U ∧
      IsZero ((L((((constantSpecialFibreProj k' (centre X I)) ⁻¹ᵁ U).ι)^*⟦
        Profinite.padicAlgClRingObj ℓ⟧)).obj
        (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
          (((deformationModel X I k').nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj L.obj))) :=
  sorry

/-- **Generic vanishing of the defect along a principal divisor** (blueprint
`det-sp-generic-divisor`, a node of the subsection `sk-lem-tf-sp-generic-divisor`, for
`ℚ̄_ℓ`-coefficients): let `X` be normal, `Z = V(h)` the effective Cartier divisor of a nonzero
global function `h`, and `L` bounded constructible with `Li^* L = 0`. Then the defect `C_{X,Z}(L)`
vanishes at every generic point of `Z`: there is a dense open `U ⊆ Z` such that the restriction of
`C_{X,Z}(L)` to the inverse image of `U` in `N_⊥ Z ≅ Z ⊗ k'` is zero. Since `Li^* L = 0`, the defect
is `Le^* Ψ_X(L)[1]`, which vanishes near the generic points of `Z`
(`exists_isZero_upperStar_nearbyCycles_of_isGeneric`). -/
theorem exists_dense_isZero_specializationDefect (hX : IsNormalScheme X.left)
    {h : Γ(X.left, ⊤)} (hh : h ≠ 0) {I : X.left.IdealSheafData}
    (hI : I = IdealSheafData.ofIdealTop (Ideal.span {h}))
    (L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hL : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (centreι X I)).obj L)) :
    ∃ U : (centre X I).left.Opens, Dense (U : Set (centre X I).left) ∧
      IsZero ((L((((constantSpecialFibreProj k' (centre X I)) ⁻¹ᵁ U).ι)^*⟦
        Profinite.padicAlgClRingObj ℓ⟧)).obj
        (specializationDefect X I k' (Profinite.padicAlgClRingObj ℓ) L.obj)) := by
  have hΨ := NearbyCyclesModel.isZero_nearbyCycles_obj (Profinite.padicAlgClRingObj ℓ)
    (deformationModel (centre X I) ⊥ k')
    (((boundedConstructible _).ι.map_isZero hL).of_iso
      ((boundedConstructibleUpperStarCompatibility _ ℓ (centreι X I)).symm.app _))
  refine genericallyVanishingDefect_of_forall_defectVanishesNear X I k' _ L.obj fun ζ hζ ↦ ?_
  obtain ⟨U, hζU, hU⟩ := exists_isZero_upperStar_nearbyCycles_of_isGeneric k' hX hh hI L hL ζ hζ
  exact ⟨U, hζU, isZero_restrict_specializationDefect_of_isZero X I k' _ _ L.obj hΨ hU⟩

end AlgebraicGeometry.ProEtale.CondensedRing
