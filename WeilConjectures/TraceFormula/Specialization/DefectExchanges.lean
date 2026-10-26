/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructible
public import WeilConjectures.TraceFormula.Additivity
public import WeilConjectures.TraceFormula.Specialization.DefectExchangeSquares
public import WeilConjectures.TraceFormula.Specialization.DeformationModelFactor
public import WeilConjectures.TraceFormula.Specialization.NearbyFiniteness
public import WeilConjectures.TraceFormula.Specialization.NearbyProperExchange
public import WeilConjectures.TraceFormula.Specialization.NearbySmoothExchange
public import WeilConjectures.TraceFormula.Specialization.NormalizePrecoherent
public import WeilConjectures.TraceFormula.Specialization.TraitModelInstances
public import WeilConjectures.TraceFormula.Specialization.TraitModelProperExchange

/-!

# Exchanges for the defect of the specialization

Let `f : X' ⟶ X` be a morphism of separated `k`-schemes of finite type, `Z = V(I) ⊆ X` a closed
subscheme and `Z' = f⁻¹ Z = V(f^* I)` its schematic inverse image, with the restriction
`f_Z : Z' ⟶ Z` (`ProEtale.CondensedRing.centreMap`). The deformation of `f_Z` maps the special fibre
`N_⊥ Z' ≅ Z' ⊗ k'` of the constant family of `Z'` to that of `Z`
(`ProEtale.CondensedRing.centreSpecialFibreMap`).

This file states the exchange properties of the defect `C_{X,Z}` of
`ProEtale.CondensedRing.specializationDefect`, which are the nodes of the blueprint subsection
`sk-lem-tf-sp-defect-exchanges`, as compatibilities required from that subsection:

* `ProEtale.CondensedRing.nonempty_specializationDefect_lowerStar_iso`,
  `ProEtale.CondensedRing.nonempty_specializationDefect_upperStar_iso`: proper and smooth exchange
  (blueprint `det-sp-defect-proper-smooth`);
* `ProEtale.CondensedRing.isZero_specializationDefect_lowerStar_centreι`,
  `ProEtale.CondensedRing.nonempty_specializationDefect_lowerShriek_upperStar_iso`: the defect
  kills complexes supported on the centre, and is unchanged by `L ↦ j_! j^* L`
  (blueprint `det-sp-defect-closed-vanishing`).

The coefficients are `ℚ̄_ℓ`, and the complexes are bounded constructible.

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k] {X X' : Over (Spec (.of k))} (f : X' ⟶ X)
  (I : X.left.IdealSheafData) (k' : Type u) [Field k'] [Algebra k k']

variable {ℓ : ℕ} [Fact ℓ.Prime] [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]



/-- **Smooth exchange for the defect** (blueprint `det-sp-defect-proper-smooth`, smooth case; a
node of the subsection `sk-lem-tf-sp-defect-exchanges`): for `f : X' ⟶ X` smooth and `L` bounded
constructible on `X`, `C_{X',Z'}(Lf^* L) ≅ Lf_Z^* C_{X,Z}(L)`. The pullback exchanges of the
deformations `f̃` and `f̃_Z` of `f` and `f_Z` are invertible by the smooth exchange of nearby cycles
(`isIso_pullbackExchange_deformationModel_app_of_smooth`), and they carry `Lf_Z^* ε_{X,Z}(L)` to
`ε_{X',Z'}(Lf^* L)` (`nonempty_specializationDefect_upperStar_iso_of_isIso`). -/
theorem nonempty_specializationDefect_upperStar_iso [Smooth f.left]
    (L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Nonempty (specializationDefect X' (I.comap f.left) k' (Profinite.padicAlgClRingObj ℓ)
        (L((f.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj L.obj) ≅
      L(((centreSpecialFibreMap f I k').left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
        (specializationDefect X I k' (Profinite.padicAlgClRingObj ℓ) L.obj)) := by
  have : Smooth (comapDeformationModelHom f I k').total :=
    smooth_deformationTotalMap k' f (siteIdeal_map_appLE_le_comap f I) rfl
  have : Smooth (centreDeformationModelHom f I k').total :=
    smooth_deformationTotalMap k' (centreMap f I) (siteIdeal_map_appLE_le_bot_centreMap f I)
      (IdealSheafData.comap_bot _).symm
  have hf := isIso_pullbackExchange_deformationModel_app_of_smooth k'
    (comapDeformationModelHom f I k') (isPullback_deformationGenericMap _ _ k') L.property
  have hg := isIso_pullbackExchange_deformationModel_app_of_smooth k'
    (centreDeformationModelHom f I k') (isPullback_deformationGenericMap _ _ k')
    (boundedConstructible_leftDerivedUpperStar_obj (Profinite.padicAlgClRingObj ℓ) ℓ (centreι X I) L)
  have h₁ := nonempty_specializationDefect_upperStar_iso_of_isIso f I k'
    (Profinite.padicAlgClRingObj ℓ) L.obj
  revert h₁ hf hg
  normalize_precoherent
  intro hf hg h₁
  exact h₁ hf hg

end AlgebraicGeometry.ProEtale.CondensedRing
