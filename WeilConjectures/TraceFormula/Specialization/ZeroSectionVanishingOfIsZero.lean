/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.ZeroSectionVanishing

/-!

# Vanishing of the specialization on the zero section

For a separated `k`-scheme `X` of finite type, a closed subscheme `i : Z = V(I) ⟶ X` and a bounded
constructible `ℚ̄_ℓ`-complex `L` on `X` with `Li^* L = 0`, the restriction `Le^* Sp_{X,Z}(L)` of
the specialization to the zero section `e` of the normal cone vanishes
(`ProEtale.CondensedRing.isZero_upperStar_nearbyCycles_deformationModel_of_isZero`, blueprint
`theorem-verdier-s-theorem-specialization-zero--2`). It follows from the invertibility of the
zero-section map `ε_{X,Z}(L) : Le^* Sp_{X,Z}(L) ⟶ Ψ_{Z × S}(Li^* L)`
(`ProEtale.CondensedRing.isIso_zeroSectionMap`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (k' : Type u) [Field k'] [Algebra k k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- **Verdier's theorem, vanishing on the zero section** (blueprint
`theorem-verdier-s-theorem-specialization-zero--2`): for a closed subscheme `i : Z = V(I) ⟶ X`
and a bounded constructible complex `L` on `X`, if `Li^* L = 0` then the restriction
`Le^* Sp_{X,Z}(L)` of the specialization to the normal cone to its zero section
`e : Z ⊗ k' ⟶ N_Z X ⊗ k'` vanishes. -/
theorem isZero_upperStar_nearbyCycles_deformationModel_of_isZero (I : X.left.IdealSheafData)
    (L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hL : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (centreι X I)).obj L)) :
    IsZero (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
      (((deformationModel X I k').nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj L.obj)) := by
  have := isIso_zeroSectionMap (ℓ := ℓ) k' X I L
  have hL' : IsZero (L(((centreι X I).left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj L.obj) :=
    ((boundedConstructible _).ι.map_isZero hL).of_iso
      ((boundedConstructibleUpperStarCompatibility _ ℓ (centreι X I)).app L).symm
  exact ((deformationModel (centre X I) ⊥ k').isZero_nearbyCycles_obj _ hL').of_iso
    (asIso (zeroSectionMap X I k' _ L.obj))

end AlgebraicGeometry.ProEtale.CondensedRing
