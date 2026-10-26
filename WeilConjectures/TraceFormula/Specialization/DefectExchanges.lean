/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructible
public import WeilConjectures.TraceFormula.Specialization.DefectCentreMap

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

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k] {X X' : Over (Spec (.of k))} (f : X' ⟶ X)
  (I : X.left.IdealSheafData) (k' : Type u) [Field k'] [Algebra k k']

variable {ℓ : ℕ} [Fact ℓ.Prime] [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]

/-- **Proper exchange for the defect** (blueprint `det-sp-defect-proper-smooth`, proper case; a
node of the subsection `sk-lem-tf-sp-defect-exchanges`): for `f : X' ⟶ X` proper and `L'` bounded
constructible on `X'`, `C_{X,Z}(Rf_* L') ≅ Rf_{Z*} C_{X',Z'}(L')`. Here the isomorphism is only
asserted to exist. -/
theorem nonempty_specializationDefect_lowerStar_iso [IsProper f.left]
    (L' : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Nonempty (specializationDefect X I k' (Profinite.padicAlgClRingObj ℓ)
        (R((f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj L'.obj) ≅
      R(((centreSpecialFibreMap f I k').left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
        (specializationDefect X' (I.comap f.left) k' (Profinite.padicAlgClRingObj ℓ) L'.obj)) :=
  sorry

/-- **Smooth exchange for the defect** (blueprint `det-sp-defect-proper-smooth`, smooth case; a
node of the subsection `sk-lem-tf-sp-defect-exchanges`): for `f : X' ⟶ X` smooth and `L` bounded
constructible on `X`, `C_{X',Z'}(Lf^* L) ≅ Lf_Z^* C_{X,Z}(L)`. Here the isomorphism is only
asserted to exist. -/
theorem nonempty_specializationDefect_upperStar_iso [Smooth f.left]
    (L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Nonempty (specializationDefect X' (I.comap f.left) k' (Profinite.padicAlgClRingObj ℓ)
        (L((f.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj L.obj) ≅
      L(((centreSpecialFibreMap f I k').left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
        (specializationDefect X I k' (Profinite.padicAlgClRingObj ℓ) L.obj)) :=
  sorry

variable (X) in
/-- **The defect kills complexes supported on the centre** (blueprint
`det-sp-defect-closed-vanishing`, first and second assertions; a node of the subsection
`sk-lem-tf-sp-defect-exchanges`): `C_{X,Z}(i_* M) = 0` for `M` bounded constructible on `Z`. -/
theorem isZero_specializationDefect_lowerStar_centreι
    (M : Dᵇc((centre X I).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsZero (specializationDefect X I k' (Profinite.padicAlgClRingObj ℓ)
      (R(((centreι X I).left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj M.obj)) :=
  sorry

variable (X) in
/-- **The defect is unchanged by extension by zero from the complement** (blueprint
`det-sp-defect-closed-vanishing`, last assertion; a node of the subsection
`sk-lem-tf-sp-defect-exchanges`): for the open immersion `j : U ⟶ X` of the complement of the
centre, the counit `j_! j^* L ⟶ L` induces `C_{X,Z}(j_! j^* L) ≅ C_{X,Z}(L)`. Here the isomorphism
is only asserted to exist. -/
theorem nonempty_specializationDefect_lowerShriek_upperStar_iso {U : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] (j : U ⟶ X)
    [IsOpenImmersion j.left]
    (hj : IsCompl (Set.range j.left.base) (Set.range (centreι X I).left.base))
    (L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Nonempty (specializationDefect X I k' (Profinite.padicAlgClRingObj ℓ)
        ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj L)).obj ≅
      specializationDefect X I k' (Profinite.padicAlgClRingObj ℓ) L.obj) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
