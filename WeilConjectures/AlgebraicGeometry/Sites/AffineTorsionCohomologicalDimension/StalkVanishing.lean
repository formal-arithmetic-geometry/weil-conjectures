/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.CohomologyMapDelta
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Vanishing of geometric stalks of higher direct images

Let `h : X ⟶ S` be a morphism of schemes, `F` an abelian étale sheaf on `X` and
`s : Spec Ω ⟶ S` a geometric point. For a pointed étale neighbourhood `V` of `s` write
`X_V = X ×_S V`. If every class in `Hᵠ(X_V, F|)` dies on `X_{V'}` for some smaller pointed
étale neighbourhood `V' ⟶ V`, then the geometric stalk of `Rᵠh_* F` at `s` vanishes
(`AlgebraicGeometry.Etale.isZero_upperStar_rightDerived_lowerStar_of_forall_exists`).

The proof is by dimension shifting: embedding `F` into an injective sheaf `I` with quotient `Q`,
`Rᵠh_* F ≅ Rᵠ⁻¹h_* Q` for `q ≥ 2` and the hypothesis passes from `F` in degree `q` to `Q` in degree
`q - 1`, since the restrictions of `I` to the `X_V` are injective. In degree one, a germ of a
section `σ` of `h_* Q` at `s` is a section of `Q` over some `X_V`; its coboundary dies on a
smaller `X_{V'}`, so that `σ` lifts to `I` there, and the germ of `σ` in `R¹h_* F` vanishes.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

open Scheme

variable {X S : Scheme.{u}} (h : X ⟶ S) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ S)

/-- The morphism `X ×_S V' ⟶ X ×_S V` induced by a morphism `f : V' ⟶ V` of pointed étale
neighbourhoods of a geometric point of `S`. -/
noncomputable abbrev pullbackNeighborhoodMap {x y : PointedEtaleNeighborhood s} (f : y ⟶ x) :
    pullback h y.1.hom ⟶ pullback h x.1.hom :=
  pullback.map h y.1.hom h x.1.hom (𝟙 X) f.1.left (𝟙 S) (by simp)
    (by simp [MorphismProperty.Over.w f.1])

/-- **Geometric stalks of higher direct images.** Let `h : X ⟶ S`, `F` an abelian étale sheaf
on `X`, `s` a geometric point of `S` and `q > 0`. If for every pointed étale neighbourhood `V`
of `s` every class of `Hᵠ(X ×_S V, F|)` vanishes on `X ×_S V'` for some pointed étale
neighbourhood `V' ⟶ V`, then the geometric stalk `s^* Rᵠh_* F` vanishes. -/
theorem isZero_upperStar_rightDerived_lowerStar_of_forall_exists
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (hq : 0 < q)
    (H : ∀ (x : PointedEtaleNeighborhood s)
      (c : Sheaf.H ((pullback.fst h x.1.hom)^*[AddCommGrpCat.{u + 1}].obj F) q),
      ∃ (y : PointedEtaleNeighborhood s) (f : y ⟶ x),
        cohomologyMap (pullbackNeighborhoodMap h s f) _ q c = 0) :
    IsZero ((s)^*[AddCommGrpCat.{u + 1}].obj
      ((((h)_*[AddCommGrpCat.{u + 1}]).rightDerived q).obj F)) :=
  sorry

end AlgebraicGeometry.Etale
