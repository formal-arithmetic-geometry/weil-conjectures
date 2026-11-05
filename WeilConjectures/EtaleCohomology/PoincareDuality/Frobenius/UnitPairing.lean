/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.SelfInjective
public import WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism.Point

/-!
# Finite-level Poincaré duality for the cohomology of the constant sheaf

Let `k` be separably closed, `a : X ⟶ Spec k` proper with a Tate orientation `γ` of relative
dimension `d`, and `Λ` a finite self-injective cogenerating coefficient ring (e.g. `ℤ/ℓᵐ`)
whose characteristic is invertible on `X`. Write `H^n(X, Λ) = Hom(Λ_X, Λ_X[n])`. For
`i + j = 2d` there is a biadditive pairing `H^i(X, Λ) × H^j(X, Λ) ⟶ Λ` which is nondegenerate on
both sides (`AlgebraicGeometry.Etale.TateOrientation.exists_nondegenerate_unitPairing`): it is the
degreewise Poincaré pairing of `K = Λ_X`
(`AlgebraicGeometry.Etale.TateOrientation.injective_degreewisePoincarePairing`) read through
`H^i_c(X, Λ) ≅ H^i(X, Λ)` (`a` proper), `Λ_X^∨(d) ≅ Λ_X` (the Tate twists are trivial over a
separably closed field) and `End(Λ_s) ≅ Λ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

/-- Composition with an isomorphism, as an additive equivalence of Hom groups. -/
@[simps!]
def _root_.CategoryTheory.Iso.postcompAddEquiv {C : Type*} [Category C] [Preadditive C]
    {X Y Y' : C} (e : Y ≅ Y') : (X ⟶ Y) ≃+ (X ⟶ Y') :=
  AddEquiv.mk' ((Iso.refl X).homCongr e) fun f g ↦ by simp

variable {Λ : Type (u + 1)} [CommRing Λ] {k : Type u} [Field k] [IsSepClosed k]

variable (Λ) in
/-- Over a connected scheme, `r ↦ r • 𝟙` identifies `Λ` with the endomorphisms of `Λ_X`. -/
noncomputable def endUnitAddEquiv (X : Scheme.{u}) [ConnectedSpace X] :
    Λ ≃+ (𝟙_ (DerivedCategoryModule Λ X) ⟶ 𝟙_ (DerivedCategoryModule Λ X)) :=
  AddEquiv.ofBijective (AddMonoidHom.mk' (fun r : Λ ↦ r • 𝟙 (𝟙_ (DerivedCategoryModule Λ X)))
    fun r s ↦ add_smul r s _) (bijective_smul_id_unit Λ X)

variable [HasTateTwist Λ] [HasInvertibleExponent Λ (Spec (.of k))] {X : Scheme.{u}}
  [HasInvertibleExponent Λ X]

variable [Finite Λ] [Module.Injective Λ Λ] {a : X ⟶ Spec (.of k)} [HasCompactification a]
  [IsProper a] {d : ℕ}

namespace TateOrientation

end TateOrientation

end AlgebraicGeometry.Etale
