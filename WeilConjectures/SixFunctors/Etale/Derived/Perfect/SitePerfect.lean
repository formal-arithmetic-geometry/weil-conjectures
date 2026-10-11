/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-!
# Perfect complexes on the coefficient site

A complex `K` of étale sheaves of `Λ`-modules on `X` is *perfect on the coefficient site*
(blueprint `def-weil-site-perfect-complex`) if, on the members `U ⟶ X` of some étale cover,
its restriction `K|_U` is isomorphic to a bounded complex of finite projective `Λ_U`-modules,
a finite projective module being a direct summand of a finite sum `Λ_U^{⊕m}` of copies of the
constant sheaf.

## Implementation notes

The blueprint works on the small pro-étale site; the definition is stated here on the small
étale site of the étale model of the coefficient categories, the restriction to `U` being the
derived pullback `Lu^*` along the member `u : U ⟶ X` of the cover. A direct summand of
`Λ_U^{⊕m}` is a retract of the constant sheaf with value `Λ^m`. The coefficient ring is
arbitrary: for `Λ = A_{E,n}` this is the finite stage of the blueprint, and for `Λ = 𝒪_E` it
is the integral stage in the étale model. Elsewhere in the repository perfectness is rendered as
dualizability for the derived tensor product
(`WeilConjectures.SixFunctors.Etale.Derived.Perfect`).

## Main definitions

- `AlgebraicGeometry.Etale.DerivedCategory.IsSitePerfect`: perfectness on the coefficient site.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

/-- Blueprint `def-weil-site-perfect-complex`: Perfect complexes on the coefficient site.

An object `K` of `D(X_ét, Λ)` is *perfect on the coefficient site* if there is an étale cover
`{uᵢ : Uᵢ ⟶ X}` such that each restriction `Luᵢ^* K` is isomorphic to (the image in
`D(Uᵢ, Λ)` of) a bounded complex `P` of sheaves of `Λ`-modules on `Uᵢ` whose terms are finite
projective, i.e. retracts of the constant sheaf `(Λ^m)_{Uᵢ}` for some `m`. -/
def DerivedCategory.IsSitePerfect
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) : Prop :=
  ∃ 𝒰 : Cover.{u} etalePrecoverage X, ∀ i : 𝒰.I₀,
    ∃ (P : CochainComplex (Sheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
      (a b : ℤ), P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ n, ∃ m : ℕ, Nonempty (Retract (P.X n)
        ((constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ (Fin m → Λ))))) ∧
      Nonempty ((L((𝒰.f i)^*[ModuleCat.{u + 1} Λ])).obj K ≅ DerivedCategory.Q.obj P)

/-- Perfectness on the coefficient site is invariant under isomorphism. -/
lemma DerivedCategory.IsSitePerfect.of_iso
    {K K' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (e : K ≅ K')
    (hK : DerivedCategory.IsSitePerfect K) : DerivedCategory.IsSitePerfect K' := by
  obtain ⟨𝒰, h⟩ := hK
  refine ⟨𝒰, fun i ↦ ?_⟩
  obtain ⟨P, a, b, ha, hb, hP, ⟨e'⟩⟩ := h i
  exact ⟨P, a, b, ha, hb, hP, ⟨(L((𝒰.f i)^*[ModuleCat.{u + 1} Λ])).mapIso e.symm ≪≫ e'⟩⟩

end Etale

end AlgebraicGeometry
