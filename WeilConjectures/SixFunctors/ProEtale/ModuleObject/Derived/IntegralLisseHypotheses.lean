/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleIhom

/-!
# The integral coefficients satisfy the hypotheses of the closure of `Dᵇc` under `⊗ᴸ` and `RHom`

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`. On a scheme `Z`
with noetherian underlying space, let `A` be a bounded complex of module objects over `𝒪̲_{E,Z}`
whose cohomology sheaves are pro-étale locally finitely presented (lisse `𝒪_E`-sheaves). If `L`
is a bounded complex with lisse cohomology sheaves, then `A ⊗ᴸ L` is bounded constructible; if
`L` is bounded constructible, then `RHom(A, L)` is bounded constructible
(`ProEtale.CondensedRing.PadicIntegersRingObj.boundedConstructible_tensorObj_of_lisse_homology`,
`ProEtale.CondensedRing.PadicIntegersRingObj.boundedConstructible_ihom_of_lisse_homology`), so
`𝒪̲_E` satisfies `ProEtale.CondensedRing.LisseHypotheses`
(`ProEtale.CondensedRing.PadicIntegersRingObj.lisseHypotheses`).

Unlike for the field coefficients, a lisse `𝒪_E`-sheaf is not locally free: it is pro-étale
locally isomorphic to a constant finitely generated `𝒪_E`-module `⊕ 𝒪_E/ϖ^{eᵢ} ⊕ 𝒪_E^r`
(Bhatt–Scholze, Section 6.8).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.PadicIntegersRingObj

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

/-- The derived tensor product `A ⊗ᴸ L` of two bounded complexes `A` and `L` of `𝒪̲_E`-module
objects with lisse cohomology sheaves is bounded constructible. -/
theorem boundedConstructible_tensorObj_of_lisse_homology (Z : Scheme.{u})
    [TopologicalSpace.NoetherianSpace Z]
    {A L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z))}
    (hA : DerivedCategory.TStructure.t.bounded A)
    (hA' : ∀ n, IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z)
      ((DerivedCategory.homologyFunctor _ n).obj A))
    (hL : DerivedCategory.TStructure.t.bounded L)
    (hL' : ∀ n, IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z)
      ((DerivedCategory.homologyFunctor _ n).obj L)) :
    boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z) (A ⊗ L) :=
  sorry

/-- The derived internal hom `RHom(A, L)` from a bounded complex `A` of `𝒪̲_E`-module objects
with lisse cohomology sheaves to a bounded constructible complex `L` is bounded constructible. -/
theorem boundedConstructible_ihom_of_lisse_homology (Z : Scheme.{u})
    [TopologicalSpace.NoetherianSpace Z]
    {A L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z))}
    (hA : DerivedCategory.TStructure.t.bounded A)
    (hA' : ∀ n, IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z)
      ((DerivedCategory.homologyFunctor _ n).obj A))
    (hL : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z) L) :
    boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z)
      ((ihom A).obj L) :=
  sorry

/-- The coefficient ring `𝒪̲_E` satisfies `ProEtale.CondensedRing.LisseHypotheses`. -/
theorem lisseHypotheses : LisseHypotheses (Profinite.padicIntegersRingObj.{u} ℓ E) where
  isTriangulated _ _ := inferInstance
  tensorObj Z _ _ _ hA hA' hL hL' :=
    boundedConstructible_tensorObj_of_lisse_homology ℓ E Z hA hA' hL hL'
  ihom Z _ _ _ hA hA' hL := boundedConstructible_ihom_of_lisse_homology ℓ E Z hA hA' hL

end AlgebraicGeometry.ProEtale.CondensedRing.PadicIntegersRingObj
