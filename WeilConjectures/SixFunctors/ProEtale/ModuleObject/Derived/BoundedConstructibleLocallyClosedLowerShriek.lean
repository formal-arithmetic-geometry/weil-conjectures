/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimitEssSurjGenerators

/-!
# Extension by zero along a locally closed immersion preserves `Dᵇc`

Let `a = j ≫ i : S ⟶ W ⟶ X` be a locally closed immersion, written as an open immersion `j`
followed by a closed immersion `i`, into a scheme `X` with noetherian underlying space. Its
extension by zero is `a_! = Ri_* ∘ j_!`.

* `ProEtale.CondensedRing.boundedConstructible_rightDerivedLowerStar_openImmersionLowerShriek_obj`:
  for any commutative condensed ring `Λ`, `a_!` maps bounded constructible complexes to bounded
  constructible complexes.
* `ProEtale.CondensedRing.boundedConstructible_lowerShriek_padicIntegersRingObj`: the case
  `Λ = 𝒪_E` (blueprint `lemma-integral-models--5`).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The extension by zero `a_! = Ri_* ∘ j_!` along a locally closed immersion `a = j ≫ i`
(`j` an open immersion, `i` a closed immersion) into a scheme with noetherian underlying space
maps bounded constructible complexes to bounded constructible complexes. -/
theorem boundedConstructible_rightDerivedLowerStar_openImmersionLowerShriek_obj
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {S W X : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]
    (j : S ⟶ W) [IsOpenImmersion j] (i : W ⟶ X) [IsClosedImmersion i]
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj Λ S))} (hK : boundedConstructible (condensedRingObj Λ S) K) :
    boundedConstructible (condensedRingObj Λ X)
      ((R((i)_*⟦Λ⟧)).obj ((D((j)_!open⟦Λ⟧)).obj K)) :=
  have : TopologicalSpace.NoetherianSpace W := i.isClosedEmbedding.isInducing.noetherianSpace
  boundedConstructible_rightDerivedLowerStar_of_isClosedImmersion Λ i
    (boundedConstructible_openImmersionLowerShriek_obj_of_noetherianSpace Λ j hK)

/-- **Integral locally closed extension.** For a locally closed immersion `a = j ≫ i : S ⟶ X`
(`j` an open immersion, `i` a closed immersion) into a scheme with noetherian underlying space,
the extension by zero `a_! = Ri_* ∘ j_!` with `𝒪_E`-coefficients sends `Dᵇc(S, 𝒪_E)` into
`Dᵇc(X, 𝒪_E)`.
(blueprint: lemma-integral-models--5) -/
theorem boundedConstructible_lowerShriek_padicIntegersRingObj (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
    {S W X : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]
    (j : S ⟶ W) [IsOpenImmersion j] (i : W ⟶ X) [IsClosedImmersion i]
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) S))}
    (hK : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) S) K) :
    boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)
      ((R((i)_*⟦Profinite.padicIntegersRingObj ℓ E⟧)).obj
        ((D((j)_!open⟦Profinite.padicIntegersRingObj ℓ E⟧)).obj K)) :=
  boundedConstructible_rightDerivedLowerStar_openImmersionLowerShriek_obj _ j i hK

end AlgebraicGeometry.ProEtale.CondensedRing
