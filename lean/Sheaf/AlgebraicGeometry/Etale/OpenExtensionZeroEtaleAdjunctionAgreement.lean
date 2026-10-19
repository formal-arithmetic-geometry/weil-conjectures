/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap
public import Sheaf.CategoryTheory.RingedSiteModules

/-!
# Agreement of open and étale extension by zero and their adjunctions

Source: Stacks Project, Modules on Sites, Tag 03DI, and Étale Cohomology, Tag 03S3
(blueprint: lem-cbc-open-extension-zero-etale-adjunction-agreement).

The recorded open and étale extensions use the very same left Kan extension on presheaves.
For an open immersion its comma categories are empty or have a terminal object: this is
precisely the single-lift/zero description of the open extension. The general étale
interpretation is the sum over lifts. Thus the specified inclusion into the unique
summand is the identity of this common Kan-extension model. We sheafify that identity,
retaining the specified comparison rather than choosing an isomorphism of left adjoints.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The comparison `κ : j_! ⟶ j_!ᵉᵗ` obtained by sheafifying the single-summand inclusion.
Source: Stacks Project, Tag 03DI, and Tag 03S3, equation `j-p-shriek`
(blueprint: lem-cbc-open-extension-zero-etale-adjunction-agreement).

Both recorded presheaf constructions are `(MorphismProperty.Over.map ⊤ h).op.lan`.
In that shared model the map which is the inclusion of the unique summand when a lift
exists, and the unique map from zero otherwise, is its identity. Whiskering this map
with `presheafToSheaf` is its sheafification, and gives its naturality in `F` as well.
All coefficients and maps are in `ModuleCat Λ`, so the construction is Λ-linear. -/
noncomputable def openImmersionToEtaleLowerShriek
    (Λ : Type (u + 1)) [CommRing Λ] {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j ⟶
      etaleLowerShriek (ModuleCat.{u + 1} Λ) j inferInstance :=
  Functor.whiskerRight
    (𝟙 (sheafToPresheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
      localizationLowerShriekPresheaf (ModuleCat.{u + 1} Λ) j inferInstance))
    (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))

/-- The specified sheafified inclusion is invertible and identifies both adjunctions.
Source: Stacks Project, Tag 03DI, statement and summandwise Hom bijection in its proof;
Tag 03S3 and the following equation `j-p-shriek`
(blueprint: lem-cbc-open-extension-zero-etale-adjunction-agreement).

Proof plan (the six steps of the node).
1. For `P = jₚ!F` and the sum presheaf `Q`, define the inverse to the inclusion by the
identity on the unique summand, or the unique zero-module map when there is no lift.
These maps commute with restrictions, including restrictions from a no-lift object to
an object admitting a lift, and with morphisms of `F`
[def-weil-pbc-extension-by-zero, def-weil-pbc-etale-sum-extension].
2. Sheafify these inverse natural presheaf maps. Uniqueness of factorization through
sheafification makes the composites identities and proves naturality; this is exactly
`openImmersionToEtaleLowerShriek` in the common Kan-extension model
[def-weil-pbc-sheafification].
3. Compute the sum adjunction by sending a map out of `Q` to its restrictions on each
summand. Conversely, send the summand indexed by `s` by the component `α_(V,s)`.
Naturality of `α` gives the restriction squares; the two operations are inverse and
natural in both sheaves [def-weil-pbc-etale-sum-extension].
4. The sheafification Hom bijection composed with step 3 is the canonical étale
adjunction [lem-weil-pbc-etale-restriction-injectives,
lem-weil-pbc-adjunction-of-natural-bijection].
5. Precompose its transpose with the inclusion from `P`. On the unique summand the
result is `α_(V,s)`, and on a zero source it is zero. This is the open transpose
[lem-weil-pbc-extension-by-zero-adjunction]. Uniqueness of sheafification proves the
asserted equality of transposes.
6. Apply that equality to the transpose of an identity: the forward Hom bijection
at the identity gives the unit, while the inverse Hom bijection at the identity gives
the counit. This gives both displayed identities
[lem-weil-pbc-adjunction-of-natural-bijection]. -/
theorem openImmersionToEtaleLowerShriek_adjunction_agreement
    (Λ : Type (u + 1)) [CommRing Λ] {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    IsIso (openImmersionToEtaleLowerShriek Λ j) ∧
    (∀ (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (α : F ⟶ (upperStar (ModuleCat.{u + 1} Λ) j).obj G),
      ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).homEquiv
        F G).symm α =
        (openImmersionToEtaleLowerShriek Λ j).app F ≫
          ((etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j inferInstance).homEquiv
            F G).symm α) ∧
    (∀ (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j inferInstance).unit.app
        F =
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app F ≫
          (upperStar (ModuleCat.{u + 1} Λ) j).map
            ((openImmersionToEtaleLowerShriek Λ j).app F)) ∧
    (∀ (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).counit.app G =
        (openImmersionToEtaleLowerShriek Λ j).app
            ((upperStar (ModuleCat.{u + 1} Λ) j).obj G) ≫
          (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j inferInstance).counit.app
            G) := by
  have hadj : openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j =
      etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j inferInstance := rfl
  rw [← hadj]
  have hκ : openImmersionToEtaleLowerShriek Λ j =
      𝟙 (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j) := by
    exact Functor.whiskerRight_id _
  have hIso : IsIso (openImmersionToEtaleLowerShriek Λ j) := by
    rw [hκ]
    infer_instance
  refine ⟨hIso, ?_, ?_, ?_⟩
  · intro F G α
    rw [hκ]
    rfl
  · intro F
    simp [hκ]
  · intro G
    simp [hκ]

end AlgebraicGeometry.Etale
