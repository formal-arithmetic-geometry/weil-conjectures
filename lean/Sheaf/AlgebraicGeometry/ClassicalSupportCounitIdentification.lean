/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Sheaf.AlgebraicGeometry.SupportLocalizationTriangle
import Sheaf.SixFunctors.OpenTensorNormalizationData

/-! # Canonical identification with the support-localization triangle

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-a1/sk-prop-a1.proof.md,
first localization triangle and canonical identification of its supported term and boundary
(blueprint: lem-pur-classical-support-counit-identification).

The helpers expose the normalized adjunction and the actual injective-cone boundary
already supplied by `supportLocalizationTriangle`. All categories are ordinary module-sheaf
categories, with no constructibility or etale-origin restriction.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.ProEtale

variable (A : Type (u + 1)) [CommRing A] [Finite A]
  {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
  [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
  (hPair : IsCompl (Set.range i) (Set.range j))

/-- The model-normalized support adjunction, extracted from the existing localization
construction. Source: blueprint sk-prop-a1 proof, first triangle
(blueprint: lem-pur-classical-support-counit-identification). -/
noncomputable def classicalSupportAdjunction :
    supportClosedDerivedPlus A i j hPair ⊣
      (finiteClosedUpperShriek A i j).rightDerivedFunctorPlus :=
  (supportLocalizationTriangle A i j hPair).choose

/-- The actual boundary transported from the injective-cone localization triangle.
Only a representative of the already constructed triangle is selected: the normalization
and resolution independence are those of `supportLocalizationTriangle`.
Source: blueprint sk-prop-a1 proof, first triangle
(blueprint: lem-pur-classical-support-counit-identification). -/
noncomputable def classicalSupportBoundary
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :
    (((lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctorPlus.obj
      ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus.obj K)).obj) ⟶
    ((supportClosedDerivedPlus A i j hPair).obj
      ((finiteClosedUpperShriek A i j).rightDerivedFunctorPlus.obj K)).obj⟦(1 : ℤ)⟧ :=
  let models := (supportLocalizationTriangle A i j hPair).choose_spec.2.1 K
  let I := models.choose
  let hI := models.choose_spec.choose
  let hq := models.choose_spec.choose_spec.choose
  let eB := models.choose_spec.choose_spec.choose_spec.choose
  (supportThirdModelComparison A j I hI K eB).inv ≫
    (supportModelTriangle A i j hPair I hq).mor₃ ≫
    (supportFirstModelComparison A i j hPair I hI K eB).hom⟦(1 : ℤ)⟧'

/-- The support triangle with its fixed counit, open unit, and injective-cone boundary.
Source: blueprint sk-prop-a1 proof, first triangle
(blueprint: lem-pur-classical-support-counit-identification). -/
noncomputable def classicalSupportTriangle
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :
    Triangle (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :=
  Triangle.mk
    (DerivedCategory.Plus.ι.map ((classicalSupportAdjunction A i j hPair).counit.app K))
    (DerivedCategory.Plus.ι.map
      ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) j).unit.app K))
    (classicalSupportBoundary A i j hPair K)

/-- Transpose the given first arrow through the normalized support adjunction.
Source: blueprint sk-prop-a1 proof, canonical first-term identification
(blueprint: lem-pur-classical-support-counit-identification). -/
noncomputable def classicalSupportTranspose
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)))
    (a : (supportClosedDerivedPlus A i j hPair).obj L ⟶ K) :
    L ⟶ (finiteClosedUpperShriek A i j).rightDerivedFunctorPlus.obj K :=
  (classicalSupportAdjunction A i j hPair).homEquiv L K a

/-- A distinguished triangle whose second arrow is the open unit is canonically the
support-localization triangle, including the boundary; its first component is the
transpose of its given first arrow. This component is independent of every completion
of a triangle morphism and is natural for natural families of first arrows.

Source: blueprint sk-prop-a1 proof, canonical identification of the supported first term
and boundary; Stacks Tags 09AA, 09BM, 0145 and 014A
(blueprint: lem-pur-classical-support-counit-identification).

Proof plan, following the five steps of the node:
1. Localize the exact closed inverse-image/direct-image adjunction using
`exactDerivedAdjunction` (def-weil-exact-derived-adjunction). Its counit is invertible
by lem-exc-proetale-closed-fully-faithful; the localized inverse is its degreewise inverse.
Restrict to bounded below objects. Thus the termwise closed direct image is fully faithful.
2. The support adjunction of lem-pur-support-localization-triangle identifies maps
L to SK with maps i_*L to K, by postcomposition with its counit. Combined with full
faithfulness this says that a map i_*L to i_*SK over the first arrow is unique.
3. Rotate the given and support triangles. TR3 completes the identities on K and
Rj_*j^*K. Deshift the remaining component; cancelling the two rotation minus signs
shows its composite with the counit is a. Step 2 identifies it with i_* of the transpose.
The other triangle square gives compatibility with the specified third arrow.
4. Apply lem-sf-triangle-morphism-iso to the identity middle and third components.
Reflect invertibility through full faithfulness. Componentwise invertibility gives the
triangle isomorphism of def-weil-pbc-triangles-with-shift, with the prescribed boundary.
5. Step 2 forces every completion to have the same first component. Naturality of the
counit and the adjunction bijection give theta(a) followed by S(v) = u followed by
theta(a') whenever a followed by v = i_*(u) followed by a'. This proves naturality.
-/
theorem classicalSupportCounitIdentification
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)))
    (a : (supportClosedDerivedPlus A i j hPair).obj L ⟶ K)
    (b : (((lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctorPlus.obj
        ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus.obj K)).obj) ⟶
      ((supportClosedDerivedPlus A i j hPair).obj L).obj⟦(1 : ℤ)⟧)
    (htriangle : Triangle.mk (DerivedCategory.Plus.ι.map a)
      (DerivedCategory.Plus.ι.map
        ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) j).unit.app K)) b ∈
      distTriang (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))) :
    (supportClosedDerivedPlus A i j hPair).map
      (classicalSupportTranspose A i j hPair K L a) ≫
        (classicalSupportAdjunction A i j hPair).counit.app K = a ∧
    IsIso (classicalSupportTranspose A i j hPair K L a) ∧
    (∃ e : Triangle.mk (DerivedCategory.Plus.ι.map a)
        (DerivedCategory.Plus.ι.map
          ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) j).unit.app K)) b ≅
        classicalSupportTriangle A i j hPair K,
      e.hom.hom₁ = DerivedCategory.Plus.ι.map
        ((supportClosedDerivedPlus A i j hPair).map
          (classicalSupportTranspose A i j hPair K L a)) ∧
      e.hom.hom₂ = 𝟙 K.obj ∧ e.hom.hom₃ = 𝟙 _) ∧
    (∀ c : Triangle.mk (DerivedCategory.Plus.ι.map a)
        (DerivedCategory.Plus.ι.map
          ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) j).unit.app K)) b ⟶
        classicalSupportTriangle A i j hPair K,
      c.hom₂ = 𝟙 K.obj → c.hom₃ = 𝟙 _ →
      c.hom₁ = DerivedCategory.Plus.ι.map
        ((supportClosedDerivedPlus A i j hPair).map
          (classicalSupportTranspose A i j hPair K L a))) ∧
    (∀ (K' : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
      (L' : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)))
      (a' : (supportClosedDerivedPlus A i j hPair).obj L' ⟶ K')
      (b' : (((lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctorPlus.obj
          ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus.obj K')).obj) ⟶
        ((supportClosedDerivedPlus A i j hPair).obj L').obj⟦(1 : ℤ)⟧),
      Triangle.mk (DerivedCategory.Plus.ι.map a')
        (DerivedCategory.Plus.ι.map
          ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) j).unit.app K')) b' ∈
          distTriang (DerivedCategory
            (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) →
      ∀ (u : L ⟶ L') (v : K ⟶ K'),
        a ≫ v = (supportClosedDerivedPlus A i j hPair).map u ≫ a' →
        classicalSupportTranspose A i j hPair K L a ≫
          (finiteClosedUpperShriek A i j).rightDerivedFunctorPlus.map v =
        u ≫ classicalSupportTranspose A i j hPair K' L' a') := by
  sorry

end AlgebraicGeometry.ProEtale
