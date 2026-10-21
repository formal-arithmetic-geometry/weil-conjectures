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

private noncomputable def classicalSupportFullyFaithful :
    (supportClosedDerivedPlus A i j hPair).FullyFaithful := by
  have := preservesFiniteColimits_lowerStar_of_isCompl (R := A) i j hPair
  let adj := upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i
  let F := upperStar (ModuleCat.{u + 1} A) i
  let G := lowerStar (ModuleCat.{u + 1} A) i
  let da := SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction adj
  let ff := da.fullyFaithfulROfCompIsoId
      ((Functor.mapDerivedCategoryCompIso G F).symm ≪≫
        Functor.mapDerivedCategoryNatIso (asIso adj.counit) ≪≫
          Functor.mapDerivedCategoryIdIso _)
  let ff' : (DerivedCategory.Plus.ι ⋙ G.mapDerivedCategory).FullyFaithful :=
    (ObjectProperty.fullyFaithfulι _).comp ff
  exact (ff'.ofIso
    (lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategoryPlusCompatibility.symm).ofCompFaithful

private theorem classicalSupportTriangle_distinguished
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :
    classicalSupportTriangle A i j hPair K ∈
      distTriang (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) := by
  let models := (supportLocalizationTriangle A i j hPair).choose_spec.2.1 K
  let I := models.choose
  let hI := models.choose_spec.choose
  let hq := models.choose_spec.choose_spec.choose
  let eB := models.choose_spec.choose_spec.choose_spec.choose
  have hs := models.choose_spec.choose_spec.choose_spec.choose_spec
  let eA := supportFirstModelComparison A i j hPair I hI K eB
  let eC := supportThirdModelComparison A j I hI K eB
  let e : supportModelTriangle A i j hPair I hq ≅
      classicalSupportTriangle A i j hPair K :=
    Triangle.isoMk _ _ eA eB eC hs.2.1 hs.2.2 (by
      change _ ≫ eA.hom⟦(1 : ℤ)⟧' = eC.hom ≫ (eC.inv ≫ _ ≫ eA.hom⟦(1 : ℤ)⟧')
      simp only [Iso.hom_inv_id_assoc]
      rfl)
  exact isomorphic_distinguished _ hs.1 _ e.symm

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
  let F := supportClosedDerivedPlus A i j hPair
  let adj := classicalSupportAdjunction A i j hPair
  let θ := classicalSupportTranspose A i j hPair K L a
  let ff := classicalSupportFullyFaithful A i j hPair
  have : F.Full := ff.full
  have : F.Faithful := ff.faithful
  have hθ : F.map θ ≫ adj.counit.app K = a := by
    exact ((adj.homEquiv L K).symm_apply_apply a)
  have unique (c : (F.obj L).obj ⟶
      (F.obj ((finiteClosedUpperShriek A i j).rightDerivedFunctorPlus.obj K)).obj)
      (hc : c ≫ DerivedCategory.Plus.ι.map (adj.counit.app K) =
        DerivedCategory.Plus.ι.map a) :
      c = DerivedCategory.Plus.ι.map (F.map θ) := by
    let d := DerivedCategory.Plus.ι.preimage (X := F.obj L)
      (Y := F.obj ((finiteClosedUpperShriek A i j).rightDerivedFunctorPlus.obj K)) c
    let t := F.preimage d
    have ht : F.map t = d := F.map_preimage d
    have hd : d ≫ adj.counit.app K = a := by
      apply DerivedCategory.Plus.ι.map_injective
      simpa only [Functor.map_comp, Functor.map_preimage, d] using hc
    have htθ : t = θ := by
      apply (adj.homEquiv L K).symm.injective
      change F.map t ≫ adj.counit.app K = (adj.homEquiv L K).symm (adj.homEquiv L K a)
      rw [ht, hd, Equiv.symm_apply_apply]
    rw [← htθ, ht, Functor.map_preimage]
  let T := Triangle.mk (DerivedCategory.Plus.ι.map a)
    (DerivedCategory.Plus.ι.map
      ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) j).unit.app K)) b
  let T' := classicalSupportTriangle A i j hPair K
  have hT' := classicalSupportTriangle_distinguished A i j hPair K
  obtain ⟨c, hc₁, hc₃⟩ := complete_distinguished_triangle_morphism₁ T T'
    htriangle hT' (𝟙 _) (𝟙 _) (by simp [T, T', classicalSupportTriangle])
  have hc : c = DerivedCategory.Plus.ι.map (F.map θ) := unique c (by
    simpa only [T, T', classicalSupportTriangle, Triangle.mk_mor₁, Category.comp_id]
      using hc₁.symm)
  let φ : T ⟶ T' := Triangle.homMk T T' c (𝟙 _) (𝟙 _) hc₁
    (by simp [T, T', classicalSupportTriangle]) hc₃
  have hi : IsIso c := isIso₁_of_isIso₂₃ φ htriangle hT'
    (inferInstanceAs (IsIso (𝟙 K.obj))) (inferInstanceAs (IsIso (𝟙 T.obj₃)))
  have : IsIso (DerivedCategory.Plus.ι.map (F.map θ)) := hc ▸ hi
  have : IsIso (F.map θ) := isIso_of_reflects_iso _ DerivedCategory.Plus.ι
  have : IsIso θ := isIso_of_reflects_iso _ F
  refine ⟨hθ, ‹IsIso θ›, ?_, ?_, ?_⟩
  · have : IsIso φ := Triangle.isIso_of_isIsos φ hi
      (inferInstanceAs (IsIso (𝟙 K.obj))) (inferInstanceAs (IsIso (𝟙 T.obj₃)))
    exact ⟨asIso φ, hc, rfl, rfl⟩
  · intro ψ hψ₂ hψ₃
    apply unique ψ.hom₁
    have h := ψ.comm₁
    rw [hψ₂] at h
    change DerivedCategory.Plus.ι.map a ≫ 𝟙 K.obj =
      ψ.hom₁ ≫ DerivedCategory.Plus.ι.map (adj.counit.app K) at h
    exact h.symm.trans (Category.comp_id _)
  · intro K' L' a' b' htriangle' u v huv
    change adj.homEquiv L K a ≫ _ = u ≫ adj.homEquiv L' K' a'
    rw [← adj.homEquiv_naturality_right, huv, adj.homEquiv_naturality_left]

end AlgebraicGeometry.ProEtale
