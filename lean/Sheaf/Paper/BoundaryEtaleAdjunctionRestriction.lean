/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q94
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.Compactification.Refinement
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Adjunction.Restrict
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishingTorsion
import Sheaf.CategoryTheory.RightDerivedFunctorUpperBound

/-!
# Bounded-below ordinary etale compact-support adjunctions

Source: Weil blueprint, sec-six-functors/sk-prop-sf-biduality-general,
cor-weil-boundary-duality-discharge.md, first proof paragraph; Bhatt--Scholze,
The pro-etale topology for schemes, Corollary 5.1.6
(blueprint: lem-weil-boundary-etale-adjunction-restriction).

The proposition below packages exactly the geometric preparation, restriction of the
ordinary ambient adjunction, reflection of lower bounds, and image of the specified
comparison unit. All derived categories use the fixed constant-ring module presentation.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- For a fixed compactification, the ambient ordinary etale right adjoint preserves
D+, and the full-subcategory adjunction is the restriction of this very adjunction.
The final map is the image of the canonical unbounded derived comparison unit.
Source: boundary-duality discharge, preparation of ordinary etale costalk adjunctions;
Bhatt--Scholze, Corollary 5.1.6
(blueprint: lem-weil-boundary-etale-adjunction-restriction). -/
def BoundaryEtaleCompactificationAdjunction (Λ : Type (u + 1)) [CommRing Λ]
    {V W : Scheme.{u}} {h : V ⟶ W} (c : Compactification h) : Prop :=
  ∃ (R : DerivedCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c ⊣ R),
    (∀ K : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      DerivedCategory.TStructure.t.plus K → DerivedCategory.TStructure.t.plus
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj K)) ∧
    (∀ L : DerivedCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      DerivedCategory.TStructure.t.plus L → DerivedCategory.TStructure.t.plus (R.obj L)) ∧
    (∃ (Rplus : DerivedCategory.Plus (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
        DerivedCategory.Plus (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (eR : DerivedCategory.Plus.ι ⋙ R ≅ Rplus ⋙ DerivedCategory.Plus.ι)
      (adjPlus : rightDerivedLowerShriekOfCompactificationPlus
        (ModuleCat.{u + 1} Λ) c ⊣ Rplus),
      adjPlus = adj.restrictFullyFaithful
        (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
        (rightDerivedLowerShriekOfCompactificationPlusCompatibility
          (ModuleCat.{u + 1} Λ) c).symm eR) ∧
    (∀ L : DerivedCategory.Plus (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      IsIso ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategory.map
        (R.map ((ProEtale.derivedComparisonAdjunction
          (ModuleCat.{u + 1} Λ) W).unit.app L.obj))) ∧
      DerivedCategory.TStructure.t.plus
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategory.obj
          (R.obj L.obj)) ∧
      DerivedCategory.TStructure.t.plus
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategory.obj
          (R.obj (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) W).mapDerivedCategory ⋙
            (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} Λ) W).rightDerivedFunctor).obj
              L.obj))))

/-- The full conclusion: existence of a compactification, Noetherianity and
quasi-separatedness, finite type and finite dimension for every compactification,
its ordinary adjunction and restriction, and reflection of every lower bound on
arbitrary unbounded etale input. A natural number dimension bound includes zero
and does not exclude the empty scheme.
Source: boundary-duality discharge, first proof paragraph
(blueprint: lem-weil-boundary-etale-adjunction-restriction). -/
def BoundaryEtaleAdjunctionRestriction (Λ : Type (u + 1)) [CommRing Λ]
    {V W S : Scheme.{u}} (h : V ⟶ W) (aW : W ⟶ S) : Prop :=
  Nonempty (Compactification h) ∧ IsNoetherian V ∧ IsNoetherian W ∧
    QuasiSeparatedSpace V ∧ QuasiSeparatedSpace W ∧
    (∀ c : Compactification h,
      IsNoetherian c.Z ∧ QuasiSeparatedSpace c.Z ∧
      LocallyOfFiniteType (c.g ≫ aW) ∧ QuasiCompact (c.g ≫ aW) ∧
      (∃ d : ℕ, topologicalKrullDim c.Z ≤ (d : WithBot ℕ∞)) ∧
      BoundaryEtaleCompactificationAdjunction Λ c) ∧
    (∀ (C : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (b : ℤ),
      DerivedCategory.TStructure.t.IsGE
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategory.obj C) b ↔
      DerivedCategory.TStructure.t.IsGE C b)

/-- Compact support and its ambient right adjoint restrict to D+, with the ambient
Hom bijections, unit and counit; comparison reflects arbitrary lower bounds and
carries the right-adjoint image of the specified comparison unit to an isomorphism
between bounded-below objects. No boundedness of the right-adjoint image is assumed.
Source: boundary-duality discharge, first proof paragraph; Bhatt--Scholze,
The pro-etale topology for schemes, Corollary 5.1.6
(blueprint: lem-weil-boundary-etale-adjunction-restriction).

Proof:
1. The finite coefficient ring is commutative and finite by
   def-weil-l-adic-coefficient-extension, hence additively torsion. The field spectrum
   is Noetherian. Apply lem-weil-pbc-finite-type-over-noetherian and
   lem-weil-pbc-locally-noetherian-quasi-separated to V and W. Nagata's theorem
   thm-nagata-compactification gives a compactification of the separated finite-type h.
2. For every c, its proper map is finite type. Compose with aW using
   lem-sfb-finite-type-composition-base-change. The same Noetherian and quasi-separated
   lemmas apply to c.Z. Use lem-kun-dimension-finite-type to obtain a natural number
   dimension bound; zero works for the empty scheme. Density of the open is unnecessary.
3. Apply thm-amb-etale-exceptional-adjoint to obtain the ordinary ambient adjunction.
4. Exact extension by zero (lem-weil-pbc-extension-by-zero-exact and
   lem-weil-pbc-exact-functor-complex-cohomology) preserves lower bounds. Direct image
   is left exact by lem-weil-pbc-module-direct-image-left-exact. The sheaf categories
   are Grothendieck abelian by lem-pur-ringed-site-grothendieck-abelian. Apply
   lem-weil-pbc-derived-functor-negative-vanishing and
   src-right-derived-functor-plus-compatibility to show F_c preserves D+.
5. By lem-kun-relative-torsion-direct-image-dimension-bound, higher direct image under
   p vanishes above 2d. Use the Grothendieck property, enough injectives from
   lem-weil-pbc-module-sheaves-enough-injectives and K-injectives from
   prop-weil-pbc-kinjective-resolutions-exist in lem-etale-derived-functor-upper-amplitude.
   Exact j_! gives F_c(D^{≤m}) contained in D^{≤m+2d}, even on unbounded inputs.
   Orthogonality, as in lem-etale-upper-shriek-explicit-amplitude-interface, now gives
   preservation of D+ by R_c, before restricting the adjunction.
6. Restrict the ambient Hom bijections along the fully faithful D+ inclusions using
   Adjunction.restrictFullyFaithful. Its unit and counit formulas identify them with
   the ambient ones under the compatibility isomorphisms.
7. Exactness from lem-sf-comparison-pullback-exact identifies every cohomology sheaf
   of S_V C with S_V of that cohomology sheaf. The site-comparison theorem
   thm-weil-pbc-site-comparison implies faithfulness on sheaves placed in degree zero.
   Consequently S_V detects zero cohomology and reflects every lower bound, with
   no boundedness assumption on C.
8. The actual comparison unit at L in D+ is invertible by
   thm-weil-pbc-site-comparison. Its target is bounded below as well. Step 5 puts
   their R_c-images in D+, and step 7 puts their S_V-images in D+.
   Applying S_V R_c to that unit preserves its inverse and gives the specified map.
-/
theorem boundary_etale_adjunction_restriction
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (_hn : 1 ≤ n) {V W : Scheme.{u}}
    (aV : V ⟶ Spec (.of D.k)) (aW : W ⟶ Spec (.of D.k))
    [IsSeparated aV] [LocallyOfFiniteType aV] [QuasiCompact aV]
    [IsSeparated aW] [LocallyOfFiniteType aW] [QuasiCompact aW]
    (h : V ⟶ W) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (_hover : h ≫ aW = aV) :
    BoundaryEtaleAdjunctionRestriction
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) h aW := by
  classical
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let Λ := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)
  have : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n _hn
  have : Finite Λ := inferInstance
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian aV
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace aV
  have : IsNoetherian V := ⟨⟩
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian aW
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace aW
  have : IsNoetherian W := ⟨⟩
  refine ⟨⟨NagataCompactification h⟩, inferInstance, inferInstance,
    inferInstance, inferInstance, ?_, ?_⟩
  · intro c
    have : LocallyOfFiniteType (c.g ≫ aW) := inferInstance
    have : QuasiCompact (c.g ≫ aW) := inferInstance
    have : IsLocallyNoetherian c.Z :=
      LocallyOfFiniteType.isLocallyNoetherian (c.g ≫ aW)
    have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace (c.g ≫ aW)
    have : IsNoetherian c.Z := ⟨⟩
    obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le (c.g ≫ aW)
    refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ⟨d, hd⟩, ?_⟩
    let A := ModuleCat.{u + 1} Λ
    let F := rightDerivedLowerShriekOfCompactification A c
    let P := lowerStar A c.g
    let J := openImmersionLowerShriek A c.i
    have hvan (M : Sheaf c.Z.smallEtaleTopology A) (q : ℕ) (hq : 2 * d < q) :
        IsZero ((P.rightDerived q).obj M) := by
      have hz := isZero_higherDirectImage_of_two_mul_lt
        (Λ := Λ) isAddTorsion_of_finite c.g (c.g ≫ aW) aW rfl d hd M q
        (by exact_mod_cast hq)
      exact hz.of_iso (P.homologyRightDerivedFunctorPlusObjSingleFunctorIso M q).symm
    let N : ℤ := (2 * d : ℕ)
    have hAmp (K : DerivedCategory (Sheaf V.smallEtaleTopology A)) (b : ℤ)
        (hK : K.IsLE b) : (F.obj K).IsLE (b + N) := by
      have : K.IsLE b := hK
      exact P.isLE_rightDerivedFunctor_obj_of_dimension (2 * d) hvan _ b
        (J.isLE_mapDerivedCategory_obj K b)
    have : F.IsLeftAdjoint := isLeftAdjoint_rightDerivedLowerShriekOfCompactification Λ c
    let R := F.rightAdjoint
    let adj : F ⊣ R := Adjunction.ofIsLeftAdjoint F
    have hR (L : DerivedCategory (Sheaf W.smallEtaleTopology A))
        (hL : DerivedCategory.TStructure.t.plus L) :
        DerivedCategory.TStructure.t.plus (R.obj L) := by
      obtain ⟨b, hb⟩ := hL
      refine ⟨b - N, ?_⟩
      rw [DerivedCategory.TStructure.t.isGE_iff_orthogonal
        (b - N - 1) (b - N) (by omega)]
      intro K φ hK
      have hFK : (F.obj K).IsLE (b - 1) := by
        convert hAmp K (b - N - 1) hK using 1
        omega
      apply (adj.homEquiv K L).symm.injective
      rw [adj.homAddEquiv_symm_zero]
      exact DerivedCategory.TStructure.t.zero _ (b - 1) b (by omega)
    have hF (K : DerivedCategory (Sheaf V.smallEtaleTopology A))
        (hK : DerivedCategory.TStructure.t.plus K) :
        DerivedCategory.TStructure.t.plus (F.obj K) :=
      DerivedCategory.TStructure.t.plus.prop_of_iso
        ((rightDerivedLowerShriekOfCompactificationPlusCompatibility A c).app ⟨K, hK⟩)
        (rightDerivedLowerShriekOfCompactificationPlus A c |>.obj ⟨K, hK⟩).property
    let Rplus := DerivedCategory.TStructure.t.plus.lift (DerivedCategory.Plus.ι ⋙ R)
      (fun L ↦ hR L.obj L.property)
    let eR : DerivedCategory.Plus.ι ⋙ R ≅ Rplus ⋙ DerivedCategory.Plus.ι := Iso.refl _
    let adjPlus := adj.restrictFullyFaithful
      (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
      (rightDerivedLowerShriekOfCompactificationPlusCompatibility A c).symm eR
    refine ⟨R, adj, hF, hR, ⟨Rplus, eR, adjPlus, rfl⟩, ?_⟩
    intro L
    have hunit := ProEtale.isIso_derivedComparisonAdjunction_unit_app A W L.obj L.property
    have ht : DerivedCategory.TStructure.t.plus
        (((ProEtale.comparisonUpperStar A W).mapDerivedCategory ⋙
          (ProEtale.comparisonLowerStar A W).rightDerivedFunctor).obj L.obj) :=
      DerivedCategory.TStructure.t.plus.prop_of_iso
        (asIso ((ProEtale.derivedComparisonAdjunction A W).unit.app L.obj)) L.property
    have hS (K : DerivedCategory (Sheaf V.smallEtaleTopology A))
        (hK : DerivedCategory.TStructure.t.plus K) :
        DerivedCategory.TStructure.t.plus
          ((ProEtale.comparisonUpperStar A V).mapDerivedCategory.obj K) := by
      obtain ⟨b, hb⟩ := hK
      have : K.IsGE b := hb
      exact ⟨b, (ProEtale.comparisonUpperStar A V).isGE_mapDerivedCategory_obj K b⟩
    exact ⟨inferInstance, hS _ (hR _ L.property), hS _ (hR _ ht)⟩
  · intro C b
    let S := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) V
    constructor
    · intro hC
      exact (DerivedCategory.isGE_iff C b).2 fun i hi ↦
        S.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
          ((DerivedCategory.isGE_iff _ b).1 hC i hi)
    · intro hC
      have : C.IsGE b := hC
      exact S.isGE_mapDerivedCategory_obj C b

end AlgebraicGeometry.Etale
