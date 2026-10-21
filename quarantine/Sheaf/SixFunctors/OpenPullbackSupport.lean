/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.OpenTensorNormalizationData
import all Sheaf.Algebra.Homology.DerivedCoefficientMapDescent
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-! # Pullback of objects extended from an open -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.OpenTensorNormalization

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxSize 4096 in
private theorem resolving_exists
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u + 1}) (K : CochainComplex (Mod R) ℤ) :
    ∃ (P : CochainComplex (Mod R) ℤ) (s : P ⟶ K), resolving R P ∧ QuasiIso s := by
  obtain ⟨P, s, hp, hf, hs, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients K
  refine ⟨P, s, ⟨hp, fun n ↦ ?_⟩, hs⟩
  exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (P.X n)).symm (hf n)

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxSize 4096 in
private theorem pullback_absolute
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u + 1}} {S : Sheaf K CommRingCat.{u + 1}}
    {V : Mod S ⥤ Mod R} (p : Pullback R S V)
    {E : Type*} [Category E] (H : Der S ⥤ E) :
    H.PreservesRightKanExtension
      (p.ordinary.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) DerivedCategory.Qh := by
  let q := HomotopyCategory.quotient (Mod R) (.up ℤ)
  let W := HomotopyCategory.quasiIso (Mod R) (.up ℤ)
  let F := p.ordinary.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let P : Set (HomotopyCategory (Mod R) (.up ℤ)) :=
    fun X ↦ ∃ Y, resolving R Y ∧ q.obj Y = X
  have hres : ∀ X, ∃ (Y : HomotopyCategory (Mod R) (.up ℤ)) (s : Y ⟶ X),
      Y ∈ P ∧ W s := by
    intro X
    obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨Y, s, hY, hs⟩ := resolving_exists R X
    exact ⟨q.obj Y, q.map s, ⟨Y, hY, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  have heps : ∀ X, X ∈ P → IsIso (p.epsilon.app X) := by
    rintro _ ⟨Y, hY, rfl⟩
    have h := p.flat Y hY
    dsimp only [derivedPullbackComplexComparison] at h
    simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using h
  have hinv : ∀ X Y (s : X ⟶ Y), X ∈ P → Y ∈ P → W s → IsIso (F.map s) := by
    intro X Y s hX hY hs
    have := heps X hX
    have := heps Y hY
    have : IsIso (DerivedCategory.Qh.map s) := Localization.inverts _ W s hs
    rw [← isIso_comp_left_iff (p.epsilon.app X), ← p.epsilon.naturality s]
    change IsIso (p.derived.map (DerivedCategory.Qh.map s) ≫ p.epsilon.app Y)
    infer_instance
  have : W.HasTwoOutOfThreeProperty :=
    (HomotopyCategory.quasiIso_saturated_triangulated (Mod R)).2.2.2.2.1
  exact Functor.pro_absolute W DerivedCategory.Qh F H (fun X ↦ by
    obtain ⟨Y, _, hY, _⟩ := Functor.resolvingClass_essentialConstancy W F P hres hinv X
    exact ⟨Y, hY⟩)

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxSize 4096 in
private noncomputable def pullback_derivedAdjunction
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u + 1}} {S : Sheaf K CommRingCat.{u + 1}}
    {V : Mod S ⥤ Mod R} [V.Additive] [Abelian.HasKInjectiveResolutions (Mod S)]
    (p : Pullback R S V) : p.derived ⊣ V.rightDerivedFunctor := by
  letI := p.universal
  letI := Functor.IsLeftDerivedFunctor.isRightKanExtension p.derived p.epsilon
    (HomotopyCategory.quasiIso (Mod R) (.up ℤ))
  letI := pullback_absolute p V.rightDerivedFunctor
  letI : (p.derived ⋙ V.rightDerivedFunctor).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight p.epsilon V.rightDerivedFunctor)
      (HomotopyCategory.quasiIso (Mod R) (.up ℤ)) := ⟨inferInstance⟩
  letI : (V.rightDerivedFunctor ⋙ p.derived).IsRightDerivedFunctor
      (Functor.whiskerRight V.rightDerivedFunctorUnit p.derived ≫
        (Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso (Mod S) (.up ℤ)) :=
    (HomotopyCategory.KInjectives.localizerMorphism (Mod S))
      |>.isRightDerivedFunctor_comp_of_isRightDerivabilityStructure _
        (fun I ↦ (HomotopyCategory.KInjectives.localizerMorphism_derives
          _).isIso_of_isRightDerivedFunctor _ I) _
  exact (p.adjunction.mapHomotopyCategory (.up ℤ)).derived
    (HomotopyCategory.quasiIso (Mod R) (.up ℤ))
    (HomotopyCategory.quasiIso (Mod S) (.up ℤ))
    p.epsilon V.rightDerivedFunctorUnit

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxSize 4096 in
/-- Derived pullback preserves the essential image of open extension by zero.
Only support is asserted; no choice or normalization of a base-change map is assumed.

Proof: the flat-model comparison and flat-term K-flat resolutions make each
specified left-derived pullback absolute. Derive its ordinary module adjunction
against the canonical K-injective right-derived direct image. Exact restriction
commutes with right derivation on the target side; on the source side it preserves
K-injectives because its left adjoint, open extension, is exact. Thus the given
ordinary direct-image square induces the corresponding square of derived right
adjoints. Uniqueness of composite left adjoints identifies derived pullback after
open extension with open extension after the corner derived pullback. The corner
pullback of M is the required essential-image witness. This uses only the supplied
operation data, so applies uniformly to ordinary and vertical diagram sites and
to every allowed coefficient map.
Source: Stacks, sites-modules.tex, Tags 04J0, 0E8I and the composite-adjunction
comparison; sites-cohomology.tex, Tags 06YY, 0G7E and 06YS.
(blueprint: lem-sf-open-pullback-support). -/
theorem derivedPullback_openSupported {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    (o : Operations d t) (M : Der (restrictRing m d.j d.R)) :
    o.opens.jShriek'.essImage (o.gPull.derived.obj (o.opens.jShriek.obj M)) := by
  let V := direct m d.g d.R d.S d.coefficient
  let VU := direct m d.gU _ _ (cornerCoefficient t)
  let r := restrict m d.j d.R
  let r' := restrict m d.j' d.S
  have : V.Additive := o.gPull.adjunction.right_adjoint_additive
  have : VU.Additive := o.gUPull.adjunction.right_adjoint_additive
  have : Abelian.HasKInjectiveResolutions (Mod d.S) := by
    have := (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses
      (topology m d.X') d.S).1
    infer_instance
  have : Abelian.HasKInjectiveResolutions (Mod (restrictRing m d.j' d.S)) := by
    have := (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses
      (topology m d.U') (restrictRing m d.j' d.S)).1
    infer_instance
  have : r'.PreservesKInjectiveComplexes :=
    o.opens.extension'.adjunction.preservesKInjectiveComplexes
  let a := o.opens.adj.comp (pullback_derivedAdjunction o.gPull)
  let b := (pullback_derivedAdjunction o.gUPull).comp o.opens.adj'
  let e : V.rightDerivedFunctor ⋙ r.mapDerivedCategory ≅
      r'.mapDerivedCategory ⋙ VU.rightDerivedFunctor :=
    (Functor.rightDerivedFunctorCompMapDerivedCategoryIso V r).symm ≪≫
      Functor.rightDerivedFunctorNatIso o.rightSquare ≪≫
      Functor.rightDerivedFunctorCompIso r' VU ≪≫
      Functor.isoWhiskerRight r'.rightDerivedFunctorIsoMapDerivedCategory
        VU.rightDerivedFunctor
  let c := Adjunction.leftAdjointUniq (a.ofNatIsoRight e) b
  exact ⟨o.gUPull.derived.obj M, ⟨(c.app M).symm⟩⟩

end SheafOfModules.OpenTensorNormalization
