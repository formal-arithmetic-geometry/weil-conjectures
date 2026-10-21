/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.CategoryTheory.NormalizedDerivedComparisonCommonResolution
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Composition of K-injective-normalized derived comparisons

Source: Stacks Project, derived.tex, Tag 070Y (`lemma-K-injective-defined`), and the
explicit successive-resolution composition argument in the DAG
(blueprint: lem-sf-normalized-derived-comparison-composition).

The normalization uses the shared resolution and localization identifications. No exact
restriction functor is required to preserve K-injective complexes.
-/

@[expose] public section

set_option autoImplicit false

universe u0 u1 u2 v0 v1 v2 w0 w1 w2
universe uA0 uA1 uA2 uB0 uB1 uB2 vA0 vA1 vA2 vB0 vB1 vB2
universe wA0 wA1 wA2 wB0 wB1 wB2

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- The canonical localization identification for a specified equality of exact functors.
Source: the canonical localization identifications stipulated in the composition statement;
Stacks Tag 070Y (blueprint: lem-sf-normalized-derived-comparison-composition).
This is the existing induced equality isomorphism followed by the existing composition
isomorphism, with the exactness instances of the composite supplied explicitly. -/
noncomputable def normalizedDerivedComparisonCompositionLocalizationIso
    {C0 : Type u0} {C1 : Type u1} {C2 : Type u2}
    [Category.{v0} C0] [Category.{v1} C1] [Category.{v2} C2]
    [Abelian C0] [Abelian C1] [Abelian C2]
    [HasDerivedCategory.{w0} C0] [HasDerivedCategory.{w1} C1]
    [HasDerivedCategory.{w2} C2]
    (r02 : C2 ⥤ C0) (r12 : C2 ⥤ C1) (r01 : C1 ⥤ C0)
    [r02.Additive] [r12.Additive] [r01.Additive]
    [PreservesFiniteLimits r02] [PreservesFiniteColimits r02]
    [PreservesFiniteLimits r12] [PreservesFiniteColimits r12]
    [PreservesFiniteLimits r01] [PreservesFiniteColimits r01]
    (e : r02 = r12 ⋙ r01) :
    r02.mapDerivedCategory ≅ r12.mapDerivedCategory ⋙ r01.mapDerivedCategory :=
  letI := comp_preservesFiniteLimits r12 r01
  letI := comp_preservesFiniteColimits r12 r01
  mapDerivedCategoryNatIso (eqToIso e) ≪≫ mapDerivedCategoryCompIso r12 r01

/-- Precisely the supplied normalization on every K-injective complex and every resolution
of its restricted complex, including invertibility of the termwise F-image of that resolution.
Source: the normalization displayed in the node, Stacks Tag 070Y
(blueprint: lem-sf-normalized-derived-comparison-composition).
The identity-resolution comparison for G is its inverse derived unit, with the shared
Q/Qh identifications; the final target isomorphism implements Fr = sG. -/
def IsKInjectiveNormalizedDerivedComparison
    {A : Type u0} {A' : Type u1} {B : Type u2} {B' : Type uB0}
    [Category.{v0} A] [Category.{v1} A'] [Category.{v2} B] [Category.{vB0} B']
    [Abelian A] [Abelian A'] [Abelian B] [Abelian B']
    [HasDerivedCategory.{w0} A] [HasDerivedCategory.{w1} A']
    [HasDerivedCategory.{w2} B] [HasDerivedCategory.{wB0} B']
    (F : A ⥤ B) (G : A' ⥤ B') [F.Additive] [G.Additive]
    (r : A' ⥤ A) (s : B' ⥤ B) [r.Additive] [s.Additive]
    [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    [PreservesFiniteLimits s] [PreservesFiniteColimits s]
    (e : r ⋙ F = G ⋙ s)
    (enoughA : ∀ K : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (a : K ⟶ I), I.IsKInjective ∧ QuasiIso a)
    (enoughA' : ∀ K : CochainComplex A' ℤ,
      ∃ (I : CochainComplex A' ℤ) (a : K ⟶ I), I.IsKInjective ∧ QuasiIso a)
    (β : r.mapDerivedCategory ⋙ F.rightDerivedFunctorOfQuasiIsoResolutions enoughA ≅
      G.rightDerivedFunctorOfQuasiIsoResolutions enoughA' ⋙ s.mapDerivedCategory) : Prop :=
  ∀ (H : CochainComplex A' ℤ) [H.IsKInjective]
    (I : CochainComplex A ℤ) [I.IsKInjective]
    (a : (r.mapHomologicalComplex (.up ℤ)).obj H ⟶ I) [QuasiIso a],
    ∃ hFa : IsIso (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map a)),
      (F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso enoughA a).inv ≫
        (normalizedDerivedComparisonComplexIso F G r s enoughA enoughA' β H).hom ≫
        s.mapDerivedCategory.map
          (G.rightDerivedFunctorOfQuasiIsoResolutionsObjIso enoughA' (𝟙 H)).hom ≫
        (normalizedDerivedComparisonTargetIso F G r s e H).inv =
      @CategoryTheory.inv _ _ _ _ _ hFa

set_option backward.isDefEq.respectTransparency false

/-- The derived unit on complexes, transported along the shared Q/Qh identifications.
Source: Stacks Tag 070Y (blueprint: lem-sf-normalized-derived-comparison-composition). -/
private noncomputable def comparisonUnit
    {A : Type u0} {B : Type u1} [Category.{v0} A] [Category.{v1} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{w0} A] [HasDerivedCategory.{w1} B]
    (F : A ⥤ B) [F.Additive]
    (enough : ∀ K : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (a : K ⟶ I), I.IsKInjective ∧ QuasiIso a) :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctorOfQuasiIsoResolutions enough where
  app K := (DerivedCategory.quotientCompQhIso B).inv.app _ ≫
    (F.rightDerivedFunctorOfQuasiIsoResolutionsUnit enough).app
      ((HomotopyCategory.quotient A (.up ℤ)).obj K) ≫
    (F.rightDerivedFunctorOfQuasiIsoResolutions enough).map
      ((DerivedCategory.quotientCompQhIso A).hom.app K)
  naturality K L f := by
    let η := F.rightDerivedFunctorOfQuasiIsoResolutionsUnit enough
    have hn := η.naturality ((HomotopyCategory.quotient A (.up ℤ)).map f)
    dsimp only [comp_map, comp_obj] at hn ⊢
    rw [(DerivedCategory.quotientCompQhIso B).inv.naturality_assoc]
    erw [reassoc_of% hn]
    simp only [Category.assoc, ← Functor.map_comp]
    erw [(DerivedCategory.quotientCompQhIso A).hom.naturality]

/-- Naturality of the unit computes its composite with every resolution comparison.
Source: Stacks Tag 070Y (blueprint: lem-sf-normalized-derived-comparison-composition). -/
private theorem comparisonUnit_resolution
    {A : Type u0} {B : Type u1} [Category.{v0} A] [Category.{v1} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{w0} A] [HasDerivedCategory.{w1} B]
    (F : A ⥤ B) [F.Additive]
    (enough : ∀ K : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (a : K ⟶ I), I.IsKInjective ∧ QuasiIso a)
    {K I : CochainComplex A ℤ} [I.IsKInjective] (a : K ⟶ I) [QuasiIso a] :
    (comparisonUnit F enough).app K ≫
        (F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso enough a).hom =
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map a) := by
  have := F.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso enough I
  have hn := (comparisonUnit F enough).naturality a
  dsimp only [comp_map] at hn
  dsimp only [rightDerivedFunctorOfQuasiIsoResolutionsObjIso, Iso.trans_hom,
    mapIso_hom, asIso_hom, Iso.symm_hom, Iso.app_inv, asIso_inv]
  rw [← Category.assoc, ← hn]
  simp [comparisonUnit, Category.assoc, ← Functor.map_comp_assoc]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section UnitSquare

variable
    {A : Type u0} {A' : Type u1} {B : Type u2} {B' : Type uB0}
    [Category.{v0} A] [Category.{v1} A'] [Category.{v2} B] [Category.{vB0} B']
    [Abelian A] [Abelian A'] [Abelian B] [Abelian B']
    [HasDerivedCategory.{w0} A] [HasDerivedCategory.{w1} A']
    [HasDerivedCategory.{w2} B] [HasDerivedCategory.{wB0} B']
    (F : A ⥤ B) (G : A' ⥤ B') [F.Additive] [G.Additive]
    (r : A' ⥤ A) (s : B' ⥤ B) [r.Additive] [s.Additive]
    [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    [PreservesFiniteLimits s] [PreservesFiniteColimits s]
    (e : r ⋙ F = G ⋙ s)
    (enoughA : ∀ K : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (a : K ⟶ I), I.IsKInjective ∧ QuasiIso a)
    (enoughA' : ∀ K : CochainComplex A' ℤ,
      ∃ (I : CochainComplex A' ℤ) (a : K ⟶ I), I.IsKInjective ∧ QuasiIso a)
    (β : r.mapDerivedCategory ⋙ F.rightDerivedFunctorOfQuasiIsoResolutions enoughA ≅
      G.rightDerivedFunctorOfQuasiIsoResolutions enoughA' ⋙ s.mapDerivedCategory)

/-- The supplied normalization is the derived-unit square at a K-injective complex.
Source: Stacks Tag 070Y (blueprint: lem-sf-normalized-derived-comparison-composition). -/
private theorem normalized_unit_square_kinjective
    (h : IsKInjectiveNormalizedDerivedComparison F G r s e enoughA enoughA' β)
    (H : CochainComplex A' ℤ) [H.IsKInjective] :
    (comparisonUnit F enoughA).app ((r.mapHomologicalComplex (.up ℤ)).obj H) ≫
        (normalizedDerivedComparisonComplexIso F G r s enoughA enoughA' β H).hom =
      (normalizedDerivedComparisonTargetIso F G r s e H).hom ≫
        s.mapDerivedCategory.map ((comparisonUnit G enoughA').app H) := by
  obtain ⟨I, a, hI, ha⟩ := enoughA ((r.mapHomologicalComplex (.up ℤ)).obj H)
  have := hI
  have := ha
  obtain ⟨hFa, hn⟩ := h H I a
  have := hFa
  have hc := comparisonUnit_resolution F enoughA a
  have hG := comparisonUnit_resolution G enoughA' (𝟙 H)
  simp only [Functor.map_id] at hG
  have hu : (comparisonUnit G enoughA').app H =
      (G.rightDerivedFunctorOfQuasiIsoResolutionsObjIso enoughA' (𝟙 H)).inv := by
    rw [← cancel_mono
      (G.rightDerivedFunctorOfQuasiIsoResolutionsObjIso enoughA' (𝟙 H)).hom]
    simpa using hG
  rw [hu]
  have hunit : (comparisonUnit F enoughA).app
      ((r.mapHomologicalComplex (.up ℤ)).obj H) =
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map a) ≫
        (F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso enoughA a).inv := by
    rw [← hc]
    simp
  rw [hunit]
  apply (cancel_epi (CategoryTheory.inv (DerivedCategory.Q.map
    ((F.mapHomologicalComplex (.up ℤ)).map a)))).mp
  simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  apply (cancel_mono (s.mapDerivedCategory.map
    (G.rightDerivedFunctorOfQuasiIsoResolutionsObjIso enoughA' (𝟙 H)).hom)).mp
  apply (cancel_mono (normalizedDerivedComparisonTargetIso F G r s e H).inv).mp
  simpa [Category.assoc, ← Functor.map_comp_assoc] using hn

/-- Resolve a complex and cancel its derived resolution map to extend the unit square.
Source: Stacks Tag 070Y (blueprint: lem-sf-normalized-derived-comparison-composition). -/
private theorem normalized_unit_square
    (h : IsKInjectiveNormalizedDerivedComparison F G r s e enoughA enoughA' β)
    (N : CochainComplex A' ℤ) :
    (comparisonUnit F enoughA).app ((r.mapHomologicalComplex (.up ℤ)).obj N) ≫
        (normalizedDerivedComparisonComplexIso F G r s enoughA enoughA' β N).hom =
      (normalizedDerivedComparisonTargetIso F G r s e N).hom ≫
        s.mapDerivedCategory.map ((comparisonUnit G enoughA').app N) := by
  obtain ⟨J, u, hJ, hu⟩ := enoughA' N
  have := hJ
  have := hu
  let RF := F.rightDerivedFunctorOfQuasiIsoResolutions enoughA
  let RG := G.rightDerivedFunctorOfQuasiIsoResolutions enoughA'
  let ru := (r.mapHomologicalComplex (.up ℤ)).map u
  have hβ : RF.map (DerivedCategory.Q.map ru) ≫
      (normalizedDerivedComparisonComplexIso F G r s enoughA enoughA' β J).hom =
      (normalizedDerivedComparisonComplexIso F G r s enoughA enoughA' β N).hom ≫
        s.mapDerivedCategory.map (RG.map (DerivedCategory.Q.map u)) := by
    dsimp only [normalizedDerivedComparisonComplexIso, Iso.trans_hom, mapIso_hom,
      Iso.symm_hom, Iso.app_inv]
    rw [← Category.assoc, ← RF.map_comp]
    change RF.map ((r.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).map u ≫
      r.mapDerivedCategoryFactors.inv.app J) ≫ _ = _
    rw [r.mapDerivedCategoryFactors.inv.naturality u, RF.map_comp]
    simpa only [Functor.comp_map, Category.assoc, Iso.app_hom] using
      congrArg (fun f ↦ RF.map (r.mapDerivedCategoryFactors.inv.app N) ≫ f)
        (β.hom.naturality (DerivedCategory.Q.map u))
  have ht : DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map ru) ≫
      (normalizedDerivedComparisonTargetIso F G r s e J).hom =
      (normalizedDerivedComparisonTargetIso F G r s e N).hom ≫
        s.mapDerivedCategory.map
          (DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map u)) := by
    dsimp only [normalizedDerivedComparisonTargetIso, Iso.trans_hom, mapIso_hom,
      Iso.symm_hom, Iso.app_inv]
    rw [← Category.assoc, ← DerivedCategory.Q.map_comp]
    erw [(NatIso.mapHomologicalComplex (eqToIso e) (.up ℤ)).hom.naturality u]
    rw [DerivedCategory.Q.map_comp]
    simp only [Category.assoc]
    change _ ≫ DerivedCategory.Q.map
      ((s.mapHomologicalComplex (.up ℤ)).map
        ((G.mapHomologicalComplex (.up ℤ)).map u)) ≫ _ = _
    have hn := s.mapDerivedCategoryFactors.inv.naturality
      ((G.mapHomologicalComplex (.up ℤ)).map u)
    dsimp only [Functor.comp_map] at hn
    rw [hn]
    rfl
  apply (cancel_mono (s.mapDerivedCategory.map
    (RG.map (DerivedCategory.Q.map u)))).mp
  calc
    _ = (comparisonUnit F enoughA).app _ ≫ RF.map (DerivedCategory.Q.map ru) ≫
        (normalizedDerivedComparisonComplexIso F G r s enoughA enoughA' β J).hom := by
      simp only [Category.assoc, hβ]
    _ = DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map ru) ≫
        (comparisonUnit F enoughA).app _ ≫
        (normalizedDerivedComparisonComplexIso F G r s enoughA enoughA' β J).hom := by
      have hn := (comparisonUnit F enoughA).naturality ru
      dsimp only [comp_map] at hn
      rw [← Category.assoc, ← hn, Category.assoc]
    _ = _ := by
      rw [normalized_unit_square_kinjective F G r s e enoughA enoughA' β h J]
      rw [← Category.assoc, ht]
      simp only [Category.assoc, ← Functor.map_comp]
      have hn := (comparisonUnit G enoughA').naturality u
      dsimp only [comp_map] at hn
      rw [hn]

end UnitSquare

section CompositionFactors

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Localization sends the identity comparison of exact functors to the identity.
Source: canonical localization factorizations
(blueprint: lem-sf-normalized-derived-comparison-composition). -/
private theorem mapDerivedCategoryNatIso_refl
    {C : Type u0} {D : Type u1} [Category.{v0} C] [Category.{v1} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{w0} C] [HasDerivedCategory.{w1} D]
    (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    mapDerivedCategoryNatIso (Iso.refl F) = Iso.refl F.mapDerivedCategory := by
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ))
  intro K
  apply (cancel_mono (F.mapDerivedCategoryFactors.hom.app K)).mp
  have hc := mapDerivedCategoryNatIso_fac (Iso.refl F) K
  dsimp only [Iso.refl_hom] at hc
  simp only [NatTrans.mapHomologicalComplex_id, NatTrans.id_app] at hc
  erw [Functor.map_id, Category.comp_id] at hc
  simpa only [Iso.refl_hom, NatTrans.id_app, Category.id_comp] using hc

/-- The inverse localization factorization respects exact-functor composition.
Source: canonical localization factorizations
(blueprint: lem-sf-normalized-derived-comparison-composition). -/
private theorem compositionFactors_inv
    {C0 : Type u0} {C1 : Type u1} {C2 : Type u2}
    [Category.{v0} C0] [Category.{v1} C1] [Category.{v2} C2]
    [Abelian C0] [Abelian C1] [Abelian C2]
    [HasDerivedCategory.{w0} C0] [HasDerivedCategory.{w1} C1]
    [HasDerivedCategory.{w2} C2]
    (F : C2 ⥤ C1) (G : C1 ⥤ C0) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (K : CochainComplex C2 ℤ) :
    (F ⋙ G).mapDerivedCategoryFactors.inv.app K ≫
        (mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj K) =
      G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app K) := by
  have hc := mapDerivedCategoryCompIso_fac F G K
  dsimp only [mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
    Iso.refl_hom] at hc
  simp only [NatTrans.mapHomologicalComplex_id, NatTrans.id_app] at hc
  erw [Functor.map_id, Category.comp_id] at hc
  apply (cancel_mono (G.mapDerivedCategory.map
    (F.mapDerivedCategoryFactors.hom.app K))).mp
  apply (cancel_mono (G.mapDerivedCategoryFactors.hom.app
    ((F.mapHomologicalComplex (.up ℤ)).obj K))).mp
  have hh := congrArg (fun f ↦ (F ⋙ G).mapDerivedCategoryFactors.inv.app K ≫ f) hc
  simp only [Iso.inv_hom_id_app] at hh
  convert hh using 1 <;> first | rfl | simp [Category.assoc]
  all_goals
    dsimp only [Functor.mapHomologicalComplex, Functor.comp_obj] at *
    rfl

end CompositionFactors

/-- Normalized comparisons compose, using the canonical localization identifications.
Source: Stacks Tag 070Y and the node's explicit composition argument
(blueprint: lem-sf-normalized-derived-comparison-composition).

Proof: (1) Transport the derived unit to complexes. For any resolution a:K -> I,
naturality gives t_F(K) followed by c_a = Q(Fa).
(2) The supplied normalization therefore says that beta commutes with these units
at K-injective complexes. Resolve an arbitrary complex and use naturality, cancelling
the derived image of the resolution, to obtain the same square at every complex.
(3) Paste beta01 and s01(beta12), inserting the canonical localization composition
maps. Their factorization equations and the strict equalities e01,e12,e02 show that
the pasted comparison has the same unit square as beta02.
(4) At K-injective H, the beta02 normalization makes Q(F0a) invertible for any
resolution a:r02H -> I. The formula in (1) then makes t_F0(r02H) invertible; cancel
it to obtain equality of the comparisons at QH.
(5) Resolve an arbitrary complex, use naturality and cancel the derived image of
its resolution. Localization extensionality extends equality to every L in D(A2).
Every resolution is chosen in its own category; preservation of K-injectives is unused. -/
theorem normalizedDerivedComparison_composition
    {A0 : Type uA0} {A1 : Type uA1} {A2 : Type uA2}
    {B0 : Type uB0} {B1 : Type uB1} {B2 : Type uB2}
    [Category.{vA0} A0] [Category.{vA1} A1] [Category.{vA2} A2]
    [Category.{vB0} B0] [Category.{vB1} B1] [Category.{vB2} B2]
    [Abelian A0] [Abelian A1] [Abelian A2] [Abelian B0] [Abelian B1] [Abelian B2]
    [HasDerivedCategory.{wA0} A0] [HasDerivedCategory.{wA1} A1]
    [HasDerivedCategory.{wA2} A2] [HasDerivedCategory.{wB0} B0]
    [HasDerivedCategory.{wB1} B1] [HasDerivedCategory.{wB2} B2]
    (F0 : A0 ⥤ B0) (F1 : A1 ⥤ B1) (F2 : A2 ⥤ B2)
    [F0.Additive] [F1.Additive] [F2.Additive]
    (enough0 : ∀ K : CochainComplex A0 ℤ,
      ∃ (I : CochainComplex A0 ℤ) (a : K ⟶ I), I.IsKInjective ∧ QuasiIso a)
    (enough1 : ∀ K : CochainComplex A1 ℤ,
      ∃ (I : CochainComplex A1 ℤ) (a : K ⟶ I), I.IsKInjective ∧ QuasiIso a)
    (enough2 : ∀ K : CochainComplex A2 ℤ,
      ∃ (I : CochainComplex A2 ℤ) (a : K ⟶ I), I.IsKInjective ∧ QuasiIso a)
    (r01 : A1 ⥤ A0) (r12 : A2 ⥤ A1) (r02 : A2 ⥤ A0)
    (s01 : B1 ⥤ B0) (s12 : B2 ⥤ B1) (s02 : B2 ⥤ B0)
    [r01.Additive] [r12.Additive] [r02.Additive]
    [s01.Additive] [s12.Additive] [s02.Additive]
    [PreservesFiniteLimits r01] [PreservesFiniteColimits r01]
    [PreservesFiniteLimits r12] [PreservesFiniteColimits r12]
    [PreservesFiniteLimits r02] [PreservesFiniteColimits r02]
    [PreservesFiniteLimits s01] [PreservesFiniteColimits s01]
    [PreservesFiniteLimits s12] [PreservesFiniteColimits s12]
    [PreservesFiniteLimits s02] [PreservesFiniteColimits s02]
    (er : r02 = r12 ⋙ r01) (es : s02 = s12 ⋙ s01)
    (e01 : r01 ⋙ F0 = F1 ⋙ s01) (e12 : r12 ⋙ F1 = F2 ⋙ s12)
    (e02 : r02 ⋙ F0 = F2 ⋙ s02)
    (β01 : r01.mapDerivedCategory ⋙ F0.rightDerivedFunctorOfQuasiIsoResolutions enough0 ≅
      F1.rightDerivedFunctorOfQuasiIsoResolutions enough1 ⋙ s01.mapDerivedCategory)
    (β12 : r12.mapDerivedCategory ⋙ F1.rightDerivedFunctorOfQuasiIsoResolutions enough1 ≅
      F2.rightDerivedFunctorOfQuasiIsoResolutions enough2 ⋙ s12.mapDerivedCategory)
    (β02 : r02.mapDerivedCategory ⋙ F0.rightDerivedFunctorOfQuasiIsoResolutions enough0 ≅
      F2.rightDerivedFunctorOfQuasiIsoResolutions enough2 ⋙ s02.mapDerivedCategory)
    (h01 : IsKInjectiveNormalizedDerivedComparison F0 F1 r01 s01 e01 enough0 enough1 β01)
    (h12 : IsKInjectiveNormalizedDerivedComparison F1 F2 r12 s12 e12 enough1 enough2 β12)
    (h02 : IsKInjectiveNormalizedDerivedComparison F0 F2 r02 s02 e02 enough0 enough2 β02)
    (L : DerivedCategory A2) :
    β02.hom.app L =
      (F0.rightDerivedFunctorOfQuasiIsoResolutions enough0).map
        ((normalizedDerivedComparisonCompositionLocalizationIso r02 r12 r01 er).hom.app L) ≫
      β01.hom.app (r12.mapDerivedCategory.obj L) ≫
      s01.mapDerivedCategory.map (β12.hom.app L) ≫
      (normalizedDerivedComparisonCompositionLocalizationIso s02 s12 s01 es).inv.app
        ((F2.rightDerivedFunctorOfQuasiIsoResolutions enough2).obj L) := by
  subst r02
  subst s02
  let RF0 := F0.rightDerivedFunctorOfQuasiIsoResolutions enough0
  let RF2 := F2.rightDerivedFunctorOfQuasiIsoResolutions enough2
  let ρ := mapDerivedCategoryCompIso r12 r01
  let σ := mapDerivedCategoryCompIso s12 s01
  let γ := isoWhiskerRight ρ RF0 ≪≫ Functor.associator _ _ _ ≪≫
    isoWhiskerLeft r12.mapDerivedCategory β01 ≪≫ (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight β12 s01.mapDerivedCategory ≪≫ Functor.associator _ _ _ ≪≫
    isoWhiskerLeft RF2 σ.symm
  suffices heq : β02.hom = γ.hom by
    simpa [γ, ρ, σ, normalizedDerivedComparisonCompositionLocalizationIso,
      mapDerivedCategoryNatIso_refl, RF0, RF2] using NatTrans.congr_app heq L
  have hcomplex (H : CochainComplex A2 ℤ) :
      (normalizedDerivedComparisonComplexIso F0 F2 (r12 ⋙ r01) (s12 ⋙ s01)
        enough0 enough2 γ H).hom =
      (normalizedDerivedComparisonComplexIso F0 F1 r01 s01 enough0 enough1 β01
        ((r12.mapHomologicalComplex (.up ℤ)).obj H)).hom ≫
        s01.mapDerivedCategory.map
          (normalizedDerivedComparisonComplexIso F1 F2 r12 s12 enough1 enough2 β12 H).hom ≫
        σ.inv.app (RF2.obj (DerivedCategory.Q.obj H)) := by
    simp only [normalizedDerivedComparisonComplexIso, γ, Iso.app_hom, Iso.trans_hom,
      mapIso_hom,
      Iso.symm_hom, Iso.app_inv, NatTrans.comp_app, isoWhiskerRight_hom,
      isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app]
    simp only [Functor.map_comp, Category.id_comp, Category.assoc]
    rw [← Functor.map_comp_assoc, compositionFactors_inv r12 r01 H,
      Functor.map_comp]
    have hn := β01.hom.naturality (r12.mapDerivedCategoryFactors.inv.app H)
    dsimp only [Functor.comp_map] at hn
    rw [Category.assoc, reassoc_of% hn]
  have htarget (H : CochainComplex A2 ℤ) :
      (normalizedDerivedComparisonTargetIso F0 F2 (r12 ⋙ r01) (s12 ⋙ s01) e02 H).hom =
      (normalizedDerivedComparisonTargetIso F0 F1 r01 s01 e01
        ((r12.mapHomologicalComplex (.up ℤ)).obj H)).hom ≫
        s01.mapDerivedCategory.map
          (normalizedDerivedComparisonTargetIso F1 F2 r12 s12 e12 H).hom ≫
        σ.inv.app (DerivedCategory.Q.obj ((F2.mapHomologicalComplex (.up ℤ)).obj H)) := by
    have he : (NatIso.mapHomologicalComplex (eqToIso e02) (.up ℤ)).hom.app H =
        (NatIso.mapHomologicalComplex (eqToIso e01) (.up ℤ)).hom.app
          ((r12.mapHomologicalComplex (.up ℤ)).obj H) ≫
        (s01.mapHomologicalComplex (.up ℤ)).map
          ((NatIso.mapHomologicalComplex (eqToIso e12) (.up ℤ)).hom.app H) := by
      ext i
      simp only [NatIso.mapHomologicalComplex, NatTrans.mapHomologicalComplex_app_f,
        HomologicalComplex.comp_f, mapHomologicalComplex_map_f, eqToIso.hom,
        eqToHom_app]
      erw [eqToHom_map, eqToHom_trans]
    simp only [normalizedDerivedComparisonTargetIso, Iso.trans_hom, mapIso_hom,
      Iso.app_hom, Iso.symm_hom, Iso.app_inv, Functor.map_comp, Category.assoc]
    rw [he, DerivedCategory.Q.map_comp]
    have hn := s01.mapDerivedCategoryFactors.inv.naturality
      ((NatIso.mapHomologicalComplex (eqToIso e12) (.up ℤ)).hom.app H)
    dsimp only [Functor.comp_map] at hn
    simp only [Category.assoc]
    erw [← reassoc_of% hn]
    erw [← reassoc_of% (compositionFactors_inv s12 s01
      ((F2.mapHomologicalComplex (.up ℤ)).obj H))]
    simp [σ]
  have hsquare (H : CochainComplex A2 ℤ) :
      (comparisonUnit F0 enough0).app
          (((r12 ⋙ r01).mapHomologicalComplex (.up ℤ)).obj H) ≫
        (normalizedDerivedComparisonComplexIso F0 F2 (r12 ⋙ r01) (s12 ⋙ s01)
          enough0 enough2 γ H).hom =
      (normalizedDerivedComparisonTargetIso F0 F2 (r12 ⋙ r01) (s12 ⋙ s01) e02 H).hom ≫
        (s12 ⋙ s01).mapDerivedCategory.map ((comparisonUnit F2 enough2).app H) := by
    rw [hcomplex, htarget]
    simp only [Category.assoc]
    rw [← Category.assoc ((comparisonUnit F0 enough0).app _)]
    erw [normalized_unit_square F0 F1 r01 s01 e01 enough0 enough1 β01 h01
      ((r12.mapHomologicalComplex (.up ℤ)).obj H)]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc,
      normalized_unit_square F1 F2 r12 s12 e12 enough1 enough2 β12 h12 H]
    simp only [Functor.map_comp, Category.assoc]
    have hn := σ.inv.naturality ((comparisonUnit F2 enough2).app H)
    dsimp only [Functor.comp_map] at hn
    congr 1
    congr 1
  have hkinj (H : CochainComplex A2 ℤ) [H.IsKInjective] :
      β02.hom.app (DerivedCategory.Q.obj H) = γ.hom.app (DerivedCategory.Q.obj H) := by
    obtain ⟨I, a, hI, ha⟩ := enough0
      (((r12 ⋙ r01).mapHomologicalComplex (.up ℤ)).obj H)
    have := hI
    have := ha
    obtain ⟨hFa, _⟩ := h02 H I a
    have := hFa
    have hc := comparisonUnit_resolution F0 enough0 a
    have hu : (comparisonUnit F0 enough0).app
        (((r12 ⋙ r01).mapHomologicalComplex (.up ℤ)).obj H) =
        DerivedCategory.Q.map ((F0.mapHomologicalComplex (.up ℤ)).map a) ≫
          (F0.rightDerivedFunctorOfQuasiIsoResolutionsObjIso enough0 a).inv := by
      rw [← hc]
      simp
    have : IsIso ((comparisonUnit F0 enough0).app
        (((r12 ⋙ r01).mapHomologicalComplex (.up ℤ)).obj H)) := by
      rw [hu]
      infer_instance
    have he : (normalizedDerivedComparisonComplexIso F0 F2 (r12 ⋙ r01) (s12 ⋙ s01)
          enough0 enough2 β02 H).hom =
        (normalizedDerivedComparisonComplexIso F0 F2 (r12 ⋙ r01) (s12 ⋙ s01)
          enough0 enough2 γ H).hom := by
      apply (cancel_epi ((comparisonUnit F0 enough0).app _)).mp
      exact (normalized_unit_square F0 F2 (r12 ⋙ r01) (s12 ⋙ s01) e02
        enough0 enough2 β02 h02 H).trans (hsquare H).symm
    simpa only [normalizedDerivedComparisonComplexIso, Iso.trans_hom, Iso.app_hom,
      mapIso_hom, Iso.symm_hom, Iso.app_inv, cancel_epi] using he
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A2 (.up ℤ))
  intro N
  obtain ⟨H, u, hH, hu⟩ := enough2 N
  have := hH
  have := hu
  apply (cancel_mono ((RF2 ⋙ (s12 ⋙ s01).mapDerivedCategory).map
    (DerivedCategory.Q.map u))).mp
  rw [← β02.hom.naturality, ← γ.hom.naturality, hkinj H]

end CategoryTheory.Functor
