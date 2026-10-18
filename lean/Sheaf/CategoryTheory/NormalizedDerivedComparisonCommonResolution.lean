/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q135
-/
module

public import Sheaf.CategoryTheory.KInjectiveDerivedMapComputation
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Normalized derived comparisons on successive resolutions

Source: Stacks Project, Derived Categories, Tag 070Y (`lemma-K-injective-defined`),
and the explicit naturality consequence in the DAG
(blueprint: lem-sf-normalized-derived-comparison-common-resolution).

The helpers insert the canonical exact-functor localization identifications. They
use the recorded total right derived functors and their canonical resolution maps.
-/

@[expose] public section

set_option autoImplicit false

universe wA wA' wB wB' vA vA' vB vB' uA uA' uB uB'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {A : Type uA} {A' : Type uA'} {B : Type uB} {B' : Type uB'}
  [Category.{vA} A] [Category.{vA'} A'] [Category.{vB} B] [Category.{vB'} B']
  [Abelian A] [Abelian A'] [Abelian B] [Abelian B']
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wA'} A']
  [HasDerivedCategory.{wB} B] [HasDerivedCategory.{wB'} B']
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

/-- The supplied comparison on a complex, with the canonical localization identification
for r inserted. Source: Stacks Tag 070Y, node's normalization convention
(blueprint: lem-sf-normalized-derived-comparison-common-resolution). -/
noncomputable def normalizedDerivedComparisonComplexIso (N : CochainComplex A' ℤ) :
    (F.rightDerivedFunctorOfQuasiIsoResolutions enoughA).obj
        (DerivedCategory.Q.obj ((r.mapHomologicalComplex (.up ℤ)).obj N)) ≅
      s.mapDerivedCategory.obj
        ((G.rightDerivedFunctorOfQuasiIsoResolutions enoughA').obj (DerivedCategory.Q.obj N)) :=
  (F.rightDerivedFunctorOfQuasiIsoResolutions enoughA).mapIso
      ((r.mapDerivedCategoryFactors).app N).symm ≪≫ β.app (DerivedCategory.Q.obj N)

/-- The canonical identification Q(F(rJ)) = Q(s(GJ)) with s(Q(GJ)).
Its first factor is induced by the given equality on objects and morphisms.
Source: Stacks Tag 070Y, node's exact-functor identifications
(blueprint: lem-sf-normalized-derived-comparison-common-resolution). -/
noncomputable def normalizedDerivedComparisonTargetIso (J : CochainComplex A' ℤ) :
    DerivedCategory.Q.obj
        ((F.mapHomologicalComplex (.up ℤ)).obj ((r.mapHomologicalComplex (.up ℤ)).obj J)) ≅
      s.mapDerivedCategory.obj (DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj J)) :=
  DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex (eqToIso e) (.up ℤ)).app J) ≪≫
    ((s.mapDerivedCategoryFactors).app ((G.mapHomologicalComplex (.up ℤ)).obj J)).symm

/-- The comparison expressed using successive resolutions u and v. The source map is
c_w inverse for w = r(u) followed by v; the target map is s(c_u), transported by e.
Source: Stacks Tag 070Y, node's displayed formula
(blueprint: lem-sf-normalized-derived-comparison-common-resolution). -/
noncomputable def normalizedDerivedComparisonResolutionMap
    {N J : CochainComplex A' ℤ} {T : CochainComplex A ℤ}
    [J.IsKInjective] [T.IsKInjective]
    (u : N ⟶ J) (v : (r.mapHomologicalComplex (.up ℤ)).obj J ⟶ T)
    [QuasiIso u] [QuasiIso v] :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj T) ⟶
      DerivedCategory.Q.obj
        ((F.mapHomologicalComplex (.up ℤ)).obj ((r.mapHomologicalComplex (.up ℤ)).obj J)) :=
  (F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso enoughA
      ((r.mapHomologicalComplex (.up ℤ)).map u ≫ v)).inv ≫
    (normalizedDerivedComparisonComplexIso F G r s enoughA enoughA' β N).hom ≫
    s.mapDerivedCategory.map (G.rightDerivedFunctorOfQuasiIsoResolutionsObjIso enoughA' u).hom ≫
    (normalizedDerivedComparisonTargetIso F G r s e J).inv

variable
  (hFv : ∀ (J : CochainComplex A' ℤ) [J.IsKInjective]
    (T : CochainComplex A ℤ) [T.IsKInjective]
    (v : (r.mapHomologicalComplex (.up ℤ)).obj J ⟶ T) [QuasiIso v],
    IsIso (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map v)))
  (hnormalized : ∀ (J : CochainComplex A' ℤ) [J.IsKInjective]
    (T : CochainComplex A ℤ) [T.IsKInjective]
    (v : (r.mapHomologicalComplex (.up ℤ)).obj J ⟶ T) [QuasiIso v],
    (F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso enoughA v).inv ≫
        (normalizedDerivedComparisonComplexIso F G r s enoughA enoughA' β J).hom ≫
        s.mapDerivedCategory.map
          (G.rightDerivedFunctorOfQuasiIsoResolutionsObjIso enoughA' (𝟙 J)).hom ≫
        (normalizedDerivedComparisonTargetIso F G r s e J).inv =
      @CategoryTheory.inv _ _ _ _ _ (hFv J T v))

include hnormalized

/-- A normalized comparison is computed on any successive K-injective resolutions.
Source: Stacks Tag 070Y and the node's explicit naturality consequence
(blueprint: lem-sf-normalized-derived-comparison-common-resolution).

Proof: (1) Exactness of r preserves the quasi-isomorphism u; composing with v gives
w, a resolution with K-injective target T (lem-weil-pbc-exact-functor-derived-factorization).
The canonical resolution formula gives c_w = RF(Q(r(u))) followed by c_v and
c_u = RG(Qu) followed by the inverse unit at J
(lem-sf-kinjective-derived-map-computation).
(2) Naturality of beta at Qu commutes RG(Qu) past beta; cancellation with the inverse
of RF(Q(r(u))) reduces the asserted arrow to c_v inverse, beta at J, and s(eta_J inverse).
(3) Apply exactly the supplied normalization to J and v. The target identification
uses Fr = sG. Invertibility of Q(Fv) is supplied by hFv; no K-injectivity of rJ is used.
The subsequent theorem records step (4), compatibility with changes of resolution. -/
theorem normalizedDerivedComparison_commonResolution
    {N J : CochainComplex A' ℤ} {T : CochainComplex A ℤ}
    [J.IsKInjective] [T.IsKInjective]
    (u : N ⟶ J) (v : (r.mapHomologicalComplex (.up ℤ)).obj J ⟶ T)
    [QuasiIso u] [QuasiIso v] :
    normalizedDerivedComparisonResolutionMap F G r s e enoughA enoughA' β u v =
      @CategoryTheory.inv _ _ _ _ _ (hFv J T v) := by
  let RF := F.rightDerivedFunctorOfQuasiIsoResolutions enoughA
  let RG := G.rightDerivedFunctorOfQuasiIsoResolutions enoughA'
  let ru := (r.mapHomologicalComplex (.up ℤ)).map u
  have hF : RF.map (DerivedCategory.Q.map ru) ≫
      (F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso enoughA v).hom =
      (F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso enoughA (ru ≫ v)).hom := by
    simp [rightDerivedFunctorOfQuasiIsoResolutionsObjIso, RF, Functor.map_comp,
      Category.assoc]
  have hG : RG.map (DerivedCategory.Q.map u) ≫
      (G.rightDerivedFunctorOfQuasiIsoResolutionsObjIso enoughA' (𝟙 J)).hom =
      (G.rightDerivedFunctorOfQuasiIsoResolutionsObjIso enoughA' u).hom := by
    simp [rightDerivedFunctorOfQuasiIsoResolutionsObjIso, RG]
  have hnat : RF.map (DerivedCategory.Q.map ru) ≫
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
  have hcancel :
      (F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso enoughA (ru ≫ v)).inv ≫
        RF.map (DerivedCategory.Q.map ru) =
      (F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso enoughA v).inv := by
    apply (cancel_mono
      (F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso enoughA v).hom).mp
    simp only [Category.assoc, hF, Iso.inv_hom_id]
  unfold normalizedDerivedComparisonResolutionMap
  rw [← hG, s.mapDerivedCategory.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc
    (normalizedDerivedComparisonComplexIso F G r s enoughA enoughA' β N).hom,
    ← hnat]
  simp only [← Category.assoc]
  rw [hcancel]
  simpa only [Category.assoc] using hnormalized J T v

/-- The inverse arrows in the formula respect the canonical changes of both resolutions.
Source: Stacks Tag 070Y, explicit change-of-resolution consequence
(blueprint: lem-sf-normalized-derived-comparison-common-resolution).

Proof: (4) For i = 1,2 put w_i = v_i r(u_i). The source transition is
c_(w_1) inverse followed by c_(w_2), and the target transition is s applied to
c_(u_1) inverse followed by c_(u_2), with the canonical endpoint identifications.
Substitute these into d_F inverse, L_1, d_G and cancel the middle c maps.
This gives L_2. Steps (1)--(3) identify each L_i with Q(Fv_i) inverse.
The transition laws of lem-sf-kinjective-derived-map-computation give the cocycle
identity, hence consistency for three or more choices. -/
theorem normalizedDerivedComparison_commonResolution_transition
    {N J₁ J₂ : CochainComplex A' ℤ} {T₁ T₂ : CochainComplex A ℤ}
    [J₁.IsKInjective] [J₂.IsKInjective] [T₁.IsKInjective] [T₂.IsKInjective]
    (u₁ : N ⟶ J₁) (u₂ : N ⟶ J₂)
    (v₁ : (r.mapHomologicalComplex (.up ℤ)).obj J₁ ⟶ T₁)
    (v₂ : (r.mapHomologicalComplex (.up ℤ)).obj J₂ ⟶ T₂)
    [QuasiIso u₁] [QuasiIso u₂] [QuasiIso v₁] [QuasiIso v₂] :
    @CategoryTheory.inv _ _ _ _ _ (hFv J₂ T₂ v₂) =
      (F.kInjectiveDerivedResolutionTransition enoughA
        ((r.mapHomologicalComplex (.up ℤ)).map u₁ ≫ v₁)
        ((r.mapHomologicalComplex (.up ℤ)).map u₂ ≫ v₂)).inv ≫
      @CategoryTheory.inv _ _ _ _ _ (hFv J₁ T₁ v₁) ≫
      (normalizedDerivedComparisonTargetIso F G r s e J₁).hom ≫
      s.mapDerivedCategory.map
        (G.kInjectiveDerivedResolutionTransition enoughA' u₁ u₂).hom ≫
      (normalizedDerivedComparisonTargetIso F G r s e J₂).inv := by
  rw [← normalizedDerivedComparison_commonResolution F G r s e enoughA enoughA' β
    hFv hnormalized u₂ v₂,
    ← normalizedDerivedComparison_commonResolution F G r s e enoughA enoughA' β
      hFv hnormalized u₁ v₁]
  simp [normalizedDerivedComparisonResolutionMap, kInjectiveDerivedResolutionTransition,
    Functor.map_comp, Category.assoc]

end CategoryTheory.Functor
