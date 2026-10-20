/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SiteCechEdgeNormalization
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Homology.ModelCategory.Injective
import Sheaf.Algebra.Homology.BoundedBelowInjectiveResolutionMono
import Sheaf.CategoryTheory.Sites.InjectiveModuleCechAcyclic
import WeilConjectures.Algebra.Homology.FirstQuadrantAugmentation
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
import WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import Sheaf.CategoryTheory.DoubleComplexTotal
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.CategoryTheory.Sites.DirectImageInjectiveEvaluationAcyclic
import WeilConjectures.CategoryTheory.SiteCechComplex

/-! Edge uniqueness split.
(blueprint: lem-weil-pbc-ringed-site-cech-refinement-square-edges-unique) -/
set_option linter.style.longLine false
set_option linter.unusedVariables false

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

theorem ringedSite_cech_refinement_square_edges_unique
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    [HasFiniteLimits C] [HasFiniteLimits D]
    (J : Precoverage C) (K : Precoverage D)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [K.HasIsos] [K.IsStableUnderComposition] [K.IsStableUnderBaseChange] [K.HasPullbacks]
    (u : C ⥤ D) [PreservesFiniteLimits u]
    (hcover : ∀ (Y : C) (S : Presieve Y), S ∈ J Y → S.map u ∈ K (u.obj Y))
    [u.IsContinuous J.toGrothendieck K.toGrothendieck]
    [PreservesFiniteLimits (sheafPullback u (Type u) J.toGrothendieck K.toGrothendieck)]
    [PreservesFiniteColimits (sheafPullback u (Type u) J.toGrothendieck K.toGrothendieck)]
    (R : Sheaf J.toGrothendieck RingCat.{u}) (R' : Sheaf K.toGrothendieck RingCat.{u})
    (ρ : R ⟶ (u.sheafPushforwardContinuous RingCat.{u}
      J.toGrothendieck K.toGrothendieck).obj R')
    [EnoughInjectives (ringedSiteModules.{u} R)]
    [EnoughInjectives (ringedSiteModules.{u} R')]
    (M : ringedSiteModules.{u} R) (N : ringedSiteModules.{u} R')
    (h : M ⟶ (SheafOfModules.pushforward.{u} ρ).obj N)
    {X : C} (hX : IsTerminal X) (huX : IsTerminal (u.obj X))
    {I₀ I₁ : Type u} [Finite I₀] [Finite I₁]
    (U : I₀ → C) (v : ∀ i, U i ⟶ X)
    (V : I₁ → D) (w : ∀ j, V j ⟶ u.obj X)
    (hU : Presieve.ofArrows U v ∈ J X)
    (hV : Presieve.ofArrows V w ∈ K (u.obj X))
    (S : SiteCechComplex U v) (T : SiteCechComplex V w)
    (r : I₁ → I₀) (a : ∀ j, V j ⟶ u.obj (U (r j)))
    (aTuple : ∀ (p : ℕ) (j : Fin (p + 1) → I₁),
      T.W p j ⟶ u.obj (S.W p (r ∘ j)))
    (haTuple : ∀ (p : ℕ) (j : Fin (p + 1) → I₁) (k : Fin (p + 1)),
      aTuple p j ≫ u.map (S.pr p (r ∘ j) k) = T.pr p j k ≫ a (j k))
    (γ : S.complex M.val.presheaf ⟶ T.complex N.val.presheaf) :
      ∀ q : ℕ,
        ∀ (eM eM' :  (S.cohomologyFunctor q).obj M.val.presheaf ⟶ (((SheafOfModules.forget R ⋙
          PresheafOfModules.toPresheaf R.obj) ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op
          X)).rightDerived q).obj M),
          S.IsNormalizedEdge (SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj) q eM →
          S.IsNormalizedEdge (SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj) q eM' →
          eM = eM' ∧
          ∀ (eN eN' :
             (T.cohomologyFunctor q).obj N.val.presheaf ⟶ (((SheafOfModules.forget R' ⋙
            PresheafOfModules.toPresheaf R'.obj) ⋙ (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op (u.obj
            X))).rightDerived q).obj N),
            T.IsNormalizedEdge (SheafOfModules.forget R' ⋙
              PresheafOfModules.toPresheaf R'.obj) q eN →
            T.IsNormalizedEdge (SheafOfModules.forget R' ⋙
              PresheafOfModules.toPresheaf R'.obj) q eN' →
            eN = eN'  := by
  intro q eM eM' heM heM'
  let I := injectiveResolution M
  obtain ⟨d, hd, he⟩ := heM I
  obtain ⟨d', hd', he'⟩ := heM' I
  have ha : d.alpha = d'.alpha := by
    apply HomologicalComplex.hom_ext
    intro n
    rw [d.alpha_f, d'.alpha_f]
  have hb : d.beta = d'.beta := by
    apply HomologicalComplex.hom_ext
    intro n
    rw [d.beta_f, d'.beta_f]
  rw [← ha, ← hb] at he'
  have heqM : eM = eM' := (cancel_mono ((I.isoRightDerivedObj
    (SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op X)) q).hom ≫
      HomologicalComplex.homologyMap d.alpha q)).mp (he.trans he'.symm)
  refine ⟨heqM, ?_⟩
  intro eN eN' heN heN'
  let I' := injectiveResolution N
  obtain ⟨dN, hdN, heN0⟩ := heN I'
  obtain ⟨dN', hdN', heN'0⟩ := heN' I'
  have haN : dN.alpha = dN'.alpha := by
    apply HomologicalComplex.hom_ext
    intro n
    rw [dN.alpha_f, dN'.alpha_f]
  have hbN : dN.beta = dN'.beta := by
    apply HomologicalComplex.hom_ext
    intro n
    rw [dN.beta_f, dN'.beta_f]
  rw [← haN, ← hbN] at heN'0
  exact (cancel_mono ((I'.isoRightDerivedObj
    (SheafOfModules.forget R' ⋙ PresheafOfModules.toPresheaf R'.obj ⋙
      (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op (u.obj X))) q).hom ≫
      HomologicalComplex.homologyMap dN.alpha q)).mp (heN0.trans heN'0.symm)
end CategoryTheory
